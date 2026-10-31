/- Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later -/

/-
# The Layer-2 named trust seam: `byteSlice`

This module holds **Layer 2** of the two proof-layer split (see the design and
`README`): a single `@[extern]` primitive `byteSlice` whose *Lean* body elaborates
and reduces — so `#print axioms` reports the proof-only body clean
(`[propext, Quot.sound]`, no added axiom) — but whose *running* C is **trusted,
not proven**.

## What it is

`byteSlice a i : ByteArray` is a `memcpy`-style suffix copy: the bytes of `a` at
-or-after the index `i`, materialized as a fresh contiguous `ByteArray`. Its Lean
body is `a.data.extract i.toNat a.data.size` — an `Array.extract` over the
backing `data` (the `[propext, Quot.sound]`-clean spelling of the suffix copy;
`ByteArray.extract` is `@[extern]` with no elaborating body and would not reduce),
chosen so the body reduces under `simp`/`rfl` where a law needs it. The
`@[extern "codec_byteSlice"]` attribute swaps only the *emitted* C: the running
binary calls the hand-written C symbol `codec_byteSlice` (in `ByteSlice.c`), which
does a single `memcpy`.

The `USize` argument is a scalar in the emitted C: the IR
(`.lake/build/ir/Codec/ByteSlice.c`) declares `lean_object* codec_byteSlice(lean_object*,
size_t)` and unboxes `USize` via `lean_unbox_usize` — the same `USize → size_t`
lowering Lean uses for `ByteArray.usize`/`uget`. (This is the scalar-index fact the
Layer-1 carrier cursor does **not** enjoy — that cursor is `Nat` and lowers to a
boxed bignum, per the task-3.1 IR inspection.)

## The trust contract (verbatim)

Layer 2 is **excluded** from the `#print axioms` gate. The Lean body is the
_specification_ (the denotation every law is proved against); the C symbol is a
_named, isolated trust seam_ whose contract is "`codec_byteSlice a i` returns the
bytes of `a` at-or-after `i`, copied with `memcpy`". That the C meets this
contract is **trusted, not proven** in Lean — the F\*-vs-KaRaMeL posture: declare
the primitive in Lean (pinning its meaning), hand-write the C under the same name,
and never present "no axiom" as "no trust".

`byteSlice` is a **standalone seam**: in this change it has *no library-internal
caller* — the proven `decodeFullArray` (Layer 1) deliberately builds its suffix via
the `List.toArray.drop` transport so its refinement stays `Classical.choice`-free
(an axiom-clean body, not a trusted `@[extern]`), and no other packed path consumes
it. It exists to be *called* by a packed path when a consumer wants the floor
suffix copy, and the bench lane is the packed-path consumer that exercises it. It
is **not** wired into `decodeFullArray`, and the "wired only onto a packed path"
constraint is a *how-to-use* rule (never a `List`-re-materializing consumer), not a
claim that it is currently in the library critical path.
-/

namespace Codec

/--
The Layer-2 named trust seam: a `memcpy`-style suffix copy. `byteSlice a i` is a
fresh `ByteArray` of the bytes of `a` at-or-after index `i` (empty when `i` is at
-or past the end).

The Lean body below is the *specification* — `a.data.extract i.toNat a.data.size`
re-packed — and reduces in proofs (`[propext, Quot.sound]`-only, no added axiom).
The `@[extern "codec_byteSlice"]` attribute makes the *running* C call the matching
`codec_byteSlice` symbol in `ByteSlice.c`; that C is trusted, not proven, and is
therefore excluded from the `#print axioms` gate (Layer 2, never conflated with
the proven Layer 1 carrier in `Codec.Packed`).
-/
@[extern "codec_byteSlice"]
def byteSlice (a : ByteArray) (i : USize) : ByteArray :=
  ByteArray.mk (a.data.extract i.toNat a.data.size)

/-- The single `memcpy` commit: turn a `USize` consumed-count cursor into the
`ByteArray` remainder `[c.toNat, a.size)` as a fresh contiguous `ByteArray`,
materialized by one `byteSlice` (the Layer-2 trusted `memcpy`).

This is the **first library consumer of the `byteSlice` trust seam**. It is
`USize`-indexed to match `byteSlice`'s own index exactly, so its refinement law
(`commitRemainder_spec` in `Codec.Packed`) is definitional — **no** `Nat ↔ USize`
roundtrip and **no** `System.Platform.numBits` premise enter (the `Nat → USize`
conversion happens once, at the call site, in the caller). Like `byteSlice`, it
remains **excluded** from the `#print axioms` gate: the Lean body is
axiom-clean, while the C `memcpy` it runs is a runtime contract invisible to
Lean, documented in this module's header — never an axiom, never "no trust". -/
def commitRemainder (a : Array UInt8) (c : USize) : ByteArray :=
  byteSlice (ByteArray.mk a) c

/--
The Layer-2 named trust seam: a buffer-to-buffer `memcpy` blit. `blitBytes dst
dstOff src srcOff len` copies `len` bytes from `src[srcOff .. srcOff+len)` into
`dst[dstOff .. dstOff+len)`, returning a fresh `ByteArray` of the **full length of
`dst`** with the rest of `dst` unchanged.

**Boundary (out-of-range) semantics — clause by clause.** All four indices/`len`
are clamped exactly as `Array.extract` clamps its `start`/`stop` bounds to
`[0, size]` (an `off ≥ size` yields an empty span; a `stop` past the end is
truncated; `stop ≤ start` is empty). Concretely the body computes, in `Nat`:

  * `n := dst.data.size`, `slen := src.data.size`;
  * `dc := min dstOff.toNat n` (destination cursor, clamped into `[0, n]`);
  * `sc := min srcOff.toNat slen` (source cursor, clamped into `[0, slen]`);
  * `lc := min len.toNat (min (n - dc) (slen - sc))` (the copied run, clamped to
    fit *both* the destination window `[dc, n)` and the source `[sc, slen)`).

and produces the length-`n` byte string
`dst[0,dc) ++ src[sc, sc+lc) ++ dst[dc+lc, n)` — the whole of `dst` with the
`[dc, dc+lc)` window overwritten by `src[sc, sc+lc)`.  `byteSlice`/`findByte` are
the suffix/`memchr` peers with the *same* `[0, size]` start-clamp (documented on
each below).  `blitBytes` is the one seam with a **named `lc`** shared between
its middle and trailing parts, because a window replacement (unlike `byteSlice`
`'s bare suffix) must agree on the *copied length* across both the middle and the
suffix; this is what makes the C's single `memcpy` agree with the body **value for
value** — by `min`'s associativity and commutativity over the same three clamped
quantities, not by the C being a term-for-term transcription. See the contract
comment in `Codec/ByteSlice.c` for the clamp order the C actually uses and why the
two orders coincide.

The Lean body below is the *specification* — an `Array.extract`+`append`
composition over the backing `data` (reducible, so its `blitBytes_spec` law closes
by `rfl`, `[propext, Quot.sound]`-only, no added axiom). The `@[extern
"codec_blitBytes"]` attribute makes the *running* C call the matching `codec_blitBytes`
symbol in `ByteSlice.c`; that C is trusted, not proven, and is therefore excluded
from the `#print axioms` gate (Layer 2).

The indices are `USize` so the body is `rfl`-clean (no `Nat ↔ USize` roundtrip, no
`System.Platform.numBits` premise). -/
@[extern "codec_blitBytes"]
def blitBytes (dst : ByteArray) (dstOff : USize) (src : ByteArray) (srcOff : USize)
    (len : USize) : ByteArray :=
  let n := dst.data.size
  let slen := src.data.size
  let dc := min dstOff.toNat n
  let sc := min srcOff.toNat slen
  let lc := min len.toNat (min (n - dc) (slen - sc))
  ByteArray.mk
    (dst.data.extract 0 dc
      ++ src.data.extract sc (sc + lc)
      ++ dst.data.extract (dc + lc) n)

/--
The Layer-2 named trust seam: a span `memchr` scan. `findByte a off b` returns
the first index `i ≥ off.toNat` (as a `USize`) at which `a` holds the byte `b`,
or `none` when there is no such index.

The Lean body below is the *specification* — `Array.findIdx?` over the
`Array.extract` of the suffix from `off` (reducible, so `findByte_spec` closes by
`rfl`). The `@[extern "codec_findByte"]` attribute makes the running C call the
matching `codec_findByte` symbol (a single `memchr`); that C is trusted, not
proven, and is excluded from the `#print axioms` gate.

**Arithmetic side condition (the C relies on it).** The body returns
`some (off + i.toUSize)` where `+` is `USize` addition, i.e. `Nat` addition
**modulo `2^64`**, while `codec_findByte` returns the absolute index as a raw
`size_t`. These agree only when the sum does not wrap:

    off.toNat + i < USize.size

which always holds here — `i < a.data.size` and `off ≤ a.data.size`, so
`off.toNat + i < 2 * a.data.size`, and no `ByteArray` in a 64-bit address space
holds `2^63` bytes — but that fact is **not** stated by any theorem, so "the C
matches the Lean body" holds on every input Lean can actually build rather than
on every input the type admits. Recorded rather than silently strengthened:
discharging it in full needs a `System.Platform.numBits` premise, which
`AGENTS.md` forbids because it would leave the `[propext, Quot.sound]`-only gate.
A caller that could wrap is a caller whose `ByteArray` does not fit in the
machine. -/
@[extern "codec_findByte"]
def findByte (a : ByteArray) (off : USize) (b : UInt8) : Option USize :=
  match Array.findIdx? (fun x => x == b) (a.data.extract off.toNat a.data.size) with
  | some i => some (off + i.toUSize)
  | none => none

/-- The `byteSlice` refinement is a definitional identity: `byteSlice a i` is the
bytes of `a` at-or-after `i`, i.e. `a.data.extract i.toNat a.data.size` re-packed
into a fresh `ByteArray`.

This law is what makes the trust seam's contract *nameable*: the C's contract is
"the C matches the Lean body", and without a theorem fixing that body the
contract points at a definition rather than at a checkable statement. It is the
sibling of `blitBytes_spec`/`findByte_spec` below, so every Layer-2 seam now has
its own `*_spec`. `rfl`-clean, `[propext, Quot.sound]`-only (no `Classical.choice`,
zero `sorry`), and no `byteSlice`-related axiom — the running C is invisible to
Lean, as the module header records. **Axiom footprint: none** (`#print axioms
Codec.byteSlice_spec` reports no axioms at all), the same as `blitBytes_spec` and
unlike `findByte_spec`'s `[propext]`; see that law for why the set is not uniform. -/
theorem byteSlice_spec (a : ByteArray) (i : USize) :
    byteSlice a i = ByteArray.mk (a.data.extract i.toNat a.data.size) := by
  rfl

/-- The `blitBytes` refinement is a definitional identity: the result is `dst`
with its `[dc, dc+lc)` slice (where `dc`/`lc` are the destination-destined cursor
and the copied run, both clamped as `Array.extract` clamps its bounds) replaced by
`src[sc, sc+lc)`. The `USize` indices carry no `Nat ↔ USize` roundtrip the law must
justify, so `#print axioms Codec.blitBytes_spec` reports `[propext, Quot.sound]`
with no `blitBytes`-related axiom. `rfl`-clean. -/
theorem blitBytes_spec (dst : ByteArray) (dstOff : USize) (src : ByteArray) (srcOff : USize)
    (len : USize) :
    blitBytes dst dstOff src srcOff len =
      ByteArray.mk
        (dst.data.extract 0 (min dstOff.toNat dst.data.size)
          ++ src.data.extract (min srcOff.toNat src.data.size)
              (min srcOff.toNat src.data.size + min len.toNat (min (dst.data.size - min dstOff.toNat dst.data.size) (src.data.size - min srcOff.toNat src.data.size)))
          ++ dst.data.extract
              (min dstOff.toNat dst.data.size + min len.toNat (min (dst.data.size - min dstOff.toNat dst.data.size) (src.data.size - min srcOff.toNat src.data.size)))
              dst.data.size) := by
  rfl

/-- The `findByte` refinement is a definitional identity: `findByte a off b` is
exactly the `Array.findIdx?` scan of the suffix from `off`, re-offset by `off`.
`rfl`-clean.

**Axiom footprint: `[propext]`** — deliberately *not* uniform with its
`byteSlice_spec`/`blitBytes_spec` siblings, which report none. The scan goes
through `Array.findIdx?`, whose `DecidableEq UInt8` instance is a propositional
(not definitional) decision, so `propext` is pulled in. `[propext]` is inside the
`[propext, Quot.sound]`-only gate; the asymmetry is recorded here so it is not
mistaken for drift. No `Classical.choice`, zero `sorry`. -/
theorem findByte_spec (a : ByteArray) (off : USize) (b : UInt8) :
    findByte a off b =
      match Array.findIdx? (fun x => x == b) (a.data.extract off.toNat a.data.size) with
      | some i => some (off + i.toUSize)
      | none => none := by
  rfl

end Codec
