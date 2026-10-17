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
`dst[dstOff .. dstOff+len)`, returning a fresh `ByteArray` with the rest of `dst`
unchanged.

The Lean body below is the *specification* — the `Array.extract`+`append`
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
  ByteArray.mk
    (dst.data.extract 0 dstOff.toNat
      ++ src.data.extract srcOff.toNat (srcOff.toNat + len.toNat)
      ++ dst.data.extract (dstOff.toNat + len.toNat) dst.data.size)

/--
The Layer-2 named trust seam: a span `memchr` scan. `findByte a off b` returns
the first index `i ≥ off.toNat` (as a `USize`) at which `a` holds the byte `b`,
or `none` when there is no such index.

The Lean body below is the *specification* — `Array.findIdx?` over the
`Array.extract` of the suffix from `off` (reducible, so `findByte_spec` closes by
`rfl`). The `@[extern "codec_findByte"]` attribute makes the running C call the
matching `codec_findByte` symbol (a single `memchr`); that C is trusted, not
proven, and is excluded from the `#print axioms` gate. -/
@[extern "codec_findByte"]
def findByte (a : ByteArray) (off : USize) (b : UInt8) : Option USize :=
  match Array.findIdx? (fun x => x == b) (a.data.extract off.toNat a.data.size) with
  | some i => some (off + i.toUSize)
  | none => none

/-- The `blitBytes` refinement is a definitional identity: the result is `dst`
with its `[dstOff, dstOff+len)` slice replaced by `src[srcOff, srcOff+len)`. The
`USize` indices carry no `Nat ↔ USize` roundtrip the law must justify, so
`#print axioms Codec.blitBytes_spec` reports `[propext, Quot.sound]` with no
`blitBytes`-related axiom. `rfl`-clean. -/
theorem blitBytes_spec (dst : ByteArray) (dstOff : USize) (src : ByteArray) (srcOff : USize)
    (len : USize) :
    blitBytes dst dstOff src srcOff len =
      ByteArray.mk
        (dst.data.extract 0 dstOff.toNat
          ++ src.data.extract srcOff.toNat (srcOff.toNat + len.toNat)
          ++ dst.data.extract (dstOff.toNat + len.toNat) dst.data.size) := by
  rfl

/-- The `findByte` refinement is a definitional identity: `findByte a off b` is
exactly the `Array.findIdx?` scan of the suffix from `off`, re-offset by `off`.
`rfl`-clean, `[propext, Quot.sound]`-only. -/
theorem findByte_spec (a : ByteArray) (off : USize) (b : UInt8) :
    findByte a off b =
      match Array.findIdx? (fun x => x == b) (a.data.extract off.toNat a.data.size) with
      | some i => some (off + i.toUSize)
      | none => none := by
  rfl

end Codec
