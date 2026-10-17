/- Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later -/

import Codec.VarBinary
import Codec.Packed

/-
# The Layer-2 named trust seams: `varintEncodeInto` / `varintDecodeFrom`

This module holds **Layer 2** of the two-proof-layer split (see the `ByteSlice`
module header and the `README`): two `@[extern]` LEB128 span primitives whose
*Lean* bodies elaborate and reduce (so `#print axioms` reports the proof-only
body clean — `[propext, Quot.sound]`, no added axiom) but whose *running* C is
**trusted, not proven**.

## What they are

`varintEncodeInto dst off n : ByteArray` places the canonical LEB128 encoding of
`n` (`Codec.varintBytes`) into `dst` at byte offset `off`, returning the full
length of `dst` with that span overwritten. `varintDecodeFrom a off : Option (Nat
× USize)` decodes one canonical varint from `a` starting at `off`, returning the
value together with the byte count consumed.

Both are `USize`-indexed so their Lean-body refinement laws are `rfl`-clean (no
`Nat ↔ USize` roundtrip and no `System.Platform.numBits` premise; the `Nat → USize`
conversion happens at the call site, once).

## The trust contract (verbatim)

Layer 2 is **excluded** from the `#print axioms` gate. The Lean body is the
_specification_ (the denotation every law is proved against); the C symbol is a
_named, isolated trust seam_:

  * `codec_varintEncodeInto dst off n` writes the canonical LEB128 bytes of `n`
    into `dst[off .. off+k)` (where `k` is `varintBytes n`'s length) and returns
    `dst` with that span overwritten and every other byte unchanged.
  * `codec_varintDecodeFrom a off n` returns `some (n, k)` exactly when the
    `k`-byte suffix from `off` is the canonical LEB128 encoding of `n` (i.e.
    `varintDecodeStep 0 1` on the suffix returns `(n, ⟨0, ·⟩)`), and `none`
    otherwise.

That the C meets these contracts is **trusted, not proven** in Lean — the
F\*-vs-KaRaMeL posture: declare the primitive in Lean (pinning its meaning),
hand-write the C under the same name, and never present "no axiom" as "no trust".
The bench lane value-checks each seam byte-for-byte against its Lean body, so a
semantically wrong C symbol fails at run time, not only at the contract.
-/

namespace Codec

/--
The Layer-2 named trust seam: a LEB128 encode into a buffer span. `varintEncodeInto
dst off n` is `dst` with its `[off, off+k)` window replaced by the canonical
LEB128 encoding of `n` (of length `k = (varintBytes n).1`).

The Lean body below is the *specification* — the `varintBytes n` bytes read back
as an `Array` and spliced into `dst.data` by the same `extract`+`append` composition
`blitBytes` uses (reducible, so its spec law closes by `rfl`). The `@[extern
"codec_varintEncodeInto"]` attribute makes the running C call the matching symbol
in `VarintFast.c` (a scalar `size_t`+`uint8_t` loop, no bignum cursor); that C is
trusted, not proven, and excluded from the `#print axioms` gate. -/
@[extern "codec_varintEncodeInto"]
def varintEncodeInto (dst : ByteArray) (off : USize) (n : Nat) : ByteArray :=
  let ⟨k, bs⟩ := varintBytes n
  let src : ByteArray := ByteArray.mk ((List.ofFn bs).toArray)
  ByteArray.mk
    (dst.data.extract 0 off.toNat
      ++ src.data.extract 0 k
      ++ dst.data.extract (off.toNat + k) dst.data.size)

/--
The Layer-2 named trust seam: a LEB128 decode from a buffer span. `varintDecodeFrom
a off` returns `some (n, k)` when the bytes at `a[off .. off+k)` are the canonical
LEB128 encoding of `n` (consuming exactly `k` bytes), and `none` when the span
does not hold a canonical varint (or is empty).

The Lean body below is the *specification* — the suffix from `off` read back as a
`Bytes` and decoded by `varintDecodeStep` (the `VarBinary` decoder), the consumed
count reconstructed as `suffix.size - m`. The `@[extern "codec_varintDecodeFrom"]`
attribute makes the running C call the matching symbol (a scalar loop); that C is
trusted, not proven, and excluded from the `#print axioms` gate. -/
@[extern "codec_varintDecodeFrom"]
def varintDecodeFrom (a : ByteArray) (off : USize) : Option (Nat × USize) :=
  let suffix : Array UInt8 := a.data.extract off.toNat a.data.size
  match varintDecodeStep 0 1 (arrayToBytes suffix) with
  | some (n, ⟨m, _⟩) => some (n, (suffix.size - m).toUSize)
  | none => none

/-- The `varintEncodeInto` refinement is a definitional identity: the result is
`dst` with its `[off, off+k)` slice replaced by the `varintBytes n` bytes. `rfl`-clean. -/
theorem varintEncodeInto_spec (dst : ByteArray) (off : USize) (n : Nat) :
    varintEncodeInto dst off n =
      (let ⟨k, bs⟩ := varintBytes n
       let src : ByteArray := ByteArray.mk ((List.ofFn bs).toArray)
       ByteArray.mk
         (dst.data.extract 0 off.toNat
           ++ src.data.extract 0 k
           ++ dst.data.extract (off.toNat + k) dst.data.size)) := by
  rfl

/-- The `varintDecodeFrom` refinement is a definitional identity: it is exactly the
`varintDecodeStep` decode of the suffix from `off`, with the consumed count read
back as `suffix.size - m`. `rfl`-clean. -/
theorem varintDecodeFrom_spec (a : ByteArray) (off : USize) :
    varintDecodeFrom a off =
      (let suffix : Array UInt8 := a.data.extract off.toNat a.data.size
       match varintDecodeStep 0 1 (arrayToBytes suffix) with
       | some (n, ⟨m, _⟩) => some (n, (suffix.size - m).toUSize)
       | none => none) := by
  rfl

end Codec
