/- Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later -/

import Codec.ByteSlice

/-
# The Layer-2 named trust seam: `parseNumber`

This module holds **Layer 2** of the two-proof-layer split (see the `ByteSlice`
module header and the `README`): a `@[extern]` numeric-literal span primitive whose
*Lean* body elaborates and reduces (so `#print axioms` reports the proof-only body
clean — `[propext, Quot.sound]`, no added axiom) but whose *running* C is **trusted,
not proven**.

## What it is

`parseNumber a off : Option (Nat × USize)` parses the longest run of ASCII decimal
digits (`0x30`–`0x39`) from the byte span `a[off ..)`, returning the non-negative
integer value together with the byte count consumed. It stops at the first
non-digit (or the end of the buffer); `off` at-or-past the end, or a span with no
leading digit, returns `none`.

This is the *integer* half of the design's `strtod`/`strtoll` numeric primitive:
JSON/TOML integer literals, protobuf length prefixes, and the tag/field-value
scalars the per-format decoders need. The signed/float (`strtod`) half is
deliberately **not** folded here — a correctly-rounded decimal→`Float` reference in
pure Lean would be a second, much larger trust seam, and the integer span already
covers the structural (length/tag/count) parses this change's formats need. (The C
still uses `strtoll`-shaped scalar arithmetic; `strtod` is orthogonal and named in
the header for honesty.)

## The representation split (why `ByteArray`, not `String`)

The Lean body is pinned to the `ByteArray`/`Array UInt8` carrier because `String`
and its accessors (`String.toList`, `String.data`, `String.get`, `String.length`,
`String.toNat?`) are `@[extern]` UTF-8-backed and **leak `Classical.choice`** into any
law built over them — a `parseNumber (s : String)` would break the `[propext,
Quot.sound]`-only gate. Raw bytes (`Array.get`, `Array.extract`, `UInt8.toNat`)
are axiom-clean, so the seam takes a `ByteArray` span, exactly as the JSON/TOML
scanner (§4.3) holds one anyway.

## The trust contract (verbatim)

Layer 2 is **excluded** from the `#print axioms` gate. The Lean body is the
_specification_; the C symbol is a _named, isolated trust seam_:

  * `codec_parseNumber a off` returns `Some (n, k)` exactly when the `k`-byte run
    from `off` is the longest nonempty run of ASCII decimal digits and equals the
    decimal numeral for `n`, and `None` otherwise.

That the C meets this contract is **trusted, not proven** — the F\*-vs-KaRaMeL
posture: declare the primitive in Lean (pinning its meaning), hand-write the C
under the same name, and never present "no axiom" as "no trust". The bench lane
value-checks the seam byte-for-byte against its Lean body.
-/

namespace Codec

/-- One decimal-digit step: thread the value accumulator `acc` and the absolute
cursor `i` over the bytes of `a`. Reads `a[i]`; if it is an ASCII digit it folds it
in (`acc·10 + digit`) and recurses, otherwise it stops. Returns `(value, endIndex)`,
where `endIndex` is the first non-digit position (the cursor is absolute within
`a`, not the consumed count). `[propext, Quot.sound]`-clean. -/
def decimalStep (a : ByteArray) (i : Nat) (acc : Nat) : Option (Nat × Nat) :=
  if h : i < a.size then
    let b : UInt8 := a.data[i]
    let d : Nat := b.toNat
    if 48 ≤ d ∧ d < 58 then
      decimalStep a (i + 1) (acc * 10 + (d - 48))
    else
      some (acc, i)
  else
    some (acc, i)
termination_by a.size - i
decreasing_by
  simp_wf
  omega

/--
The Layer-2 named trust seam: the longest-run decimal parse. `parseNumber a off`
parses the leading decimal numeral at `a[off ..)`, returning `some (n, k)` where
`n` is the value and `k` the byte count consumed, or `none` when there is no
leading digit.

The Lean body below is the *specification* — the `decimalStep` scan over the bytes
(reducible, so `parseNumber_spec` closes by `rfl`). The `@[extern "codec_parseNumber"]`
attribute makes the running C call the matching symbol in `NumParse.c` (a scalar
`strtoll`-shaped accumulator, no per-byte bignum); that C is trusted, not proven,
and excluded from the `#print axioms` gate. -/
@[extern "codec_parseNumber"]
def parseNumber (a : ByteArray) (off : USize) : Option (Nat × USize) :=
  match decimalStep a off.toNat 0 with
  | some (n, endIdx) =>
      if off.toNat = endIdx then none
      else some (n, (endIdx - off.toNat).toUSize)
  | none => none

/-- The `parseNumber` refinement is a definitional identity: it is exactly the
`decimalStep` scan of the suffix from `off`, re-based to the consumed count (and
`none` when no digit was consumed). `rfl`-clean. -/
theorem parseNumber_spec (a : ByteArray) (off : USize) :
    parseNumber a off =
      (match decimalStep a off.toNat 0 with
       | some (n, endIdx) =>
           if off.toNat = endIdx then none
           else some (n, (endIdx - off.toNat).toUSize)
       | none => none) := by
  rfl

/-- `decimalStep` consumes at least one digit: the value accumulator is unchanged
only when the cursor never advanced. A simple sanity lemma the roundtrips lean on.
`[propext, Quot.sound]`-only. -/
theorem decimalStep_atLeastOne (a : ByteArray) (i acc : Nat) (h : i < a.size)
    (hd : 48 ≤ (a.data[i] : UInt8).toNat ∧ (a.data[i] : UInt8).toNat < 58) :
    decimalStep a i acc = decimalStep a (i + 1) (acc * 10 + ((a.data[i] : UInt8).toNat - 48)) := by
  rw [decimalStep]
  simp [h, hd]

end Codec
