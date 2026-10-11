/- Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later -/

import Codec.Encode

/-!
# The array-accumulating encoder (the F\* run-model)

The proven encoder `Codec.encode` is stated over `Bytes = List UInt8`; its result
is a `List` whose every byte is a heap cons cell. The decoder's carrier swap
(`Codec.DecodeArray`) needs its dual on the encode side so the roundtrip can be
stated over a packed representation.

The encoder is the cheaper half: `encode` already list-accumulates and appends, so
the only change is the result carrier. `encodeArray` runs the proven `encode` and
materializes the accumulated `Bytes` as a single `Array UInt8` (via `List.toArray`,
which reduces to the `List`-backed `Array.mk`) — one fold at the end, never a
per-byte `Array.push`. Its refinement `encodeArray_eq` closes by `cases` on
`encode` plus the `List.toArray`/`Array.toList` transparency; `Array UInt8` (rather
than `ByteArray`) is the carrier so `a.toList` reduces under `simp`/`rfl`.
-/

namespace Codec

/-- The array-accumulating encoder: `encode` a value and materialize the result
bytes as a single `Array UInt8` (or `none` out-of-domain). -/
def encodeArray {α : Type} (d : Codec α) (x : α) : Option (Array UInt8) :=
  match encode d x with
  | none => none
  | some l => some l.toArray

/-- The array-accumulating encoder agrees with the list spec: it produces exactly
the `Array` whose `.toList` is the `Bytes` encoding. Proved by `cases` on `encode`
plus `List.toArray`/`Array.toList` transparency (`List.toArray` reducibly wraps the
`List`, so `l.toArray.toList = l` and `a.toList.toArray = a` are `rfl`); no new
induction. `[propext, Quot.sound]`-only. -/
theorem encodeArray_eq {α : Type} (d : Codec α) (x : α) (a : Array UInt8) :
    encodeArray d x = some a ↔ encode d x = some a.toList := by
  rw [encodeArray]
  cases h : encode d x with
  | none => simp
  | some l =>
      simp only [Option.some.injEq]
      constructor
      · intro h
        exact congrArg Array.toList h
      · intro h
        rw [h]

end Codec
