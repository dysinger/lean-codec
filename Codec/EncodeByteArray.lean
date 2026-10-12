/- Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later -/

import Codec.EncodeArray

/-!
# The packed `ByteArray`-accumulating encoder (the densest run-model)

The encoder's dual to `Codec.DecodeByteArray`: `encode d x : Option (Bytes)` runs
the proven `encode` (one list-append fold); `encodeArray` materializes the
accumulated bytes as an `Array UInt8`. This module re-packs the same result as the
densest stdlib carrier `ByteArray` — the packed `uint8_t*` buffer, no per-byte
boxing — via the reducible `ByteArray.mk` over the already-proven `encodeArray`.

As with `encodeArray`, the accumulation is one `List`-fold materialized at the end
(`List.toArray`, then `ByteArray.mk`), never a per-byte `ByteArray.push`, so the
encode side stays O(n) amortized. The refinement `encodeByteArray_eq` transfers from
`encodeArray_eq` through the transparent `ByteArray.mk`/`ByteArray.data` pair.
-/

namespace Codec

/-- The packed `ByteArray`-accumulating encoder: `encode` a value and materialize
the result bytes as a single packed `ByteArray` (or `none` out-of-domain). Defined
by composition over the proven `encodeArray` then `ByteArray.mk`. -/
def encodeByteArray {α : Type} (d : Codec α) (x : α) : Option ByteArray :=
  (encodeArray d x).map ByteArray.mk

/-- The packed encoder agrees with the `Bytes` spec through the `ByteArray`/
`Array` barrier: `encodeByteArray d x = some a` iff `encode d x = some a.data.toList`.
Transferred from `encodeArray_eq`; `ByteArray.data (ByteArray.mk l) = l.toArray`
closes by `rfl`. `[propext, Quot.sound]`-only. -/
theorem encodeByteArray_eq {α : Type} (d : Codec α) (x : α) (a : ByteArray) :
    encodeByteArray d x = some a ↔ encode d x = some a.data.toList := by
  rw [encodeByteArray]
  calc
    (encodeArray d x).map ByteArray.mk = some a
        ↔ encodeArray d x = some a.data := by
          cases encodeArray d x <;> simp
          rename_i val
          constructor
          · intro h
            exact congrArg ByteArray.data h
          · intro h
            cases a
            simp [h]
    _ ↔ encode d x = some a.data.toList := encodeArray_eq d x a.data

/-- `encodeByteArray` is a left-inverse transport: re-encoding the `.data.toList`
of a packed output reproduces the packed output. -/
theorem encodeByteArray_mk {α : Type} (d : Codec α) (x : α) (l : Array UInt8) :
    encodeByteArray d x = some (ByteArray.mk l) ↔ encode d x = some l.toList := by
  simpa using (encodeByteArray_eq d x (ByteArray.mk l))

end Codec
