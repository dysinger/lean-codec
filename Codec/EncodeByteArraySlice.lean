/- Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later -/

import Codec.EncodeByteArray
import Codec.Encode

/-!
# The packed `ByteArray.push` encode accumulator (the "carrier swap, not compiler" fix)

`encodeRepeat` accumulates the encoding in an O(n²) `List.append` fold (`encode (seq …)`
and every repetition step re-concatenates the growing prefix); the cost the bench
measures is that `List.append` fold plus one heap cons per byte. This module promotes
the **packed, amortized-O(n) `ByteArray.push` accumulator** to the committed encode
surface.

`encodeByteArrayBytes xs : ByteArray` folds `ByteArray.push` (the stdlib `@[extern]`
`lean_byte_array_push`, already a packed `uint8_t*` appender) over the byte list into a
single pre-grown buffer — **no custom C** (contrast `Codec.ExternFastPath`, whose
`encodeAppend` was a thin `@[extern]` shim over this same `push`; this module is the
"no extern framing" commitment the `slice-returning-run-model` design calls for). One
`List.foldl` materializes a single packed `ByteArray` at the end, never a per-byte
cons cell.

**Proved equal to the spec** by `encodeByteArrayBytes_eq_encodeRepeat`: the push fold's
bytes are exactly the `Bytes` `encodeRepeat Codec.byte` denotation (re-packed). Everything
`[propext, Quot.sound]`-only.
-/

namespace Codec

/-- `List.foldl` with `Array.push` builds `List.toArray` (accumulated in order): the
fold's `.toList` is the input appended to the accumulator's list. -/
theorem foldl_push_toArray (xs : List UInt8) (acc : Array UInt8) :
    xs.foldl (fun a b => a.push b) acc = (acc.toList ++ xs).toArray := by
  induction xs generalizing acc with
  | nil => simp
  | cons b rest ih =>
      rw [List.foldl_cons, ih]
      rw [List.push_toArray]
      simp

/-- The `ByteArray.push` fold commutes with `ByteArray.mk` over an `Array.push`
fold: pushing onto a packed accumulator wraps the same `Array.push` fold. -/
theorem foldl_ba_push (xs : List UInt8) (acc : Array UInt8) :
    xs.foldl (fun (a : ByteArray) b => a.push b) (ByteArray.mk acc) =
      ByteArray.mk (xs.foldl (fun (a : Array UInt8) b => a.push b) acc) := by
  induction xs generalizing acc with
  | nil => rfl
  | cons b rest ih =>
      simp only [List.foldl_cons]
      rw [show (ByteArray.mk acc).push b = ByteArray.mk (acc.push b) by rfl]
      rw [ih]

/-- The **packed encode accumulator**: fold `ByteArray.push` (amortized O(n)) over the
byte list into a single packed buffer, replacing the O(n²) `List.append` fold of
`encodeRepeat Codec.byte`. One fold materializes a single `ByteArray`; no per-byte cons
cell, no `@[extern]` of its own (`ByteArray.push` is the stdlib extern). -/
def encodeByteArrayBytes (xs : List UInt8) : ByteArray :=
  xs.foldl (fun acc b => acc.push b) ByteArray.empty

/-- The push accumulator agrees with the proven re-packed form:
`encodeByteArrayBytes xs = ByteArray.mk xs.toArray` (via `foldl_ba_push` +
`foldl_push_toArray`). `[propext, Quot.sound]`-only. -/
theorem encodeByteArrayBytes_eq (xs : List UInt8) :
    encodeByteArrayBytes xs = ByteArray.mk xs.toArray := by
  unfold encodeByteArrayBytes
  rw [show ByteArray.empty = ByteArray.mk #[] by rfl]
  rw [foldl_ba_push]
  rw [foldl_push_toArray]
  rfl

/-- `encodeByteArrayBytes xs` produces exactly the packed `xs` (roundtrip with
`ByteArray.data.toList`): the accumulator's bytes are the input list. -/
theorem encodeByteArrayBytes_data_toList (xs : List UInt8) :
    (encodeByteArrayBytes xs).data.toList = xs := by
  simp [encodeByteArrayBytes_eq]

/-- `encodeRepeat Codec.byte xs` re-encodes the byte list as itself. -/
theorem encodeRepeat_byte (xs : List UInt8) : encodeRepeat Codec.byte xs = some xs := by
  induction xs with
  | nil => simp [encodeRepeat]
  | cons b rest ih =>
      simp [encodeRepeat, encode]
      rw [ih]
      simp [single]

/-- **The refinement against the `Bytes` spec (task 2.2):** the O(n) push fold's bytes
equal the `List.append` `encodeRepeat Codec.byte` denotation (re-packed). The accumulator
*is* the packed form of the canonical byte encoding. `[propext, Quot.sound]`-only. -/
theorem encodeByteArrayBytes_eq_encodeRepeat (xs : List UInt8) :
    (encodeByteArrayBytes xs).data.toList = (encodeRepeat Codec.byte xs).get! := by
  rw [encodeByteArrayBytes_data_toList, encodeRepeat_byte]
  rfl

end Codec
