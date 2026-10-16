/- Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later -/

import Codec.DecodeArray
import Codec.Decode

/-!
# The packed `ByteArray`-carrier decoder (the densest run-model)

The proven decoder `Codec.decode` runs over `Bytes = List UInt8` (a heap cons cell
per byte); `Codec.DecodeArray` shipped the F\*-style `Array UInt8` carrier (O(1)
indexed access, but each byte is still a boxed `UInt8`). This module adds the
**densest stdlib carrier**: `ByteArray`, the packed `uint8_t*` buffer
(`LeanScalarArray`) with cached size and O(1) `lean_byte_array_get!`. No per-byte
boxing.

The run-model here is a **native index recursion** — `decodeByteArrayRel` recurses
structurally on `d`, reading `a[i]` (the O(1) `lean_byte_array_get!` primop) in the
`byte` case and recursing `i + m` through `seq`, *never materializing a `List`*.
(An earlier "composition over `decodeArray`" draft re-materialized `a.data.toList`
and ran the list decoder, so it never read a packed byte.) The refinement
`decodeByteArrayRel_eq` closes by the one byte fact `a[i] = a.data[i]`
(`ByteArray.getElem_eq_getElem_data`) against `decodeArrayRel_eq`.

The full-consumption repetition `decodeFullByteArray` is **transferred**, not
re-derived: `decodeFullByteArray p h a i = decodeFullArray p h a.data i` through the
reducible `ByteArray.data` (an `Array UInt8`, never the opaque `ByteArray.toList`),
with `decodeFullByteArray_spec` closed whole from `decodeFullArray_spec`. The result
list `List α` is carrier-independent (list-building-bound), so a second native
`WellFounded.fix` recursion gains nothing — only the single/multi-byte *read* path
(`decodeByteArrayRel`, above) is native, where the O(1) packed read wins.
Everything `[propext, Quot.sound]`-only.
-/

namespace Codec

/-- The **native** run-model decoder: the number of bytes *consumed* relative to the
start index `i`, structurally identical to `decode` but reading `a[i]` (the packed,
O(1) `lean_byte_array_get!`) instead of cons-peeling, recursing `i + m` through
`seq`. No `List` is materialized from the buffer. -/
def decodeByteArrayRel {α : Type} (d : Codec α) (a : ByteArray) (i : Nat) : List (α × Nat) :=
  match d with
  | Codec.iso is d => (decodeByteArrayRel d a i).filterMap fun (x, n) => (is.apply x).map fun y => (y, n)
  | Codec.seq d₁ d₂ => (decodeByteArrayRel d₁ a i).flatMap fun (x, m) => (decodeByteArrayRel d₂ a (i + m)).map fun (y, n) => ((x, y), m + n)
  | Codec.alt d₁ d₂ => decodeByteArrayRel d₁ a i ++ decodeByteArrayRel d₂ a i
  | Codec.empty => []
  | Codec.pure x => [(x, 0)]
  | Codec.byte => if h : i < a.size then [(a[i], 1)] else []

/-- The packed indexed `ByteArray`-carrier decoder: every `(value, remaining-index)`
pair derivable from `d` against `a` starting at absolute position `i`, re-basing the
native relative-consumed count onto the absolute index. -/
def decodeByteArray {α : Type} (d : Codec α) (a : ByteArray) (i : Nat) : List (α × Nat) :=
  (decodeByteArrayRel d a i).map fun (x, n) => (x, i + n)

/-- The native recursion agrees with the `Array` run-model (`decodeArrayRel`): a
result `(x, n)` of `decodeByteArrayRel d a i` matches `decodeArrayRel d a.data i`
byte-for-byte (the `byte` case is `a[i] = a.data[i]`; `a.size = a.data.size`). -/
theorem decodeByteArrayRel_eq {α : Type} (d : Codec α) (a : ByteArray) (i : Nat) :
    decodeByteArrayRel d a i = decodeArrayRel d a.data i := by
  induction d generalizing a i with
  | iso is d ih => simp [decodeByteArrayRel, decodeArrayRel, ih]
  | seq d₁ d₂ ih₁ ih₂ => simp [decodeByteArrayRel, decodeArrayRel, ih₁, ih₂]
  | alt d₁ d₂ ih₁ ih₂ => simp [decodeByteArrayRel, decodeArrayRel, ih₁, ih₂]
  | empty => simp [decodeByteArrayRel, decodeArrayRel]
  | pure x => simp [decodeByteArrayRel, decodeArrayRel]
  | byte => simp [decodeByteArrayRel, decodeArrayRel]; split <;> simp [ByteArray.getElem_eq_getElem_data]

/-- The single refinement law: the `ByteArray` decoder equals the `Bytes` spec, in
the **function-level** form (lesson 2). Transferred from `decodeArray_eq` via
`decodeByteArrayRel_eq`, `[propext, Quot.sound]`-only. -/
theorem decodeByteArray_eq {α : Type} (d : Codec α) (a : ByteArray) (i : Nat) :
    decodeByteArray d a i =
      (decode d (a.data.toList.drop i)).map fun (x, r) => (x, i + ((a.data.toList.drop i).length - r.length)) := by
  rw [decodeByteArray, decodeByteArrayRel_eq]
  exact decodeArray_eq d a.data i

/-- The single-byte reading over the packed carrier: `decodeByteArray byte a i`
is `[(a[i], i + 1)]` when `i < a.size`, `[]` otherwise — the native `a[i]` read. -/
theorem decodeByteArray_byte (a : ByteArray) (i : Nat) :
    decodeByteArray Codec.byte a i =
      if h : i < a.size then [(a[i], i + 1)] else [] := by
  rw [decodeByteArray]
  simp [decodeByteArrayRel]
  split <;> simp

/-! ## The full-consumption repetition decoder (transferred)

The full-consumption repetition over the `ByteArray` carrier is defined by
composition with the `Array` run-model (`DecodeArray.decodeFullArray`), through the
reducible `ByteArray.data` (an `Array UInt8`, *not* the opaque `ByteArray.toList`):
`decodeFullByteArray p h a i = decodeFullArray p h a.data i`. This is **not** a
second native `WellFounded.fix` recursion: the full-consumption layer is
result-*list*-construction-bound (the `List α` accumulates regardless of carrier —
see `DecodeArray`'s own note that the O(1)-index win is on single/multi-byte
*reads*, not the list-building path), so a native recursion buys nothing here and
would only re-derive `decodeFullArrayStep`/`_some`/`_ne_none` a second time. The
native *read* recursion (`decodeByteArrayRel`, above) is left native; only the
full-consumption folding is transferred, which is the same shape the
`unfoldBy`/`DecodeArray` deduplication already settled.
-/

/-- The packed-carrier full-consumption repetition decoder: `some (xs, j)` iff the
productive `p` fully consumes the remaining bytes of `a` from index `i` as the list
`xs`, ending at `j = a.size`. Transferred from `DecodeArray.decodeFullArray` through
`a.data`. -/
def decodeFullByteArray {α : Type} (p : Codec α) (h : ConsumesByte p) (a : ByteArray) (i : Nat) :
    Option (List α × Nat) :=
  decodeFullArray p h a.data i

/-- The full-consumption law for the packed `ByteArray` carrier: `decodeFullByteArray
p h a i = some (xs, j)` iff `xs` is the (unique, under `huniq`) list that fully
consumes `drop i` via `decodeRepeat`, ending at `j = a.size`. Transferred whole from
`decodeFullArray_spec` in one reduction over `a.data` (`[propext, Quot.sound]`-only,
no new induction). -/
theorem decodeFullByteArray_spec {α : Type} (p : Codec α) (h : ConsumesByte p)
    (huniq : ∀ {x y : List α} {s : Bytes},
      (x, []) ∈ decodeRepeat p h s → (y, []) ∈ decodeRepeat p h s → x = y)
    (a : ByteArray) (i : Nat) (xs : List α) (j : Nat) :
    decodeFullByteArray p h a i = some (xs, j) ↔
      (xs, []) ∈ decodeRepeat p h (a.data.toList.drop i) ∧ j = a.size := by
  rw [decodeFullByteArray]
  exact decodeFullArray_spec p h huniq a.data i xs j

end Codec