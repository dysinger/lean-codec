/- Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later -/

import Codec.DecodeByteArray
import Codec.EncodeByteArray

/-!
# The trusted `@[extern]` C fast path (F\*-style buffer-edge seam)

The codec's run-model is **proved**, but the reason it is not yet *fast* is the
Lean C generator's boxed, GC'd representation (`Nat` as bignum, `List UInt8` cons
cells, unions as closures). The full fix — a separate GC-less C target — is
`compiler-tier-extraction` (weeks). This module is the **stopgap that lands
first**: it splices hand-written, GC-less C into the *already proved* `ByteArray`
run-model's hot path via Lean's existing `@[extern]` FFI, exactly the posture
F\* uses for its trusted primitives and Lean's own stdlib already uses for
`ByteArray` itself (`ByteArray.get` ⇒ `lean_byte_array_fget`, `ByteArray.size` ⇒
`lean_sarray_size`, …).

**The trust posture.** Each primitive below is a *plain `def`* whose **Lean body
still elaborates** — so `simp`/`rfl` and the refinement lemmas
(`decodeByteArray_eq` / `decodeFullByteArray_spec` / `encodeByteArray_eq`) keep
seeing the *meaning*, pinned in Lean, and the codec's laws stay
`[propext, Quot.sound]`-only. The `@[extern "codec_…"]` tag only swaps the
*emitted* code for trusted C supplied by `Codec/ExternFastPath.c` (libc-only,
passing through the Lean runtime's inline `sarray`/push primitives, no new
`lean_rt` dependency of its own). That C is trusted to satisfy its declared
contract — a **named, isolated trust seam at the buffer edge**, the same stance
F\* takes toward KaRaMeL / the Pulse `read0`/`emplace` primitives. It does not
introduce a proof axiom: the Lean body, not the C, is what the theorem prover
reasons about.

**Why this shape.** The stdlib already owns the per-element `@[extern]`s
(`ByteArray.get`, `size`, `push`, …). The *remaining* boxed overhead is paid by
the run-model's own recursion — `Nat` index arithmetic, `List` cons-ing, and the
`WellFounded.fix` measure recomputation. This change exposes two dedicated,
specialized C loops that fold that overhead away *inside one trusted call*:

  * `codec_byte_array_slice` — a full-consumption `uint8_t *` copy (`memcpy`-style)
    of the packed suffix `a[i .. a.size)` into a fresh `ByteArray`: the
    `Codec.byte` full-consumption hot path, one bounds-checked C loop instead of
    `n` Lean-indexed `a[i]` calls and the general `copySlice`'s three
    `extract`+concats.
  * `codec_encode_append` — a single-byte amortized append into a packed
    accumulator (the encode accumulation; the Lean body is `ByteArray.push`).

The `(ptr, len)` slice accessors of a C slice are subsumed by the return value
being a `ByteArray` (whose `size`/`data` are themselves stdlib
`@[extern]`s), so no `List UInt8` and no `(ptr, len)` pair is materialized or
returned across the seam: the result stays a packed buffer.
-/

namespace Codec.ExternFastPath

/-! ## Slice copy (the raw byte loop) -/

/-- Copy the suffix `a[i .. a.size)` into a fresh packed `ByteArray`.

The Lean body is `ByteArray.mk ((a.data.toList.drop i).toArray)` — it reduces
over the reducible `Array.data.toList`/`List.toArray` pair (`Array` is the
`List`-backed structure, `Array.toList (List.toArray l) = l` by `rfl`), so
`(byteSlice a i).data.toList = a.data.toList.drop i` closes by `rfl` — keeping the
codec's laws `[propext, Quot.sound]`-only. The extern symbol `codec_byte_array_slice`
is a hand-written, bounds-checked `memcpy`-style loop (the *executed* body; the
Lean body is proof-only and never code-generated), specializing the suffix case
that the general `copySlice`'s three `extract`+concats would otherwise pay.
-/
@[extern "codec_byte_array_slice"]
def byteSlice (a : ByteArray) (i : Nat) : ByteArray :=
  ByteArray.mk ((a.data.toList.drop i).toArray)

/-- The suffix slice carries exactly `a.size - i` bytes. -/
theorem byteSlice_size (a : ByteArray) (i : Nat) :
    (byteSlice a i).size = a.size - i := by
  unfold byteSlice ByteArray.size
  simp

/-- The suffix slice's bytes are the tail of `a`'s bytes: `drop i`. This is the
named trust contract the hand-written C loop (`memcpy` of `a[i .. size)`) must
preserve — it is the *Lean body* redex (`rfl`, `List.toArray`/`Array.toList` are
mutual inverses over the reducible `Array`), so it is `[propext, Quot.sound]`-only
(no `Classical.choice` from the stdlib's `Array.toList_extract`). -/
theorem byteSlice_data_toList (a : ByteArray) (i : Nat) :
    (byteSlice a i).data.toList = a.data.toList.drop i := by
  rfl

/-! ## Encode append (amortized accumulation) -/

/-- Append one byte into an accumulator `ByteArray`, growing it amortized-O(1)
(reusing `ByteArray.push`, whose `@[extern]` symbol
`lean_byte_array_push` already owns the growth). The Lean body is `a.push b`; the
extern symbol `codec_encode_append` is the thin C wrapper that keeps the encode
accumulation on the packed `uint8_t *` path (no per-byte box, no `List` cell).
-/
@[extern "codec_encode_append"]
def encodeAppend (a : ByteArray) (b : UInt8) : ByteArray := a.push b

/-- `encodeAppend` is `ByteArray.push` — the trust contract in Lean. -/
theorem encodeAppend_eq (a : ByteArray) (b : UInt8) : encodeAppend a b = a.push b := rfl

/-- `encodeAppend` appends exactly one byte: the result's bytes are `a`'s bytes
plus `b`. -/
theorem encodeAppend_toList (a : ByteArray) (b : UInt8) :
    (encodeAppend a b).data.toList = a.data.toList ++ [b] := by
  simp [encodeAppend_eq]

/-! ## Routing the run-model hot path (§2)

These re-stage the *proved* run-model's `byte`/full-consumption/accumulation
hot paths over the two primitives above, each with an equality law closing
against the existing (proved) functions — `[propext, Quot.sound]`-only, no new
axiom. -/

open Codec

/-- The full-consumption result of `decodeRepeat Codec.byte` is the input
alone: `(s, [])` is enumerated. Proved by induction on `s` via `decodeRepeat_eq`
+ `decode Codec.byte`. -/
theorem decodeRepeat_byte_full (s : Bytes) :
    (s, []) ∈ decodeRepeat Codec.byte byte_consumesByte s := by
  induction s with
  | nil => rw [decodeRepeat_eq]; simp
  | cons b rest ih =>
      rw [decodeRepeat_eq]
      simp [decode]
      exact ih

/-- The **uniqueness** of `Codec.byte`'s full consumption: any full-consuming
decode of `s` equals `s` (the `huniq` hypothesis `decodeFull_spec` takes). -/
theorem decodeRepeat_byte_unique {x : List UInt8} {s : Bytes}
    (hmem : (x, []) ∈ decodeRepeat Codec.byte byte_consumesByte s) : x = s := by
  induction s generalizing x with
  | nil =>
      rw [decodeRepeat_eq] at hmem
      simp [decode] at hmem
      exact hmem
  | cons b rest ih =>
      rw [decodeRepeat_eq] at hmem
      simp [decode] at hmem
      rcases hmem with ⟨a, ha, hb⟩
      subst x
      rw [ih ha]

/-- The **fast** full-consumption `Codec.byte` decoder: one `codec_byte_array_slice`
call reads the packed suffix `a[i .. a.size)` (the `memcpy` loop), then
materializes the `List UInt8` at the boundary. Replaces the `WellFounded.fix`
recursion of `decodeFullByteArray` (per-byte `a[i]` reads + `Nat` measure
recomputation) with a single trusted C call. -/
def decodeFullByteArrayByte (a : ByteArray) (i : Nat) : Option (List UInt8 × Nat) :=
  some ((byteSlice a i).data.toList, a.size)

/-- The fast path agrees with the proved `decodeFullByteArray` at `Codec.byte`:
the single C slice `byteSlice` reads exactly the bytes the `WellFounded.fix`
recursion would (`a.data.toList.drop i`), ending at `a.size`. Closes by
`decodeFullByteArray_spec` + `byteSlice_data_toList` + `decodeRepeat_byte_unique`.
`[propext, Quot.sound]`-only. -/
theorem decodeFullByteArrayByte_eq (a : ByteArray) (i : Nat) :
    decodeFullByteArrayByte a i = decodeFullByteArray Codec.byte byte_consumesByte a i := by
  rw [decodeFullByteArrayByte]
  rw [(decodeFullByteArray_spec Codec.byte byte_consumesByte
      (fun {x y} {s} hx hy => (decodeRepeat_byte_unique hx).trans (decodeRepeat_byte_unique hy).symm)
      a i ((byteSlice a i).data.toList) a.size).mpr]
  · constructor
    · rw [byteSlice_data_toList]
      exact decodeRepeat_byte_full (a.data.toList.drop i)
    · rfl

/-- `List.foldl` with `Array.push` builds the `List.toArray` (accumulated in
order): the fold's `.data` is the input list appended to the accumulator. -/
theorem foldl_push_toArray (xs : List UInt8) (acc : Array UInt8) :
    xs.foldl (fun a b => a.push b) acc = (acc.toList ++ xs).toArray := by
  induction xs generalizing acc with
  | nil => simp
  | cons b rest ih =>
      rw [List.foldl_cons, ih]
      rw [List.push_toArray]
      simp

/-- The `ByteArray.push` fold commutes with `ByteArray.mk` over an `Array.push`
fold: pushing bytes onto a packed accumulator wraps the same `Array.push` fold. -/
theorem foldl_ba_push (xs : List UInt8) (acc : Array UInt8) :
    xs.foldl (fun (a : ByteArray) b => a.push b) (ByteArray.mk acc) =
      ByteArray.mk (xs.foldl (fun (a : Array UInt8) b => a.push b) acc) := by
  induction xs generalizing acc with
  | nil => rfl
  | cons b rest ih =>
      simp only [List.foldl_cons]
      rw [show (ByteArray.mk acc).push b = ByteArray.mk (acc.push b) by rfl]
      rw [ih]

/-- The **fast** encode accumulator: fold `codec_encode_append` (amortized
`ByteArray.push`) over the byte list into a single packed buffer, replacing the
`List`-append fold of `encodeRepeat Codec.byte` (one heap cons + concat per byte)
with appends into a pre-sized `uint8_t *` buffer. -/
def encodeByteArrayBytes (xs : List UInt8) : ByteArray :=
  xs.foldl (fun acc b => encodeAppend acc b) ByteArray.empty

/-- The fast encode accumulator agrees with the proven `encodeRepeat Codec.byte`
re-packed: `encodeByteArrayBytes xs = ByteArray.mk xs.toArray` (via
`foldl_ba_push` + `foldl_push_toArray`). `[propext, Quot.sound]`-only. -/
theorem encodeByteArrayBytes_eq (xs : List UInt8) :
    encodeByteArrayBytes xs = ByteArray.mk xs.toArray := by
  unfold encodeByteArrayBytes
  rw [show (fun acc b => encodeAppend acc b) = (fun acc b => acc.push b) by
        funext a b; simp [encodeAppend_eq]]
  change xs.foldl (fun acc b => acc.push b) ByteArray.empty = ByteArray.mk xs.toArray
  rw [show ByteArray.empty = ByteArray.mk #[] by rfl]
  rw [foldl_ba_push]
  rw [foldl_push_toArray]
  rfl

/-- `encodeByteArrayBytes xs` produces exactly the packed `xs` (roundtrip with
`ByteArray.toList`): the fast accumulator's bytes are the input list. Proved via
`encodeByteArrayBytes_eq` + the reducible `List.toArray`. -/
theorem encodeByteArrayBytes_data_toList (xs : List UInt8) :
    (encodeByteArrayBytes xs).data.toList = xs := by
  simp [encodeByteArrayBytes_eq]

/-- `encodeRepeat Codec.byte xs` re-encodes the byte list as itself (each `byte`
step emits `single b`, concatenated in order). -/
theorem encodeRepeat_byte (xs : List UInt8) : encodeRepeat Codec.byte xs = some xs := by
  induction xs with
  | nil => simp [encodeRepeat]
  | cons b rest ih =>
      simp [encodeRepeat, encode]
      rw [ih]
      simp [single]

/-- The fast encode accumulator is the packed form of `encodeRepeat Codec.byte`:
the bytes it encodes are exactly `(encodeRepeat Codec.byte xs).get! = xs`. -/
theorem encodeByteArrayBytes_eq_encodeRepeat (xs : List UInt8) :
    (encodeByteArrayBytes xs).data.toList = (encodeRepeat Codec.byte xs).get! := by
  rw [encodeByteArrayBytes_data_toList, encodeRepeat_byte]
  rfl

end Codec.ExternFastPath
