/- Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later -/

import Codec.Sound

/-!
# The packed byte buffer: the extraction-facing transport surface

The provable core (`Codec`, `Rel`, `decode`, `encode`, `roundtrip`, …) is stated
over `Bytes` (= `List UInt8`), because `List` reduces under `simp`/`rfl`/`induction`
and `ByteArray`'s FFI-backed operations do not. This module adds the **executable
surface**: a `Buffer`, a packed byte region backed by `ByteArray`, together with the
explicit transport `Buffer.toBytes`/`Buffer.ofBytes` and the transported interpreters
`decodeBuffer`/`encodeBuffer`.

The transport is an *abstraction barrier*, not a re-derivation: the interpreters are
defined by composing the proven `decode`/`encode` with `toBytes`/`ofBytes`, and the
laws (`roundtripBuffer`, the `decodeBuffer`/`encodeBuffer` correspondences) transfer
by rewriting through that barrier. Nothing here changes the denotation; it is the
`[D1]`-adjacent step of swapping in a packed representation *after* the proofs, so
extraction emits a flat buffer rather than per-byte `List.cons` cells.
-/

namespace Codec

/-- A packed byte buffer, the executable transport target. The field is a
`ByteArray`; extraction compiles this to a flat, contiguous byte region (no
per-byte heap allocation), unlike the `List`-backed `Bytes` used for proofs. -/
structure Buffer where
  /-- The underlying packed bytes. -/
  byteArray : ByteArray

namespace Buffer

/-- The empty buffer. -/
def empty : Buffer := ⟨ByteArray.empty⟩

/-- Transport a buffer onto the provable substrate: its bytes as a `List UInt8`.
Routed through `.data` (the reducible `Array`) rather than `ByteArray.toList`
(an opaque FFI projection), so the transport laws below close by `rfl`. -/
def toBytes (b : Buffer) : Bytes := b.byteArray.data.toList

/-- Transport a byte list onto the packed surface: `List.toArray` then `ByteArray.mk`. -/
def ofBytes (l : Bytes) : Buffer := ⟨ByteArray.mk l.toArray⟩

/-- `ofBytes` is a left inverse of `toBytes`: a byte list round-trips through the
packed representation unchanged. Reducible because `toBytes` goes through
`ByteArray.data` (an `Array`) and `List.toArray`/`Array.toList` are transparent. -/
theorem toBytes_ofBytes (l : Bytes) : toBytes (ofBytes l) = l := by
  rfl

/-- The empty byte list transports to the empty buffer. -/
theorem ofBytes_empty : ofBytes [] = empty := by
  apply congrArg Buffer.mk
  apply ByteArray.ext
  rfl

end Buffer

/-! ## The transported interpreters

`decodeBuffer`/`encodeBuffer` are the packed-surface readings of `decode`/`encode`,
defined by composing the proven interpreters with the `toBytes`/`ofBytes` barrier.
Their laws below are *transfer* lemmas: they state that the packed interpreters
agree with the `Bytes` ones, so every unconditional `Bytes`-level law
(`decode_spec`, `roundtrip`, …) holds for the packed surface by composition. -/

/-- Packed decoding: decode against the buffer's bytes, re-packing each remainder. -/
def decodeBuffer {α : Type} (d : Codec α) (b : Buffer) : List (α × Buffer) :=
  (decode d b.toBytes).map fun (x, r) => (x, Buffer.ofBytes r)

/-- Packed encoding: encode, then pack the result (or `none` out-of-domain). -/
def encodeBuffer {α : Type} (d : Codec α) (x : α) : Option Buffer :=
  match encode d x with
  | none => none
  | some l => some (Buffer.ofBytes l)

/-- `decodeBuffer` agrees with `decode` through the barrier: a packed result
`(x, r')` is exactly a `Bytes` result `(x, r)` re-packed. -/
theorem decodeBuffer_eq {α : Type} (d : Codec α) (b : Buffer) (x : α) (r' : Buffer) :
    (x, r') ∈ decodeBuffer d b ↔ ∃ r, (x, r) ∈ decode d b.toBytes ∧ r' = Buffer.ofBytes r := by
  rw [decodeBuffer, List.mem_map]
  constructor
  · intro h
    rcases h with ⟨pr, hpr, heq⟩
    rcases pr with ⟨x', r⟩
    have hx : x' = x := congrArg Prod.fst heq
    have hr : r' = Buffer.ofBytes r := (congrArg Prod.snd heq).symm
    subst x'
    rw [hr]
    exact ⟨r, hpr, rfl⟩
  · intro h
    rcases h with ⟨r, hpr, hr⟩
    rw [hr]
    exact ⟨(x, r), hpr, rfl⟩

/-- `encodeBuffer` agrees with `encode` through the barrier: it packs exactly the
`Bytes` encodings. (The fresh name `b` sits on the left of `=`, matching the
`decodeBuffer_eq`/`Buffer.ofBytes` convention.) -/
theorem encodeBuffer_eq {α : Type} (d : Codec α) (x : α) (b : Buffer) :
    encodeBuffer d x = some b ↔ ∃ l, encode d x = some l ∧ b = Buffer.ofBytes l := by
  rw [encodeBuffer]
  cases encode d x with
  | none => simp
  | some l =>
      simp
      rw [eq_comm]

/-- The packed roundtrip: a value encoded to a buffer decodes back to `x` with an
empty remainder. This is the `Buffer` reading of `roundtrip`, transferred through
the `toBytes`/`ofBytes` barrier (no new induction — it composes `roundtrip`). -/
theorem roundtripBuffer {α : Type} (d : Codec α) (x : α) (b : Buffer) :
    encodeBuffer d x = some b → (x, Buffer.empty) ∈ decodeBuffer d b := by
  intro hb
  rcases (encodeBuffer_eq d x b).1 hb with ⟨l, hl, rfl⟩
  have hrt : (x, []) ∈ decode d l := roundtrip d x l hl
  rw [decodeBuffer_eq]
  refine ⟨[], ?_, ?_⟩
  · simpa [Buffer.toBytes_ofBytes] using hrt
  · exact Buffer.ofBytes_empty

/-- The packed reading of `decode_spec` (the bidirectional law): `decodeBuffer d b`
yields `(x, Buffer.ofBytes r)` iff the buffer's bytes split as a `Rel`-prefix plus
`r`. Stated with a `Bytes` remainder (the provable substrate) so it transfers from
`decode_spec` via `decodeBuffer_eq` without the reverse (`ofBytes (toBytes b) = b`)
transport — no new induction. -/
theorem decodeBuffer_spec {α : Type} (d : Codec α) (b : Buffer) (x : α) (r : Bytes) :
    (x, Buffer.ofBytes r) ∈ decodeBuffer d b ↔
      ∃ s₀, b.toBytes = s₀ ++ r ∧ Rel d x s₀ := by
  rw [decodeBuffer_eq]
  constructor
  · intro h
    rcases h with ⟨r', hmem, hu⟩
    have hrr' : r' = r := by
      simpa [Buffer.toBytes_ofBytes] using (congrArg Buffer.toBytes hu).symm
    rcases (decode_spec d x).1 hmem with ⟨s₀, hs, hrel⟩
    rw [hrr'] at hs
    exact ⟨s₀, hs, hrel⟩
  · intro h
    rcases h with ⟨s₀, hs, hrel⟩
    refine ⟨r, ?_, rfl⟩
    rw [hs]
    exact (decode_spec d x).2 ⟨s₀, rfl, hrel⟩

end Codec
