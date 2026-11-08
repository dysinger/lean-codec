/- Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later -/

import Codec.Decode
import Codec.Encode
import Codec.ByteSlice

/-!
# The packed result carrier

This file gives the **packed result carrier** for the interpreter: a decoder
that reads `a[i]` by a scalar index and threads only the consumed count, and an
encoder that accumulates into a contiguous `Array UInt8`. Each is proved equal to
the unchanged `Bytes n := Fin n → UInt8` spec by a refinement lemma that closes
`[propext, Quot.sound]`-only.

## Cursor type

The packed carrier is indexed by `Nat` (the consumed count), not `USize`. The
reason is proof-first: `USize` addition is `Nat` addition modulo `2^64`
(`USize.toNat_add : (a + b).toNat = (a.toNat + b.toNat) % 2^64`), and
`USize.size = 2^64` depends on `System.Platform.numBits = 64` — a platform fact
that is not cleanly provable in the stdlib. A `USize`-cursor refinement would
therefore carry an unproven platform/modulo premise into every law, violating the
`[propext, Quot.sound]`-only gate. The `Nat` cursor is the same choice
`fastEncodeRepeat`/`pushBytesFrom` already make and keep `#print axioms`-clean.
(The `USize`-lowers-to-`size_t` scalar claim is verified or refuted by IR
inspection — see the bench/tasks notes — never asserted here.)

## The bridge

The spec `decode : Codec α → {n} → Bytes n → List (α × Suffix n)` returns a
`Suffix n` (a length-indexed remainder). The packed decoder returns `List (α × Nat)`
— the `Nat` is the consumed count. The bridge reconstructs the spec's `Suffix n`
from the consumed count `c` (with `c ≤ n`) as

    { remaining := n - c, hle := Nat.sub_le n c, bytes := bdrop c s }

where `s : Bytes n` is the readback of the array (`fun i => a[i.val]`).
-/

namespace Codec

/-! ## Bridge: read `Array UInt8` back as `Bytes` -/

/-- Read a contiguous `Array UInt8` back as a length-indexed `Bytes a.size`:
`fun i => a[i.val]`. A pure `Array.get` read, no `ofFn` round-trip (which would
leak a third axiom). -/
def arrayToBytes (a : Array UInt8) : Bytes a.size :=
  fun i => a[i.val]

/-- Pack a length-indexed `Bytes n` into a contiguous `Array UInt8`.

This is the **one** `Bytes n → Array` transport in the library, and it is stated
here so that a caller does not invent its own. It goes through `List.ofFn`, which
is the `Fin n`-indexed enumeration; the result's size is `n` by `List.ofFn`'s own
length fact, so the round-trip `arrayToBytes (bytesToArray s) = s` needs no
`Array.extract`/`toList` machinery — which is the transport family `README.md`'s
"Representations" section records as removed precisely because it was the choice-axiom
source in the old `List`-carrier design.

(An earlier revision of this docstring said that round-trip was "`rfl` by
`funext`/`Fin.ext`". **It is not**: it needs `Array.getElem_toList` then
`List.getElem_ofFn`, plus a size transport, and it is proved as
`arrayToBytes_bytesToArray` next to `decodeWholeBytes_eq` rather than here.) -/
def bytesToArray {n : Nat} (s : Bytes n) : Array UInt8 :=
  Array.mk (List.ofFn s)

/-- The packing transport is size-preserving: `(bytesToArray s).size = n`.
`rfl`, because `Array.mk`'s size is the list's length and `List.ofFn`'s is its
index. -/
-- **Disclosed duplicate** (`codec-audit-round-nine` review A-9): `Codec.decodeWholeBytes_size`
-- (`Codec/Decode.lean`) states **exactly** this proposition and is literally
-- `bytesToArray_size s`, so the partition counts two laws where one statement is proved.
-- Kept because `decodeWholeBytes_size` is the name a caller of `decodeWholeBytes` looks
-- for, and removing either moves the gate's asserted partition — a change to the gate's
-- record, not a correction to a proof.
theorem bytesToArray_size {n : Nat} (s : Bytes n) : (bytesToArray s).size = n := by
  -- Named lemmas only: `simp [bytesToArray]` reaches `List.length_ofFn` through a
  -- classical route and leaks `Classical.choice` (checked with `#print axioms`),
  -- which is exactly the transport-lemma hazard the removed `List` carrier had.
  show (List.ofFn s).length = n
  exact List.length_ofFn

/-! ## The packed decoder -/

/-- The packed decoder: read bytes by an `Array UInt8` index and thread a consumed
count. Structurally identical to `decode`, but the result is `List (α × Nat)` — the
`List` is the non-determinism multiplicity (the `alt`/`seq` result), and the `Nat`
is the packed consumed count. `a[i]` is an `Array.get` (an `@[extern]` contiguous
read); there is no list-peeling. -/
def decodeArray {α : Type} (d : Codec α) (a : Array UInt8) (i : Nat) : List (α × Nat) :=
  match d with
  | Codec.iso j d =>
      (decodeArray d a i).filterMap fun (x, c) => (j.apply x).map fun y => (y, c)
  | Codec.seq d₁ d₂ =>
      (decodeArray d₁ a i).flatMap fun (x, c₁) =>
        (decodeArray d₂ a c₁).flatMap fun (y, c₂) => [((x, y), c₂)]
  | Codec.alt d₁ d₂ => decodeArray d₁ a i ++ decodeArray d₂ a i
  | Codec.empty => []
  | Codec.pure x => [(x, i)]
  | Codec.byte =>
      if h : i < a.size then
        [(a[i], i + 1)]
      else []
  | Codec.satisfy p =>
      if h : i < a.size then
        let b := a[i]
        if p b then [(b, i + 1)] else []
      else []

/-- The cursor-returning decoder, re-exposed under a name that states the
partial-remainder contract: `decodeArrayFast := decodeArray`. It is **not** a new
decoder — `decodeArray` already returns `(value, consumed count)` pairs and
materializes **no** suffix during decode: a decode yielding `k` backtracking
results does **zero** suffix copies, not `k`.

What it does *not* do is call the Layer-2 `commitRemainder` seam. That seam is
**available but unused** here — the proven path deliberately builds its suffix
with the list-materializing `ByteArray.mk ((a.toList.drop c).toArray)` transport
(below), so its refinement consults no choice principle and needs no trusted
`@[extern]`. `Codec/ByteSlice.lean` states the same thing from its side; the two
headers agree, and neither calls `commitRemainder` "the deferred commit" of a path
that never makes one.

The `Nat` cursor is a fixed binding decision (see the module header): it is the
proof carrier, kept `[propext, Quot.sound]`-clean; the `Nat → USize` conversion
happens once at the call site, if the caller ever commits a cursor. -/
def decodeArrayFast {α : Type} (d : Codec α) (a : Array UInt8) (i : Nat) : List (α × Nat) :=
  decodeArray d a i

/-- `decodeArrayFast` is `decodeArray`: the name exists to state the
partial-remainder contract, not to change the decoder. A `rfl` law, recorded because
§1.8's definition-coverage check treats an unmentioned `def` as a gap — and a
contract-only alias deserves to have its contract *stated*, not only written in a
docstring. -/
theorem decodeArrayFast_eq {α : Type} (d : Codec α) (a : Array UInt8) (i : Nat) :
    decodeArrayFast d a i = decodeArray d a i :=
  rfl

/-! ## The packed full-consumption result -/

/-- The packed full-consumption decoder: a single suffix copy, never
`Option (List α × Suffix n)`. Its body is the `rfl`-clean
`ByteArray.mk ((a.toList.drop i).toArray)` — a list-materializing transport
(chosen so the refinement consults no choice principle), **not**
`copySlice`/`extract`. The `c` in the result is the consumed count; the packed
suffix is the `ByteArray` of the bytes at-or-after `c`. -/
def decodeFullArray {α : Type} (d : Codec α) (a : Array UInt8) (i : Nat) :
    Option (ByteArray × Nat) :=
  match decodeArray d a i with
  | [] => none
  | (_, c) :: _ => some (ByteArray.mk ((a.toList.drop c).toArray), c)

/-! ## The packed encoder -/

/-- The byte-sequence packer: fold a `List UInt8` into a `ByteArray` by
`ByteArray.push` (amortized O(n)) — a *byte-sequence* packer, **not** a general
`Codec α` encoder (that is `encodeArray`). -/
def encodeByteArrayBytes (xs : List UInt8) : ByteArray :=
  xs.foldl (fun acc b => acc.push b) ByteArray.empty

/-- The packed encoder: produce an `Array UInt8` by accumulating with
`Array.append` instead of a nested `concat` closure. Structural (not `partial`),
matching `encode`, so the refinement `encodeArray_eq` is provable by induction on
`d`. -/
def encodeArray {α : Type} (d : Codec α) (x : α) : Option (Array UInt8) :=
  match d with
  | Codec.iso j d => (j.unapply x).bind fun a => encodeArray d a
  | Codec.seq d₁ d₂ =>
      match x with
      | (x₁, x₂) =>
          (encodeArray d₁ x₁).bind fun s₁ =>
            (encodeArray d₂ x₂).map fun s₂ => s₁ ++ s₂
  | Codec.alt d₁ d₂ => encodeArray d₁ x <|> encodeArray d₂ x
  | Codec.empty => none
  | Codec.pure x₀ => if x = x₀ then some #[] else none
  | Codec.byte => some #[x]
  | Codec.satisfy p => if p x then some #[x] else none

/-! ## Refinement lemmas -/

/-- The consumed count a `Suffix (a.size - i)` produces against a buffer starting
at absolute cursor `i`: the absolute consumed count is `i + ((a.size - i) - t.remaining)`.
This is the packed-carrier readback of the spec's `Suffix` remainder. -/
def consumedAbs (a : Array UInt8) (i : Nat) (t : Suffix (a.size - i)) : Nat :=
  i + ((a.size - i) - t.remaining)

/-- The identity suffix consumes nothing: `consumedAbs a i (Suffix.id …) = i`. -/
theorem consumedAbs_id (a : Array UInt8) (i : Nat) :
    consumedAbs a i (Suffix.id (a.size - i) (bdrop i (arrayToBytes a))) = i := by
  dsimp [consumedAbs, Suffix.id]
  omega

/-- Dropping one byte consumes exactly one: `consumedAbs a i (Suffix.drop 1 s) = i + 1`
when the suffix is non-empty (`i < a.size`). -/
theorem consumedAbs_drop_one (a : Array UInt8) (i : Nat) (s : Bytes (a.size - i))
    (h : i < a.size) :
    consumedAbs a i (Suffix.drop 1 s) = i + 1 := by
  dsimp [consumedAbs, Suffix.drop]
  omega

/-- The packed decoder never moves the cursor **backward**: every result's consumed
count `c` is at least the starting cursor `i`. This is the unconditional monotonicity
fact. Note the *upper* bound `c ≤ a.size` — the "never overruns" guarantee — is **not**
unconditional: `pure x` returns `(x, i)` for *any* `i`, so a cursor already past the end
(`i > a.size`) yields `c = i > a.size`. The upper bound therefore needs the `i ≤ a.size`
precondition and is stated separately in `decodeArray_bounded_upper`.
`[propext, Quot.sound]`-only. -/
theorem decodeArray_bounded {α : Type} (d : Codec α) (a : Array UInt8) (i c : Nat)
    (x : α) :
    (x, c) ∈ decodeArray d a i → i ≤ c := by
  induction d generalizing i c with
  | iso j d ih =>
      intro hc
      rw [decodeArray, List.mem_filterMap] at hc
      rcases hc with ⟨pr, hmem, hm⟩
      have hc : c = pr.2 := by
        cases hj : j.apply pr.1 with
        | none => simp [hj] at hm
        | some y =>
            simp [hj] at hm
            exact hm.2.symm
      subst c
      exact ih i pr.2 pr.1 hmem
  | seq d₁ d₂ ih₁ ih₂ =>
      intro hc
      rw [decodeArray, List.mem_flatMap] at hc
      rcases hc with ⟨pr₁, h1, h2⟩
      rw [List.mem_flatMap] at h2
      rcases h2 with ⟨pr₂, h3, h4⟩
      replace h4 : x = (pr₁.1, pr₂.1) ∧ c = pr₂.2 := by simpa using h4
      rcases h4 with ⟨hx, hc2⟩
      subst c
      have hb1 := ih₁ i pr₁.2 pr₁.1 h1
      have hb2 := ih₂ pr₁.2 pr₂.2 pr₂.1 h3
      exact Nat.le_trans hb1 hb2
  | alt d₁ d₂ ih₁ ih₂ =>
      intro hc
      rw [decodeArray, List.mem_append] at hc
      rcases hc with hc | hc
      · exact ih₁ i c x hc
      · exact ih₂ i c x hc
  | empty =>
      intro hc
      simp [decodeArray] at hc
  | pure x₀ =>
      intro hc
      simp [decodeArray] at hc
      rcases hc with ⟨hx, hc⟩
      subst x c
      exact Nat.le_refl i
  | byte =>
      intro hc
      rw [decodeArray] at hc
      by_cases h : i < a.size
      · simp [h] at hc
        rcases hc with ⟨hx, hc⟩
        subst x c
        exact Nat.le_succ i
      · simp [h] at hc
  | satisfy p =>
      intro hc
      rw [decodeArray] at hc
      by_cases h : i < a.size
      · simp [h] at hc
        by_cases hp : p a[i]
        · simp [hp] at hc
          rcases hc with ⟨hx, hc⟩
          subst x c
          exact Nat.le_succ i
        · simp [hp] at hc
      · simp [h] at hc

/-- The packed decoder never overruns the buffer **when started inside it**: for
`i ≤ a.size`, every result's consumed count `c` is at most `a.size`. This is the
"never overruns" upper bound the packed carrier enjoys a valid cursor — the
consumed count is `i + ((a.size - i) - t.remaining)` for a genuine suffix `t` (with
`t.remaining ≤ a.size - i`), so it is bounded by `i + (a.size - i) = a.size`. The
`i ≤ a.size` precondition is load-bearing: without it `pure x` yields `c = i > a.size`
(see `decodeArray_bounded`). `[propext, Quot.sound]`-only. -/
theorem decodeArray_bounded_upper {α : Type} (d : Codec α) (a : Array UInt8) (i c : Nat)
    (x : α) (hi : i ≤ a.size) :
    (x, c) ∈ decodeArray d a i → c ≤ a.size := by
  induction d generalizing i c with
  | iso j d ih =>
      intro hc
      rw [decodeArray, List.mem_filterMap] at hc
      rcases hc with ⟨pr, hmem, hm⟩
      have hc : c = pr.2 := by
        cases hj : j.apply pr.1 with
        | none => simp [hj] at hm
        | some y =>
            simp [hj] at hm
            exact hm.2.symm
      subst c
      exact ih i pr.2 pr.1 hi hmem
  | seq d₁ d₂ ih₁ ih₂ =>
      intro hc
      rw [decodeArray, List.mem_flatMap] at hc
      rcases hc with ⟨pr₁, h1, h2⟩
      rw [List.mem_flatMap] at h2
      rcases h2 with ⟨pr₂, h3, h4⟩
      replace h4 : x = (pr₁.1, pr₂.1) ∧ c = pr₂.2 := by simpa using h4
      rcases h4 with ⟨hx, hc2⟩
      subst c
      have hb1 := ih₁ i pr₁.2 pr₁.1 hi h1
      have hb2 := ih₂ pr₁.2 pr₂.2 pr₂.1 hb1 h3
      exact hb2
  | alt d₁ d₂ ih₁ ih₂ =>
      intro hc
      rw [decodeArray, List.mem_append] at hc
      rcases hc with hc | hc
      · exact ih₁ i c x hi hc
      · exact ih₂ i c x hi hc
  | empty =>
      intro hc
      simp [decodeArray] at hc
  | pure x₀ =>
      intro hc
      simp [decodeArray] at hc
      rcases hc with ⟨hx, hc⟩
      subst x c
      exact hi
  | byte =>
      intro hc
      rw [decodeArray] at hc
      by_cases h : i < a.size
      · simp [h] at hc
        rcases hc with ⟨hx, hc⟩
        subst x c
        omega
      · simp [h] at hc
  | satisfy p =>
      intro hc
      rw [decodeArray] at hc
      by_cases h : i < a.size
      · simp [h] at hc
        by_cases hp : p a[i]
        · simp [hp] at hc
          rcases hc with ⟨hx, hc⟩
          subst x c
          omega
        · simp [hp] at hc
      · simp [h] at hc

/-! ## Transport lemmas for the decode refinement

The decode-side `Suffix`-transport bridge. The spec's `decode d s` returns
`(x, t)` with `t : Suffix n`; the packed `decodeArray d a i` returns `(x, c)` with
the absolute consumed count `c`. The bridge is `consumedAbs a i t` (`i` plus the
count consumed within `s`), and these lemmas transport a `bdrop`/`Suffix.trans`
across it. `[propext, Quot.sound]`-only. -/

/-- `(n - i) - m = n - (i + m)`. The length identity behind
`bdrop` composition (`Nat.sub_sub`). -/
theorem sub_sub_eq {n i m : Nat} : (n - i) - m = n - (i + m) := by
  exact Nat.sub_sub n i m

/-- `bdrop (i + m) s` is `bdrop m (bdrop i s)` up to the length cast
`(n - i) - m = n - (i + m)`. The composition law the `seq` bridge needs.
`[propext, Quot.sound]`-only. -/
theorem bdrop_add {n i m : Nat} (s : Bytes n) :
    bdrop (i + m) s = cast (congrArg Bytes (sub_sub_eq (n := n) (i := i) (m := m))) (bdrop m (bdrop i s)) := by
  apply Bytes.ext
  intro k
  unfold bdrop
  rw [cast_bytes_val (e := sub_sub_eq (n := n) (i := i) (m := m))]
  congr 1
  apply Fin.ext
  dsimp
  omega

/-- The length identity: the length left after consuming `consumedAbs a i t` bytes is
exactly `t.remaining`. `[propext, Quot.sound]`-only. -/
theorem consumedAbs_remaining (a : Array UInt8) (i : Nat) (t : Suffix (a.size - i)) :
    a.size - consumedAbs a i t = t.remaining := by
  unfold consumedAbs
  have hle : t.remaining ≤ a.size - i := t.hle
  omega

/-! ## Refinement: the packed decoder equals the spec `decode` -/

/-- `decode` is insensitive to a length cast of its input: decoding a
length-cast `Bytes n` result yields the same values, with each `Suffix` field
length-cast along the same equality. (The `cast` is along `rfl` after `subst`, so
the body is definitionally transparent.) `[propext, Quot.sound]`-only. -/
theorem decode_cast {α : Type} (d : Codec α) {n m : Nat} (e : n = m) (s : Bytes n) :
    decode d (cast (congrArg Bytes e) s) =
      (decode d s).map (fun (x, t) => (x, cast (congrArg Suffix e) t)) := by
  subst e
  simp

/-- A length-cast `Suffix` has the same `remaining` field (the cast only moves
the `hle` bound, which is proof-irrelevant). **No axioms at all** (measured:
`#print axioms Codec.PackedCand`). -/
theorem Suffix_cast_remaining {n m : Nat} (e : n = m) (t : Suffix n) :
    (cast (congrArg Suffix e) t).remaining = t.remaining := by
  cases e
  rfl

/-- The consumed-count bridge composed with the `decode` genuine-suffix
invariant: for any decode result `(x, t) ∈ decode d (bdrop i (arrayToBytes a))`,
the `bdrop (consumedAbs a i t)` of the *whole* array is exactly `t.bytes`,
transported across `consumedAbs_remaining`. Proved by `bdrop_add` (drop
composition) + `decode_genuine_suffix` + `cast` cancellation. `[propext,
Quot.sound]`-only. -/
theorem bdrop_consumedAbs_eq {α : Type} (d : Codec α) (a : Array UInt8) (i : Nat) :
    ∀ (x : α) (t : Suffix (a.size - i)), (x, t) ∈ decode d (bdrop i (arrayToBytes a)) →
      bdrop (consumedAbs a i t) (arrayToBytes a) =
        cast (congrArg Bytes (consumedAbs_remaining a i t).symm) t.bytes := by
  intro x t hm
  have hg := decode_genuine_suffix d (bdrop i (arrayToBytes a)) x t hm
  have hb := bdrop_add (n := a.size) (i := i) (m := (a.size - i) - t.remaining) (s := arrayToBytes a)
  unfold consumedAbs
  rw [hb, ← hg, cast_cast]

/-- Transitivity of the consumed-count bridge across a length cast:
`consumedAbs a (consumedAbs a i t₁) (cast … t₂) = consumedAbs a i (Suffix.trans t₁ t₂)`.
This is the `seq`-case arithmetic that aligns the inner decoder's absolute cursor
with the composed `Suffix.trans`. `[propext, Quot.sound]`-only. -/
theorem consumedAbs_cast_trans (a : Array UInt8) (i : Nat) (t₁ : Suffix (a.size - i)) (t₂ : Suffix t₁.remaining) :
    consumedAbs a (consumedAbs a i t₁) (cast (congrArg Suffix (consumedAbs_remaining a i t₁).symm) t₂) =
    consumedAbs a i (Suffix.trans t₁ t₂) := by
  unfold consumedAbs
  rw [Suffix_cast_remaining]
  · simp only [Suffix.trans]
    have ht₁ : t₁.remaining ≤ a.size - i := t₁.hle
    have ht₂ : t₂.remaining ≤ t₁.remaining := t₂.hle
    omega
  · exact (consumedAbs_remaining a i t₁).symm

/-- The packed decoder equals the spec `decode`, up to the consumed-count
readback: `decodeArray d a i = (decode d (bdrop i (arrayToBytes a))).map
(fun (x, t) => (x, consumedAbs a i t))`. The `seq` case bridges the inner
`decodeArray d₂ a c₁` (over `bdrop c₁ (arrayToBytes a)`) with `decode d₂ t₁.bytes`
via `decode_cast` and the genuine-suffix/`bdrop_add` composition
(`bdrop_consumedAbs_eq`), with `consumedAbs_cast_trans` aligning the cursors.
`[propext, Quot.sound]`-only, zero `sorry`, and choice-free. -/
theorem decodeArray_eq {α : Type} (d : Codec α) (a : Array UInt8) (i : Nat) :
    decodeArray d a i = (decode d (bdrop i (arrayToBytes a))).map (fun (x, t) => (x, consumedAbs a i t)) := by
  induction d generalizing a i with
  | iso j d ih =>
      simp only [decodeArray, decode]
      rw [ih a i]
      rw [List.filterMap_map, List.map_filterMap]
      congr 1
      funext pr
      cases pr with
      | mk x t =>
          dsimp
          cases hj : j.apply x with
          | none => rfl
          | some y => rfl
  | seq d₁ d₂ ih₁ ih₂ =>
      simp only [decodeArray, decode]
      rw [ih₁ a i]
      rw [List.flatMap_map]
      rw [List.map_flatMap]
      simp only [List.map_flatMap]
      change (List.map (fun a_1 => List.flatMap (fun x => [((a_1.fst, x.fst), x.snd)]) (decodeArray d₂ a (consumedAbs a i a_1.snd))) (decode d₁ (bdrop i (arrayToBytes a)))).flatten =
             (List.map (fun a_1 => List.flatMap (fun a_2 => List.map (fun x => (x.fst, consumedAbs a i x.snd)) [((a_1.fst, a_2.fst), a_1.snd.trans a_2.snd)]) (decode d₂ a_1.snd.bytes)) (decode d₁ (bdrop i (arrayToBytes a)))).flatten
      congr 1
      apply List.map_inj_left.mpr
      intro pr hm
      cases pr with
      | mk x₁ t₁ =>
          dsimp
          rw [ih₂ a (consumedAbs a i t₁)]
          rw [List.flatMap_map]
          have hbd := bdrop_consumedAbs_eq d₁ a i x₁ t₁ hm
          rw [hbd]
          rw [decode_cast d₂ (e := (consumedAbs_remaining a i t₁).symm)]
          rw [List.flatMap_map]
          congr 1
          funext pr₂
          cases pr₂ with
          | mk y t₂ =>
              dsimp
              rw [consumedAbs_cast_trans a i t₁ t₂]
              rfl
  | alt d₁ d₂ ih₁ ih₂ =>
      simp only [decodeArray, decode]
      rw [ih₁ a i, ih₂ a i]
      rw [List.map_append]
  | empty => rfl
  | pure x₀ =>
      simp only [decodeArray, decode, List.map]
      congr
      exact (consumedAbs_id a i).symm
  | byte =>
      simp only [decodeArray, decode]
      by_cases h : i < a.size
      · have hn : (a.size - i) ≠ 0 := by omega
        simp [h, hn]
        constructor
        · dsimp [arrayToBytes, bdrop]
          congr 1
          omega
        · exact (consumedAbs_drop_one a i (bdrop i (arrayToBytes a)) h).symm
      · have hn : (a.size - i) = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_not_gt h)
        simp [h, hn]
  | satisfy p =>
      simp only [decodeArray, decode]
      by_cases h : i < a.size
      · have hn : (a.size - i) ≠ 0 := by omega
        by_cases hp : p (a[i])
        · have hp' : p ((bdrop i (arrayToBytes a)) ⟨0, Nat.pos_of_ne_zero hn⟩) = true := by
            dsimp [bdrop, arrayToBytes]
            simpa using hp
          simp [h, hn, hp, hp']
          constructor
          · dsimp [arrayToBytes, bdrop]
            congr 1
            omega
          · exact (consumedAbs_drop_one a i (bdrop i (arrayToBytes a)) h).symm
        · have hnp : p ((bdrop i (arrayToBytes a)) ⟨0, Nat.pos_of_ne_zero hn⟩) = false := by
            dsimp [bdrop, arrayToBytes]
            simpa using hp
          simp [h, hn, hp, hnp]
      · have hn : (a.size - i) = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_not_gt h)
        simp [h, hn]

/-- **A `ConsumesByte` decoder's packed candidate advances strictly**: at cursor
`k`, every `(x, c) ∈ decodeArray d a k` has `k < c`.

This is the cursor form of `ConsumesByte`, and it is the **well-foundedness fact**
a cursor-driven full-consumption search needs: the search recurses at the cursor a
candidate consumed, so without `k < c` the measure would not decrease. The spec
form of the same fact is the hypothesis of `decodeFullFast`'s `decreasing_by`;
here it is obtained through `decodeArray_eq` from `(x, t) ∈ decode d (bdrop i …)`.

`decodeArray` alone does **not** give it — `pure x` produces a candidate with
`c = k` (`decodeArray (pure 5) a 1 = [(5, 1)]`), which is why the search must be
run under `ConsumesByte` and not on a bare `Codec`.

`[propext, Quot.sound]`-only. -/
theorem decodeArray_consumes {α : Type} (d : Codec α) (h : ConsumesByte d)
    (a : Array UInt8) (k : Nat) :
    ∀ (x : α) (c : Nat), (x, c) ∈ decodeArray d a k → k < a.size → k < c := by
  intro x c hmem hk
  rw [decodeArray_eq] at hmem
  simp only [List.mem_map] at hmem
  obtain ⟨⟨y, t⟩, hmem', heq⟩ := hmem
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ heq
  show k < consumedAbs a k t
  unfold consumedAbs
  have hroot : t.remaining < a.size - k := h y (bdrop k (arrayToBytes a)) t hmem'
  have hk' : k ≤ a.size := Nat.le_of_lt hk
  omega

/-! ## The packed full-consumption decoder (`R5.1`, task 6.1b)

`decodeFullArray` below **commits to the head** candidate — it is the packed twin
of the defect 6.1a found and fixed in `decodeFullFast`, and its `head?` statement
makes that visible. `decodeArray_consumes` says a `ConsumesByte` decoder's packed
candidate advances strictly at a live cursor, which is the well-foundedness fact a
cursor-driven search needs; `decodeFullArrayFast`/`decodeFullArraySearch` are that
search, defined exactly as the proved `decodeFullFast`/`decodeFullFastSearch` pair,
with the `Suffix` plumbing replaced by the packed cursor. -/

/- **The packed cursor search**: the packed full-consumption decoder.
Mirrors `Codec.decodeFullFast`'s shape one-for-one — a cursor on the *remaining*
length, an accumulator, and a sibling search over `decodeArray`'s candidates —
with `Suffix`/`bdrop` replaced by the `Nat` consumed count `k`.

The recursion descends on `a.size - k`, so it compiles to a loop. The cursor bound
`hk : k ≤ a.size` is an **ordinary parameter** and not derived inside a `match` arm:
deriving it with `by omega` there was what made the unfolders leak
`Classical.choice` (see `decodeFullArrayFast_succ`), and an earlier session's
"thread `hk` as a parameter" advice was the right instinct recorded with the wrong
reason. `PackedCand`'s own `≤` field is what the search passes through, so the bound
never has to be invented. `[propext, Quot.sound]`-only, choice-free, zero `sorry`. -/
/-- A packed candidate **carrying its own strict-advance fact**. `decodeArray_consumes`
says a `ConsumesByte` decoder's candidate always advances the cursor, so the fact is
there for every candidate; putting it *in the type* is what lets the recursive call
read its cursor bound off a **named field** (`by omega` over `hkc : k < c` and
`hk : k < a.size`) instead of deriving it from a `ConsumesByte` application inside
the `match` arm, which is the spelling that keeps both `decreasing_by` and the
unfolders `[propext, Quot.sound]`-only (task 6.1b, plan item 1).

The third component is `≤` and not `<` because `pure x` yields a candidate with
`c = i`: `decodeArray_bounded_upper`'s `≤` is the honest bound and `<` is false. -/
abbrev PackedCand {α : Type} (d : Codec α) (a : Array UInt8) (k : Nat) :=
  { pr : α × Nat // pr ∈ decodeArray d a k ∧ k < pr.2 ∧ pr.2 ≤ a.size }

/-- The packed candidate list at cursor `k`, with the strict-advance fact attached.

**Built by `map`, not `filterMap`, and that is a measured 2.6× on this function**
(task 6.6). The previous body was
`(decodeArray d a k).attach.filterMap fun p => if hp : k < p.val.2 then if hq : …
` — two `dif`s per element, each re-deciding a proposition that
`decodeArray_consumes` and `decodeArray_bounded_upper` **always** make true under
`ConsumesByte`. Measured at `n` = 65536, one step per iteration: `packedCands` cost
**91 ns/step**, of which `.attach` alone was 25 and a plain `attach.map` was 35 —
i.e. the two `dif`s were ~56 of the 91. `packedCands` is rebuilt on **every** step of
the search and was the single largest term in the whole packed decode, so this is
the dominant per-step cost in the library.

The two facts the `dif`s re-derived are supplied once, from the cursor relation: at
`k < a.size` the attaching `map` discharges them from `decodeArray_consumes` and
`decodeArray_bounded_upper`. At `k = a.size` the cursor is at the end of the buffer
and `decodeArray` yields **no** candidate at all (`ConsumesByte` can never advance
past the end), so the empty list is the honest answer and no fact is needed.

**Why this is not `List.map` over the raw list:** the membership witness must
survive, which is what `.attach` is for. `attach.map` keeps it; a `map` over
`decodeArray d a k` would lose it. -/
def packedCands {α : Type} (d : Codec α) (h : ConsumesByte d)
    (a : Array UInt8) (k : Nat) (hk : k ≤ a.size) : List (PackedCand d a k) :=
  if hlt : k < a.size then
    (decodeArray d a k).attach.map fun p =>
      ⟨p.val, p.property,
       decodeArray_consumes d h a k p.val.1 p.val.2 p.property hlt,
       decodeArray_bounded_upper d a k p.val.2 p.val.1 hk p.property⟩
  else
    -- `k = a.size`: the cursor is exhausted, so there is nothing to try. Stated
    -- as `[]` rather than left to the `map`, because `decodeArray_consumes` (and
    -- hence the `PackedCand` construction) is only available at `k < a.size`.
    []

/-- `packedCands` is no longer than the raw candidate list. -/
theorem length_packedCands_le {α : Type} (d : Codec α) (h : ConsumesByte d)
    (a : Array UInt8) (k : Nat) (hk : k ≤ a.size) :
    (packedCands d h a k hk).length ≤ (decodeArray d a k).length := by
  unfold packedCands
  split
  · rw [List.length_map, List.length_attach]
    omega
  · exact Nat.zero_le _

mutual
def decodeFullArrayFast {α : Type} (d : Codec α) (h : ConsumesByte d)
    (a : Array UInt8) (k : Nat) (hk : k ≤ a.size) (acc : List α) : Option (List α) :=
  match _hm : a.size - k with
  | 0 => some acc.reverse
  | _ + 1 =>
    decodeFullArraySearch d h a k hk acc (packedCands d h a k hk)
termination_by (a.size - k, (packedCands d h a k hk).length + 1)

/-- The sibling search driving `decodeFullArrayFast`: **every** candidate of
`decodeArray d a k` is tried in order and the first fully-consuming one wins — the
same search as `decodeFullStep` and as `decodeFullFastSearch`, which is what makes
this decoder equal to the specification rather than to `head?`. Structural on the
candidate list. -/
def decodeFullArraySearch {α : Type} (d : Codec α) (h : ConsumesByte d)
    (a : Array UInt8) (k : Nat) (hk : k ≤ a.size) (acc : List α)
    (cands : List (PackedCand d a k)) : Option (List α) :=
  match cands with
  | [] => none
  | ⟨(x, c), _hmem, _hkc, hlt⟩ :: rest =>
    match decodeFullArrayFast d h a c hlt (x :: acc) with
    | none => decodeFullArraySearch d h a k hk acc rest
    | some xs => some xs
termination_by (a.size - k, cands.length)
decreasing_by
  · -- search -> fast: the candidate consumed a byte and stayed in bounds.
    simp_wf
    omega
  · -- search -> search: the candidate list strictly shrinks.
    simp_wf
    exact Prod.Lex.right _ (Nat.le_refl _)
end

/-- `decodeFullArrayFast`'s recursion equation at a known-**successor** cursor: the
body is `match _hm : a.size - k with …`, so the named equation blocks ι-reduction and
`rw [decodeFullArrayFast.eq_def]` alone leaves a stuck `match`; the `dsimp only`
between the two rewrites is load-bearing, exactly as for `decodeFullFast_succ`.

**Correction to an earlier session's record (do not re-derive).** This used to be
proved by `split`, and that spelling **leaked `Classical.choice`** — as did the
`(by omega)` proof term the definition used to carry in its successor arm, because
`omega` closed a goal in a context whose only witness was the `match`'s own equation.
`#print axioms` on both unfolders reported `[propext, Classical.choice,
Quot.sound]` while `tasks.md` claimed `[propext, Quot.sound]`. The leak is gone:
`decodeFullArrayFast`/`decodeFullArraySearch` now take the cursor bound `hk : k ≤
a.size` as an **ordinary parameter** (the candidate already carries its own `≤`
field, so the search passes it straight through) instead of manufacturing it with
`by omega` inside a `match` arm, and the unfolders use 6.1a's
`conv`/`dsimp only`/`rw` recipe, which does transfer once the arm is proof-free. -/
theorem decodeFullArrayFast_succ {α : Type} (d : Codec α) (h : ConsumesByte d)
    (a : Array UInt8) (k : Nat) (hk : k ≤ a.size) (acc : List α) (j : Nat)
    (hj : a.size - k = j + 1) :
    decodeFullArrayFast d h a k hk acc =
      decodeFullArraySearch d h a k hk acc (packedCands d h a k hk) := by
  conv => lhs; rw [decodeFullArrayFast.eq_def]; dsimp only; rw [hj]

/-- `decodeFullArrayFast`'s recursion equation at a known-**zero** cursor: the input
is exhausted, so the accumulator is the answer. Note this base case is reached by
`a.size - k = 0` (end of input), **not** by an empty candidate list — the packed
mirror of `decodeFullFast_zero`. -/
theorem decodeFullArrayFast_zero {α : Type} (d : Codec α) (h : ConsumesByte d)
    (a : Array UInt8) (k : Nat) (hk : k ≤ a.size) (acc : List α) (hk0 : a.size - k = 0) :
    decodeFullArrayFast d h a k hk acc = some acc.reverse := by
  conv => lhs; rw [decodeFullArrayFast.eq_def]; dsimp only; rw [hk0]

/-- **Membership in `packedCands` is membership in `decodeArray`, plus the two
cursor facts.** This is the bridge between the candidate list the search walks and
the raw `decodeArray` results the specification-side lemmas talk about. -/
theorem mem_packedCands {α : Type} (d : Codec α) (h : ConsumesByte d)
    (a : Array UInt8) (k : Nat) (pr : α × Nat) (hpr : pr ∈ decodeArray d a k)
    (hk : k < a.size) :
    ∃ (hkc : k < pr.2) (hlt : pr.2 ≤ a.size),
      ⟨pr, hpr, hkc, hlt⟩ ∈ packedCands d h a k (Nat.le_of_lt hk) := by
  have hkc : k < pr.2 := decodeArray_consumes d h a k pr.1 pr.2 hpr hk
  have hlt : pr.2 ≤ a.size :=
    decodeArray_bounded_upper d a k pr.2 pr.1 (Nat.le_of_lt hk) hpr
  refine ⟨hkc, hlt, ?_⟩
  unfold packedCands
  rw [dite_eq_left hk, List.mem_map]
  refine ⟨⟨pr, hpr⟩, List.mem_attach _ _, ?_⟩
  rfl

/-- **Every packed candidate comes from `decodeArray`.** The search never invents a
candidate: its membership witness is exactly a `decodeArray` membership. -/
theorem packedCands_mem {α : Type} (d : Codec α) (_h : ConsumesByte d)
    (a : Array UInt8) (k : Nat) (c : PackedCand d a k) : c.val ∈ decodeArray d a k :=
  c.property.1

/-- **The search never invents a candidate, part two**: every packed candidate's
cursor strictly advanced and stayed in bounds. -/
theorem packedCands_consumes {α : Type} (d : Codec α) (_h : ConsumesByte d)
    (a : Array UInt8) (k : Nat) (c : PackedCand d a k) :
    k < c.val.2 ∧ c.val.2 ≤ a.size :=
  ⟨c.property.2.1, c.property.2.2⟩

/-- **The search's step equation over a `cons`**: the search tries the candidate's
re-rooted recursion at the advanced cursor and takes the first full consumption, or
continues with the rest of the list. The packed mirror of `decodeFullStep_cons`.

The proof is a single `conv` on the LHS that rewrites the definition's own
equation: on Lean **4.35.0** that closes the goal outright.

Until the 4.35.0 bump this needed a `match`-in-`match` recipe after the `conv`
(`simp only` to force the inner `match`, `split` for the outer one, then
`injection` on the discriminant equation to re-align `split`'s binders with the
stated ones — `tasks.md` 6.1a trap 2). 4.35.0 made the `rw` aggressive enough
that it discharges the whole goal, so that tail became dead and was removed.
While both toolchains were supported it was wrapped in `first | (tail) | skip`;
the ecosystem is now pinned to 4.35.0, so the guard is gone too.

**This is not vacuous, and the check for that is cheap.** A one-line proof can
easily mean the goal closed for the wrong reason, so mutating an arm of the
statement (`none => decodeFullArraySearch … rest` → `none => some []`) was
verified to break it with `unsolved goals`. The law still says what it said. -/
theorem decodeFullArraySearch_cons {α : Type} (d : Codec α) (h : ConsumesByte d)
    (a : Array UInt8) (k : Nat) (hk : k ≤ a.size) (acc : List α)
    (x : α) (c : Nat) (hmem : (x, c) ∈ decodeArray d a k ∧ k < c ∧ c ≤ a.size)
    (rest : List (PackedCand d a k)) :
    decodeFullArraySearch d h a k hk acc (⟨(x, c), hmem⟩ :: rest) =
      (match decodeFullArrayFast d h a c hmem.2.2 (x :: acc) with
       | none => decodeFullArraySearch d h a k hk acc rest
       | some xs => some xs) := by
  conv => lhs; rw [decodeFullArraySearch.eq_def]

/-- **The search over the empty candidate list is `none`** — the packed mirror of
`decodeFullStep_nil`. Note this case is *unreachable* at a live cursor under
`ConsumesByte` (`decodeArray_consumes` guarantees every candidate advances), and it
is reached only at the end of the buffer, where `decodeFullArrayFast`'s base case
already answers `some acc.reverse`. Stated because the search congruence needs it. -/
theorem decodeFullArraySearch_nil {α : Type} (d : Codec α) (h : ConsumesByte d)
    (a : Array UInt8) (k : Nat) (hk : k ≤ a.size) (acc : List α) :
    decodeFullArraySearch d h a k hk acc ([] : List (PackedCand d a k)) = none := by
  conv => lhs; rw [decodeFullArraySearch.eq_def]

/-- **A `ConsumesByte` step strictly advances the packed cursor.** The array-cursor
form of `ConsumesByte`, and the fact the bridge's strong induction needs at every
step. The spec-side twin of `decodeArray_consumes` (which states it for
`decodeArray`'s results); this states it for `decode`'s, at the array root. -/
theorem consume_lt {α : Type} (d : Codec α) (h : ConsumesByte d) (a : Array UInt8)
    (k : Nat) (hk : k < a.size) (x : α) (t : Suffix (a.size - k))
    (hm : (x, t) ∈ decode d (bdrop k (arrayToBytes a))) : k < consumedAbs a k t := by
  unfold consumedAbs
  have := h x (bdrop k (arrayToBytes a)) t hm
  omega

/-! ## The candidate bijection (task 6.1b, step A)

`packedCands` and the specification's `(decode d (bdrop k (arrayToBytes a))).attach`
are **the same list**, element for element, with the packed element `⟨(x, c), …⟩`
standing for the spec element `⟨(x, t), …⟩` at `c = consumedAbs a k t`. This is the
new mathematics 6.1b was blocked on: the bridge's successor case hands its step
hypothesis to the search congruence, and that hypothesis is stated over *spec*
candidates while the fast decoder walks *packed* ones. -/

/-- **`filterMap` with a total predicate is `map`.** The generic form of
"`packedCands`' two `dif`s always take the `some` branch under `ConsumesByte`".
Stated for a general list and a general `g` because the proof is pure list induction
and has nothing to do with `Codec` — the caller supplies the pointwise `some` fact.
**Axiom-free** (measured: `#print axioms` reports no axioms). -/
theorem filterMap_eq_map_of_forall {β γ : Type} (l : List β) (f : β → Option γ)
    (g : β → γ) (h : ∀ b ∈ l, f b = some (g b)) :
    l.filterMap f = l.map g := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    rw [List.filterMap_cons, h hd (List.mem_cons_self ..),
        ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]
    rfl

/-- **Membership readback**: a packed result `(x, c)` at cursor `k` is exactly a spec
`decode` result `(x, t)` at the same cursor, with `c` the packed readback of `t`.
This is `decodeArray_eq` read as a *membership* equivalence rather than a list
equality, which is the form every candidate argument below wants — and the form that
avoids rewriting under `.attach` (the dependent-motive trap).

Needs no `ConsumesByte`: it is a fact about the two decoders agreeing, not about
advance. `[propext, Quot.sound]`-only. -/
theorem mem_decodeArray_iff {α : Type} (d : Codec α) (a : Array UInt8) (k : Nat) :
    ∀ (x : α) (c : Nat),
      (x, c) ∈ decodeArray d a k ↔
        ∃ t : Suffix (a.size - k),
          (x, t) ∈ decode d (bdrop k (arrayToBytes a)) ∧ c = consumedAbs a k t := by
  intro x c
  rw [decodeArray_eq]
  simp only [List.mem_map]
  constructor
  · rintro ⟨⟨y, t⟩, hm, heq⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ heq
    exact ⟨t, hm, rfl⟩
  · rintro ⟨t, hm, rfl⟩
    exact ⟨(x, t), hm, rfl⟩

/-- **`packedCands` is the attach list, mapped.** Under `ConsumesByte` at a live
cursor both `dif` guards in `packedCands` are always satisfied (`decodeArray_consumes`
gives `k < pr.2`, `decodeArray_bounded_upper` gives `pr.2 ≤ a.size`), so the
`filterMap` never drops an element and is a `List.map`. This is the lemma that turns
`packedCands` into something `List.mem_map` can open — the earlier plan's
"unfold-and-prove-the-`dif`s" step, and it is what makes the `attach`/`filterMap`
`rw` the ledger warned against unnecessary. `[propext, Quot.sound]`-only. -/
theorem packedCands_eq_attach {α : Type} (d : Codec α) (h : ConsumesByte d)
    (a : Array UInt8) (k : Nat) (hk : k < a.size) :
    packedCands d h a k (Nat.le_of_lt hk) =
      (decodeArray d a k).attach.map
        (fun p => (⟨p.val, p.property,
          decodeArray_consumes d h a k p.val.1 p.val.2 p.property hk,
          decodeArray_bounded_upper d a k p.val.2 p.val.1 (Nat.le_of_lt hk) p.property⟩ :
          PackedCand d a k)) := by
  unfold packedCands
  rw [dite_eq_left hk]

/-- **The two candidate lists have the same length.** A corollary of
`packedCands_eq_attach` and `decodeArray_eq`: nothing is dropped and nothing is
invented, so the packed search walks exactly as many candidates as the spec
backtracking step does. `[propext, Quot.sound]`-only. -/
theorem packedCands_length_eq {α : Type} (d : Codec α) (h : ConsumesByte d)
    (a : Array UInt8) (k : Nat) (hk : k < a.size) :
    (packedCands d h a k (Nat.le_of_lt hk)).length =
      (decode d (bdrop k (arrayToBytes a))).length := by
  rw [packedCands_eq_attach d h a k hk, List.length_map, List.length_attach,
      decodeArray_eq]
  simp

/-- **The candidate correspondence, forward — Step A's target.** For every spec
candidate `(x, t)` at cursor `k`, the packed candidate `(x, consumedAbs a k t)` — with
all three cursor facts attached — is a member of `packedCands d h a k`.

This is the direction the bridge's successor case needs: given a spec candidate to
feed the search congruence's step hypothesis, produce the packed candidate the fast
decoder actually walks, and know they name the **same** `(value, remainder)`.
`[propext, Quot.sound]`-only. -/
theorem packedCand_of_mem {α : Type} (d : Codec α) (h : ConsumesByte d)
    (a : Array UInt8) (k : Nat) (hk : k < a.size) (x : α)
    (t : Suffix (a.size - k)) (hm : (x, t) ∈ decode d (bdrop k (arrayToBytes a))) :
    (⟨(x, consumedAbs a k t),
        (mem_decodeArray_iff d a k x (consumedAbs a k t)).mpr ⟨t, hm, rfl⟩,
        consume_lt d h a k hk x t hm,
        by
          have := t.hle
          unfold consumedAbs
          omega⟩ : PackedCand d a k) ∈ packedCands d h a k (Nat.le_of_lt hk) := by
  rw [packedCands_eq_attach d h a k hk, List.mem_map]
  exact ⟨⟨(x, consumedAbs a k t),
    (mem_decodeArray_iff d a k x (consumedAbs a k t)).mpr ⟨t, hm, rfl⟩⟩,
    List.mem_attach _ _, rfl⟩

/-- **The packed `/` spec candidate bijection, as an equivalence.** Both directions
at once: a `PackedCand` at cursor `k` is a spec candidate at the same cursor, and
vice versa, with the `consumedAbs`/`Suffix` correspondence between them. The second
direction is `packedCand_of_mem`; the first is `mem_decodeArray_iff` plus the
`PackedCand` invariant. Used by the bridge to move its step hypothesis across.
`[propext, Quot.sound]`-only. -/
theorem packedCand_iff {α : Type} (d : Codec α) (_h : ConsumesByte d)
    (a : Array UInt8) (k : Nat) (_hk : k < a.size) (c : PackedCand d a k) :
    ∃ t : Suffix (a.size - k),
      (c.val.1, t) ∈ decode d (bdrop k (arrayToBytes a)) ∧ c.val.2 = consumedAbs a k t := by
  obtain ⟨⟨x, c'⟩, hmem, -, -⟩ := c
  exact (mem_decodeArray_iff d a k x c').mp hmem

/-! ## The bridge: the packed decoder equals the specification (`R5.1`, task 6.1b)

`array_bridge` is the packed twin of `cursor_bridge` and closes 6.1b's gate: it proves
`decodeFullArrayRoot = decodeFull`, so the packed cursor decoder is the
specification's decoder rather than a second, faster-guessed one.

The route is the one `tasks.md` 6.1b's plan lays out (Steps A–D), with one structural
correction recorded at each step where the plan was wrong:

* **Step A**, the candidate bijection, is `packedCands`/`decode` correspondence —
  already landed above (`packedCand_of_mem`, `packedCands_eq_attach`, …), together
  with the two `getElem?` lemmas below. The plan's *route* to it (rewrite under
  `.attach`) does not work — the dependent motive blocks it — so the correspondence is
  stated positionally instead, which is both provable and exactly what the step
  hypothesis needs.
* **Steps B–C** are `decodeFullStepPacked` + `stepPacked_eq_step` + `CandAligned`: the
  packed search is a packed-candidate recursion, and under an alignment it agrees with
  the spec `decodeFullStep`.
* **Step D** is `decodeFullArrayRoot_eq`, `array_bridge` at `K := a.size`, `k := 0`.

**The one place the plan's arithmetic was wrong.** 6.1b's plan said the strong
induction's measure must be `a.size - k ≤ K`. It must be `a.size - k = K`: the IH is
consumed at the *child* cursor, so it needs `a.size - c < K`, which `≤` does not give
at `K = a.size - k`. With `=` the child's measure is `t.remaining`, strictly smaller,
and `ih` applies directly — the same shape `cursor_bridge` uses.

**The other correction: the child cursor can reach the end of the buffer.**
`consumedAbs a k t` can equal `a.size` (a candidate consuming the last byte), where
`array_bridge`'s own cursor premise `k < a.size` is false and no IH exists. That
branch is not a gap: the guard `rcases Nat.lt_or_ge` splits it off and the fast
decoder's base case (`decodeFullArrayFast_zero`) plus `decodeFull_at_zero` close it. -/

/-- `getElem?_probe`-shaped: every result of the packed decoder at index `i` is the
spec result there read back through `consumedAbs`. This is `decodeArray_eq` read
positionally — the form the `attach` correspondence needs, since rewriting *under*
`.attach` dies on the dependent motive. `[propext, Quot.sound]`-only. -/
theorem decodeArray_getElem?_spec {α : Type} (d : Codec α) (a : Array UInt8) (k i : Nat)
    (pr : α × Nat) (hpr : (decodeArray d a k)[i]? = some pr) :
    ∃ t : Suffix (a.size - k),
      (decode d (bdrop k (arrayToBytes a)))[i]? = some (pr.1, t) ∧ pr.2 = consumedAbs a k t := by
  rw [decodeArray_eq, List.getElem?_map] at hpr
  cases hd : (decode d (bdrop k (arrayToBytes a)))[i]? with
  | none => rw [hd] at hpr; simp at hpr
  | some q =>
      rw [hd] at hpr
      simp only [Option.map, Option.some.injEq] at hpr
      subst hpr
      exact ⟨q.2, rfl, rfl⟩

/-- **The attach lists correspond element for element.** At index `i`, the packed
candidate and the spec candidate name the same value, with the packed cursor the
readback of the spec suffix — obtained by opening both `attach` lists through
`List.getElem?_attach` and reading the underlying lists positionally. This is the
positional form of the candidate bijection 6.1b's Step A asked for.
`[propext, Quot.sound]`-only. -/
theorem attach_getElem?_corr {α : Type} (d : Codec α) (a : Array UInt8) (k i : Nat) :
    ∀ (c : { pr : α × Nat // pr ∈ decodeArray d a k })
      (s : { pr : α × Suffix (a.size - k) // pr ∈ decode d (bdrop k (arrayToBytes a)) }),
      (decodeArray d a k).attach[i]? = some c →
      (decode d (bdrop k (arrayToBytes a))).attach[i]? = some s →
      c.val.1 = s.val.1 ∧ c.val.2 = consumedAbs a k s.val.2 := by
  intro c s hc hs
  rw [List.getElem?_attach] at hc
  rw [List.getElem?_attach] at hs
  cases hd : (decodeArray d a k)[i]? with
  | none =>
      simp only [hd] at hc
      exact absurd hc (by simp)
  | some pr =>
      simp only [hd] at hc
      have hc' : c = ⟨pr, List.mem_of_getElem? hd⟩ := (Option.some.inj hc).symm
      subst hc'
      obtain ⟨t, ht, hce⟩ := decodeArray_getElem?_spec d a k i pr hd
      cases hd2 : (decode d (bdrop k (arrayToBytes a)))[i]? with
      | none => rw [ht] at hd2; exact absurd hd2 (by simp)
      | some q =>
          simp only [hd2] at hs
          have hs' : s = ⟨q, List.mem_of_getElem? hd2⟩ := (Option.some.inj hs).symm
          subst hs'
          rw [ht] at hd2
          have hq : q = (pr.1, t) := (Option.some.inj hd2).symm
          subst hq
          exact ⟨rfl, hce⟩

variable {α : Type} (d : Codec α) (h : ConsumesByte d) (a : Array UInt8)

/-- The packed mirror of `decodeFullStep`: try each packed candidate in order at its own
cursor and take the first full consumption. This is the *specification* of the packed
search, stated over `PackedCand`s so it typechecks against the search's own recursion;
`stepPacked_eq_step` then relates it to the spec `decodeFullStep`. -/
def decodeFullStepPacked (k : Nat) (acc : List α) : List (PackedCand d a k) → Option (List α)
  | [] => none
  | c :: rest =>
      match decodeFullArrayFast d h a c.val.2 c.property.2.2 (c.val.1 :: acc) with
      | none => decodeFullStepPacked k acc rest
      | some xs => some xs

/-- **The search is exactly its packed step function.** `decodeFullStepPacked` is the
packed mirror of `decodeFullStep` stated over `PackedCand`s; the search's own body is
already that recursion, so this is list induction. The two-step route exists because
the bridge cannot relate the packed search to the *spec* step directly — the two walk
differently typed candidate lists — and this makes the packed search a fixed object
whose agreement with the spec step is then a separate, self-contained lemma
(`stepPacked_eq_step`). `[propext, Quot.sound]`-only. -/
theorem decodeFullArraySearch_eq_stepPacked (k : Nat) (hk : k ≤ a.size) (acc : List α) :
    ∀ (cs : List (PackedCand d a k)),
      decodeFullArraySearch d h a k hk acc cs = decodeFullStepPacked d h a k acc cs := by
  intro cs
  induction cs with
  | nil => rw [decodeFullArraySearch.eq_def]; rfl
  | cons hd tl ih =>
      obtain ⟨⟨x, c⟩, hmem, hkc, hlt⟩ := hd
      rw [decodeFullArraySearch_cons d h a k hk acc x c ⟨hmem, hkc, hlt⟩ tl,
          decodeFullStepPacked]
      cases decodeFullArrayFast d h a c hlt (x :: acc) with
      | none => simp only; exact ih
      | some xs => rfl

/-- **Two candidate lists, aligned position by position.** Same length, and at every
index the packed element and the spec element name the same value, with the packed
cursor the packed readback of the spec suffix. This is the invariant that lets
`decodeFullStepPacked` and `decodeFullStep` be compared: it is what
`packedCands_aligned` discharges for the lists the decoder actually walks. -/
def CandAligned (k : Nat)
    (cs : List (PackedCand d a k))
    (ss : List { pr : α × Suffix (a.size - k) // pr ∈ decode d (bdrop k (arrayToBytes a)) }) : Prop :=
  cs.length = ss.length ∧
  ∀ (i : Nat) (c : PackedCand d a k)
    (s : { pr : α × Suffix (a.size - k) // pr ∈ decode d (bdrop k (arrayToBytes a)) }),
    cs[i]? = some c → ss[i]? = some s →
      c.val.1 = s.val.1 ∧ c.val.2 = consumedAbs a k s.val.2

/-- The length component of an alignment. -/
theorem CandAligned_fst {k : Nat} {cs : List (PackedCand d a k)}
    {ss : List { pr : α × Suffix (a.size - k) // pr ∈ decode d (bdrop k (arrayToBytes a)) }}
    (hal : CandAligned d a k cs ss) : cs.length = ss.length := hal.1

/-- The pointwise component of an alignment, at an index. -/
theorem CandAligned_at {k : Nat} {cs : List (PackedCand d a k)}
    {ss : List { pr : α × Suffix (a.size - k) // pr ∈ decode d (bdrop k (arrayToBytes a)) }}
    (hal : CandAligned d a k cs ss) (i : Nat) (c : PackedCand d a k)
    (s : { pr : α × Suffix (a.size - k) // pr ∈ decode d (bdrop k (arrayToBytes a)) })
    (hc : cs[i]? = some c) (hs : ss[i]? = some s) :
    c.val.1 = s.val.1 ∧ c.val.2 = consumedAbs a k s.val.2 := hal.2 i c s hc hs

/-- Alignment is preserved by taking both tails: the correspondence shifts by one. -/
theorem CandAligned_tail {k : Nat} {cs : List (PackedCand d a k)}
    {ss : List { pr : α × Suffix (a.size - k) // pr ∈ decode d (bdrop k (arrayToBytes a)) }}
    (hal : CandAligned d a k cs ss) : CandAligned d a k cs.tail ss.tail := by
  obtain ⟨hlen, hpt⟩ := hal
  refine ⟨by simp [List.length_tail, hlen], ?_⟩
  intro i c s hc hs
  have hc' : cs[i + 1]? = some c := by rw [← List.getElem?_tail]; exact hc
  have hs' : ss[i + 1]? = some s := by rw [← List.getElem?_tail]; exact hs
  exact hpt (i + 1) c s hc' hs'


/-- **The search/step agreement**: under an alignment, the packed step function over
`cs` equals the spec `decodeFullStep` over `ss`, with the accumulator reversed on.

This is the packed mirror of `decodeFullFastSearch_eq` and the reason 6.1b needed the
candidate bijection: the step hypothesis is stated over **spec** candidates (that is
what `decodeFullStep` consumes), while the recursion walks **packed** ones, and the
alignment is what transports one into the other. Follows `decodeFullFastSearch_eq`'s
shape — induction on the candidate list, `decodeFullStep_cons` on a `cons`,
`reverse_cons_append` for the accumulator — with the alignment supplying the
value/cursor identification at each head. `[propext, Quot.sound]`-only. -/
theorem stepPacked_eq_step {k : Nat} (hk : k ≤ a.size) (acc : List α) :
    ∀ (cs : List (PackedCand d a k))
      (ss : List { pr : α × Suffix (a.size - k) // pr ∈ decode d (bdrop k (arrayToBytes a)) }),
      CandAligned d a k cs ss →
      (∀ (x : α) (t : Suffix (a.size - k))
          (_hmem : (x, t) ∈ decode d (bdrop k (arrayToBytes a)))
          (hbd : consumedAbs a k t ≤ a.size),
          decodeFullArrayFast d h a (consumedAbs a k t) hbd (x :: acc) =
            (decodeFull d h t.remaining t.bytes).map (fun tail => (x :: acc).reverse ++ tail)) →
      decodeFullStepPacked d h a k acc cs =
        (decodeFullStep d h (bdrop k (arrayToBytes a)) (fun m s' _ => decodeFull d h m s') ss).map
          (fun tail => acc.reverse ++ tail) := by
  intro cs
  induction cs with
  | nil =>
      intro ss hal hstep
      obtain ⟨hlen, _⟩ := hal
      have hss : ss = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen.symm)
      subst hss
      rw [decodeFullStepPacked, decodeFullStep.eq_def]
      simp only [Option.map_none]
  | cons hd tl ih =>
      intro ss hal hstep
      obtain ⟨hlen, hpt⟩ := hal
      cases ss with
      | nil => simp at hlen
      | cons shd stl =>
          obtain ⟨⟨y, t⟩, hmem'⟩ := shd
          obtain ⟨⟨x, c⟩, hmem, hkc, hlt⟩ := hd
          have e0 := hpt 0 ⟨(x, c), hmem, hkc, hlt⟩ ⟨(y, t), hmem'⟩
            (List.getElem?_cons_zero) (List.getElem?_cons_zero)
          obtain ⟨hxy, hct0⟩ := e0
          have hct : c = consumedAbs a k t := hct0
          subst hxy
          -- `hct : c = consumedAbs a k t`, so the packed decoder's child call is
          -- already at `consumedAbs a k t`; only the bound proof needs carrying.
          have hcle : consumedAbs a k t ≤ a.size := by
            have hh := t.hle
            unfold consumedAbs
            omega
          have hfast : decodeFullArrayFast d h a c hlt (x :: acc)
              = decodeFullArrayFast d h a (consumedAbs a k t) hcle (x :: acc) := by
            cases hct
            rfl
          rw [decodeFullStepPacked]
          simp only
          rw [hfast]
          rw [decodeFullStep_cons d h (bdrop k (arrayToBytes a))
                (fun m s' _ => decodeFull d h m s') x t hmem' stl]
          rw [hstep x t hmem' hcle]
          have htail : CandAligned d a k tl stl := by
            refine ⟨by simpa using hlen, ?_⟩
            intro i2 c2 s2 hc2 hs2
            have hc2' : (⟨(x, c), hmem, hkc, hlt⟩ :: tl)[i2 + 1]? = some c2 := by
              rw [List.getElem?_cons_succ]; exact hc2
            have hs2' : (⟨(x, t), hmem'⟩ :: stl)[i2 + 1]? = some s2 := by
              rw [List.getElem?_cons_succ]; exact hs2
            exact hpt (i2 + 1) c2 s2 hc2' hs2'
          cases hd' : decodeFull d h t.remaining t.bytes with
          | none =>
              simp only [Option.map_none]
              exact ih stl htail hstep
          | some xs =>
              simp only [Option.map, Option.some.injEq]
              rw [reverse_cons_append]

/-- **The real lists are aligned.** `packedCands` at a live cursor lines up with the
spec `(decode …).attach` list: same length (`packedCands_length_eq`), and at each
index the packed candidate is the spec candidate's readback. Proved through the
`getElem?` correspondence, which is why no `attach` rewrite is needed.
`[propext, Quot.sound]`-only. -/
theorem packedCands_aligned {k : Nat} (hk : k < a.size) :
    CandAligned d a k (packedCands d h a k (Nat.le_of_lt hk))
      (decode d (bdrop k (arrayToBytes a))).attach := by
  refine ⟨by rw [List.length_attach, packedCands_length_eq d h a k hk], ?_⟩
  intro i c s hc hs
  rw [packedCands_eq_attach d h a k hk, List.getElem?_map] at hc
  -- `hc` now reads `Option.map f (decodeArray…attach[i]?) = some c`; open the option.
  cases hg : (decodeArray d a k).attach[i]? with
  | none => rw [hg] at hc; simp at hc
  | some c0 =>
      rw [hg] at hc
      simp only [Option.map, Option.some.injEq] at hc
      subst hc
      exact attach_getElem?_corr d a k i c0 s hg hs

/-- `decodeFull` is invariant under a `Bytes` length cast. `rfl` after `subst`. -/
theorem decodeFull_cast {α : Type} (d : Codec α) (h : ConsumesByte d) {n m : Nat}
    (e : n = m) (s : Bytes n) :
    decodeFull d h n s = decodeFull d h m (cast (congrArg Bytes e) s) := by
  subst e; rfl

/-- **The array bridge (task 6.1b's target).** At every live cursor `k`, the packed
fast decoder equals the specification at `bdrop k (arrayToBytes a)`, accumulator
reversed on — together with its search congruence, for the same reason
`cursor_bridge` carries both: the search's step calls the decoder at an advanced
cursor, so neither half is provable alone.

Measure: `a.size - k ≤ K` (**not** `= K`) — the recursive calls sit at the child
cursor, so the IH is consumed at a smaller remaining length. -/
theorem array_bridge {α : Type} (d : Codec α) (h : ConsumesByte d) (a : Array UInt8) :
    ∀ K (k : Nat) (hk : k < a.size), a.size - k = K →
      (∀ (acc : List α),
        decodeFullArrayFast d h a k (Nat.le_of_lt hk) acc
          = (decodeFull d h (a.size - k) (bdrop k (arrayToBytes a))).map
              (fun tail => acc.reverse ++ tail)) ∧
      (∀ (acc : List α),
        decodeFullArraySearch d h a k (Nat.le_of_lt hk) acc (packedCands d h a k (Nat.le_of_lt hk))
          = (decodeFullStep d h (bdrop k (arrayToBytes a))
              (fun m s' _ => decodeFull d h m s')
              (decode d (bdrop k (arrayToBytes a))).attach).map
              (fun tail => acc.reverse ++ tail)) := by
  intro K
  induction K using Nat.strongRecOn with
  | ind K ih =>
  intro k hk hK
  rcases Nat.eq_zero_or_pos (a.size - k) with hzero | hpos
  · -- vacuous: `a.size - k = 0` means `a.size ≤ k`, contradicting `hk`
    exact absurd hzero (by omega)
  · obtain ⟨j, hj⟩ : ∃ j, a.size - k = j + 1 := ⟨a.size - k - 1, by omega⟩
    have hrem : a.size - k = j + 1 := hj
    constructor
    · intro acc
      rw [decodeFullArrayFast_succ d h a k (Nat.le_of_lt hk) acc j hj,
          decodeFull_succ d h (a.size - k) j hj (bdrop k (arrayToBytes a))]
      rw [decodeFullArraySearch_eq_stepPacked d h a k (Nat.le_of_lt hk) acc (packedCands d h a k (Nat.le_of_lt hk))]
      refine stepPacked_eq_step d h a (Nat.le_of_lt hk) acc (packedCands d h a k (Nat.le_of_lt hk))
        (decode d (bdrop k (arrayToBytes a))).attach (packedCands_aligned d h a hk) ?_
      intro x t hmem
      have hlt : k < consumedAbs a k t := consume_lt d h a k hk x t hmem
      have hrem2 : a.size - consumedAbs a k t = t.remaining := consumedAbs_remaining a k t
      have hremk : a.size - k = j + 1 := hrem
      have hleT : t.remaining ≤ a.size - k := t.hle
      have hcle : consumedAbs a k t ≤ a.size := by
        have h := t.hle
        unfold consumedAbs
        omega
      have hsmall : a.size - consumedAbs a k t < a.size - k :=
        Nat.sub_lt_sub_left hk hlt
      have hmeas : a.size - consumedAbs a k t < K := by omega
      intro hbd
      rcases Nat.lt_or_ge (consumedAbs a k t) a.size with hend | hend
      · -- child cursor still inside the buffer: the IH applies
        have hchild := (ih (a.size - consumedAbs a k t) hmeas (consumedAbs a k t)
          (by omega) rfl).1 (x :: acc)
        rw [hchild]
        -- the child's root is exactly `t.bytes`
        rw [bdrop_consumedAbs_eq d a k x t hmem]
        show (Option.map (fun tail => (x :: acc).reverse ++ tail)
              (decodeFull d h (a.size - consumedAbs a k t)
                (cast (congrArg Bytes (consumedAbs_remaining a k t).symm) t.bytes))) = _
        rw [decodeFull_cast d h (consumedAbs_remaining a k t).symm t.bytes]
      · -- child cursor is the end of the buffer (`consumedAbs = a.size`): the fast
        -- decoder answers from its base case and the spec from `decodeFull_at_zero`.
        have heq : consumedAbs a k t = a.size := by omega
        have hz : a.size - consumedAbs a k t = 0 := by omega
        have hrz : t.remaining = 0 := by
          rw [← hrem2]; exact hz
        rw [decodeFullArrayFast_zero d h a (consumedAbs a k t) hbd (x :: acc) hz]
        rw [decodeFull_at_zero d h t.remaining t.bytes hrz]
        simp only [Option.map, List.append_nil]
    · intro acc
      rw [decodeFullArraySearch_eq_stepPacked d h a k (Nat.le_of_lt hk) acc (packedCands d h a k (Nat.le_of_lt hk))]
      refine stepPacked_eq_step d h a (Nat.le_of_lt hk) acc (packedCands d h a k (Nat.le_of_lt hk))
        (decode d (bdrop k (arrayToBytes a))).attach ?_ ?_
      · -- alignment of the real lists
        exact packedCands_aligned d h a hk
      · -- the same step hypothesis as the fast half
        intro x t hmem hbd
        have hlt : k < consumedAbs a k t := consume_lt d h a k hk x t hmem
        have hrem2 : a.size - consumedAbs a k t = t.remaining := consumedAbs_remaining a k t
        have hremk : a.size - k = j + 1 := hrem
        have hcle : consumedAbs a k t ≤ a.size := by
          have h := t.hle
          unfold consumedAbs
          omega
        have hsmall : a.size - consumedAbs a k t < a.size - k := Nat.sub_lt_sub_left hk hlt
        have hmeas : a.size - consumedAbs a k t < K := by omega
        rcases Nat.lt_or_ge (consumedAbs a k t) a.size with hend | hend
        · have hchild := (ih (a.size - consumedAbs a k t) hmeas (consumedAbs a k t)
            hend rfl).1 (x :: acc)
          rw [hchild, bdrop_consumedAbs_eq d a k x t hmem]
          show (Option.map (fun tail => (x :: acc).reverse ++ tail)
                (decodeFull d h (a.size - consumedAbs a k t)
                  (cast (congrArg Bytes (consumedAbs_remaining a k t).symm) t.bytes))) = _
          rw [decodeFull_cast d h (consumedAbs_remaining a k t).symm t.bytes]
        · have heq : consumedAbs a k t = a.size := by omega
          have hz : a.size - consumedAbs a k t = 0 := by omega
          have hrz : t.remaining = 0 := by rw [← hrem2]; exact hz
          rw [decodeFullArrayFast_zero d h a (consumedAbs a k t) hbd (x :: acc) hz]
          rw [decodeFull_at_zero d h t.remaining t.bytes hrz]
          simp only [Option.map, List.append_nil]


/-- The packed full-consumption decoder, at the start of the buffer. -/
def decodeFullArrayRoot {α : Type} (d : Codec α) (h : ConsumesByte d)
    (a : Array UInt8) : Option (List α) :=
  decodeFullArrayFast d h a 0 (Nat.zero_le _) []

/-- **The root bridge (task 6.1b's gate): the packed full-consumption decoder, from
cursor `0`, equals the specification.**

This is `array_bridge` at `K := a.size`, `k := 0`: `a.size - 0` is `a.size`, `bdrop 0`
is the identity, and the accumulator's reverse is a no-op — all definitional, exactly
as `decodeFullFastRoot_eq` takes `cursor_bridge`'s `m = 0` case. The empty buffer is
split off first because `array_bridge`'s cursor premise `k < a.size` is then false,
and both sides answer `some []` there anyway.

Note the specification side is **`decodeFull` directly**, not `decodeFullFastRoot`:
6.1a already proved those equal, so routing through it would add a second bridge for
no gain. `[propext, Quot.sound]`-only, zero `sorry`, and choice-free. -/
theorem decodeFullArrayRoot_eq {α : Type} (d : Codec α) (h : ConsumesByte d)
    (a : Array UInt8) :
    decodeFullArrayRoot d h a = decodeFull d h a.size (arrayToBytes a) := by
  unfold decodeFullArrayRoot
  rcases Nat.eq_zero_or_pos a.size with hz | hp
  · have h0 : a.size - 0 = 0 := by omega
    rw [decodeFullArrayFast_zero d h a 0 (Nat.zero_le _) [] h0,
        decodeFull_at_zero d h a.size (arrayToBytes a) hz]
    rfl
  · have hb := (array_bridge d h a a.size 0 hp (by omega)).1 []
    have hbd : bdrop 0 (arrayToBytes a) = arrayToBytes a := by
      funext i
      exact congrArg (arrayToBytes a) (Fin.ext (by simp))
    rw [hb]
    -- `a.size - 0` and `bdrop 0` are definitionally `a.size` and the identity, but
    -- `decodeFull`'s index blocks a `rw`; transport the *goal* instead.
    have hmap : (Option.map (fun tail => ([] : List α).reverse ++ tail)
        (decodeFull d h (a.size - 0) (bdrop 0 (arrayToBytes a))))
        = (decodeFull d h a.size (bdrop 0 (arrayToBytes a))) := by
      show ((decodeFull d h (a.size - 0) (bdrop 0 (arrayToBytes a))).map id)
          = decodeFull d h a.size (bdrop 0 (arrayToBytes a))
      -- `a.size - 0 = a.size`, so the two `decodeFull` calls are connected by
      -- `decodeFull_cast` at that equation.
      have hc := decodeFull_cast d h (n := a.size - 0) (m := a.size)
        (Nat.sub_zero a.size) (bdrop 0 (arrayToBytes a))
      -- `hc : decodeFull (a.size-0) (bdrop 0 …) = decodeFull a.size (cast … (bdrop 0 …))`
      rw [hc]
      exact congrFun Option.map_id _
    rw [hmap, hbd]


/-! ## The wired fast surface (task 6.3)

`decodeFullArrayRoot` is the fast decoder and is proved equal to the specification,
but until this section it was only *available*: no library-level entry point named it,
so a caller reaching for "decode this whole buffer" had to know to find it. These two
functions are that entry point, and they are what `README.md` points readers at.

The division of labour is the same one the rest of the library keeps:

* **`decodeWhole`** takes the runtime carrier (`Array UInt8`) and is the fast path —
  the packed cursor decoder, `decodeFullArrayRoot`.
* **`decodeWholeBytes`** takes the *specification* carrier (`Bytes n`), packs it, and
  delegates. The packing is the one `bytesToArray` transport, so no caller invents
  its own.

Both are equal to `decodeFull`, which is what lets every law about the specification
be read off for the wired surface without a second set of proofs. -/

/-- **The fast, whole-buffer full-consumption decoder — the surface to run.** Takes
the packed carrier and routes straight to `decodeFullArrayRoot` (the `Array UInt8` +
`Nat`-cursor search). Measured on an idle-ish machine at `n` = 4 KiB: **48 ns/byte**,
against 75 for the `Bytes`/`Suffix` `decodeFullFastRoot` and a 6 ns/step ideal-loop
floor — see `README.md`'s "Where the speed actually goes".

This is deliberately a *named* entry point rather than a note telling readers to call
`decodeFullArrayRoot`: a fast path that is merely available is a fast path nobody
takes. -/
def decodeWhole {α : Type} (d : Codec α) (h : ConsumesByte d) (a : Array UInt8) :
    Option (List α) :=
  decodeFullArrayRoot d h a

/-- **`decodeWhole` decodes exactly the specification.** `arrayToBytes`-readback of
the packed input, decoded by `decodeFull`, is what `decodeWhole` returns, so every
law about `decodeFull` transfers — **carrying its hypotheses with it**. In
particular `decodeFull_spec` is *conditional* on full-consumption uniqueness
(`huniq`, see `Codec.Sound`'s "Full-consumption uniqueness" section), so it explains
the wired surface only under that premise; this equality does not supply it.
One rewrite of the bridge; `[propext, Quot.sound]`-only. -/
theorem decodeWhole_eq {α : Type} (d : Codec α) (h : ConsumesByte d)
    (a : Array UInt8) :
    decodeWhole d h a = decodeFull d h a.size (arrayToBytes a) :=
  decodeFullArrayRoot_eq d h a

/-- **The specification-carrier entry point.** Packs a `Bytes n` and delegates to
`decodeWhole`; it exists so a caller holding the spec carrier has a wired path too,
rather than being left to choose between the slow `decodeFull` and hand-rolling the
packing. -/
def decodeWholeBytes {α : Type} (d : Codec α) (h : ConsumesByte d) {n : Nat}
    (s : Bytes n) : Option (List α) :=
  decodeWhole d h (bytesToArray s)

/-- **`decodeWholeBytes` decodes the specification over the readback.** The packed
delegate's `a.size` is `n` (`bytesToArray_size`), so the right side is `decodeFull`
at that size applied to `arrayToBytes (bytesToArray s)`.

**That is *not* the form a caller who started from `Bytes n` would state.** The form a
`Bytes n` caller states is `decodeWholeBytes d h s = decodeFull d h n s` — the size
argument being `n` and the buffer being `s` itself. Getting from here to there needs
the readback to round-trip, which is `arrayToBytes_bytesToArray`, and it is
**proved** as `decodeWholeBytes_spec`, immediately below. An earlier revision of this
docstring advertised the by-index form as if it already were the caller's law;
`[propext, Quot.sound]`-only. -/
theorem decodeWholeBytes_eq {α : Type} (d : Codec α) (h : ConsumesByte d) {n : Nat}
    (s : Bytes n) :
    decodeWholeBytes d h s = decodeFull d h (bytesToArray s).size
      (arrayToBytes (bytesToArray s)) :=
  decodeWhole_eq d h (bytesToArray s)

/-- **The readback is pointwise the identity.** Reading `arrayToBytes (bytesToArray s)` at
index `i` gives `s i`, at `i`'s own value re-indexed by the size equation.

This is the missing half of the round-trip the docstring above `bytesToArray` called
"`rfl` by `funext`/`Fin.ext`" — **it is not**. The two bridge lemmas are
`Array.getElem_toList` (the `Array` → `List` read bridge) and then `List.getElem_ofFn`.
(`Array.getElem_mk` and `Array.getElem_eq_getElem_toList` do not exist in 4.35.0.)

The bound is written `Nat.lt_of_lt_of_eq i.isLt (bytesToArray_size s)`, **not**
`by simpa …`: a `simpa` on a dependent `Fin` bound reaches classical logic through the
`Array`/`List` sizing simp set and makes the whole theorem depend on
`Classical.choice`, with no compiler error. `[propext, Quot.sound]`-only. -/
theorem arrayToBytes_bytesToArray_apply {n : Nat} (s : Bytes n)
    (i : Fin (bytesToArray s).size) :
    arrayToBytes (bytesToArray s) i
      = s ⟨i.val, Nat.lt_of_lt_of_eq i.isLt (bytesToArray_size s)⟩ := by
  have hiL : i.val < (List.ofFn s).length := by
    rw [List.length_ofFn]; exact Nat.lt_of_lt_of_eq i.isLt (bytesToArray_size s)
  show (Array.mk (List.ofFn s))[i.val] = s _
  rw [← Array.getElem_toList]
  exact List.getElem_ofFn (f := s) (i := i.val) (h := hiL)

/-- **The readback round-trips**, in the `cast` form a caller can rewrite with:
`arrayToBytes (bytesToArray s)` is `s` transported along the size equation.
`[propext, Quot.sound]`-only. -/
theorem arrayToBytes_bytesToArray {n : Nat} (s : Bytes n) :
    arrayToBytes (bytesToArray s)
      = cast (congrArg Bytes (bytesToArray_size s).symm) s := by
  funext i
  rw [cast_bytes_val_symm (e := (bytesToArray_size s)) (f := s) (i := i)]
  exact arrayToBytes_bytesToArray_apply s i

/-- Local helper: transporting the *size argument and the buffer together* along one
length equation leaves `decodeFull` unchanged. The final step of
`decodeWholeBytes_spec` is a rewrite **under a dependent argument**
(`decodeFull h (size) (cast …)` → `decodeFull h n s`), which `rw`, `subst` and
`generalize` all refuse with "Dependent elimination failed" or an unsolved bound.
Carrying `hk : k = n` and `ha : a = cast …` as *hypotheses* gives `subst` the
orientation it needs. `private`, so it is not public surface. -/
private theorem decodeWholeBytes_spec_aux {α : Type} (d : Codec α) (h : ConsumesByte d)
    {n : Nat} (s : Bytes n) (k : Nat) (hk : k = n)
    (a : Bytes k) (ha : a = cast (congrArg Bytes hk.symm) s) :
    d.decodeFull h k a = d.decodeFull h n s := by
  subst hk; subst ha; rfl

/-- **`decodeWholeBytes`'s law, at the caller's own index.**

`decodeWholeBytes_eq` states the specification only up to `(bytesToArray s).size` and
the readback `arrayToBytes (bytesToArray s)` — *not* the form a caller who started from
`Bytes n` would state, which is this one: `decodeWholeBytes d h s = decodeFull d h n s`.
The two bridge lemmas above close the gap. `[propext, Quot.sound]`-only. -/
theorem decodeWholeBytes_spec {α : Type} (d : Codec α) (h : ConsumesByte d) {n : Nat}
    (s : Bytes n) : decodeWholeBytes d h s = decodeFull d h n s := by
  unfold decodeWholeBytes
  rw [decodeWhole_eq]
  exact decodeWholeBytes_spec_aux d h s _ (bytesToArray_size s) _ (arrayToBytes_bytesToArray s)

/-- **The packed carrier is not a second spec.** The wired surface's input size is
the caller's index: `(bytesToArray s).size = n`, so `decodeWholeBytes`'s specification
is `decodeFull d h n` over a `Bytes n`, not over some carrier-private length. -/
theorem decodeWholeBytes_size {n : Nat} (s : Bytes n) : (bytesToArray s).size = n :=
  bytesToArray_size s

/-- **Decode a whole buffer as exactly ONE value.**

`decodeWhole`/`decodeWholeBytes` answer "how many values does this buffer hold" —
`Option (List α)`. For a single-value codec (a 2-byte integer, a header, a whole
message) that is the wrong question, and until this function there was **no wired entry point for
it**: `decodeOne` threads a cursor but is the committed-choice decoder, unproven
against the spec, and never wired; `decodeFull` is the repetition form. So a
downstream author with a 2-byte integer codec had to either invent repetition
semantics or drop to an unwired internal.

The definition is deliberately the **projection of the wired surface**, not a new
decoder: it is `decodeWhole` at a singleton result. That is what makes it usable
without new proofs — every law about `decodeWhole` (in particular
`decodeWhole_eq`) reads off for it immediately, and there is no third decoder whose
agreement with the spec would need establishing.

A buffer holding two values returns `none`, not the first: this is "decode **one**
value that consumes everything", and silently taking a prefix would be the
`decodeFullArray` head-projection defect (`Codec/Packed.lean`, "Do not use
`decodeFullArray` for full consumption" in `README.md`). -/
def decodeWholeOne {α : Type} (d : Codec α) (h : ConsumesByte d)
    (a : Array UInt8) : Option α :=
  match decodeWhole d h a with
  | some [x] => some x
  | _ => none

/-- The single-value entry point on the specification carrier. -/
def decodeWholeOneBytes {α : Type} (d : Codec α) (h : ConsumesByte d) {n : Nat}
    (s : Bytes n) : Option α :=
  decodeWholeOne d h (bytesToArray s)

/-- **`decodeWholeOne` is the `decodeWhole` singleton, hence the spec's.**
`some x` exactly when the specification decodes the whole buffer to exactly the list
`[x]`. Stated against `decodeFull` (via `decodeWhole_eq`) so a caller gets the
specification link without re-deriving anything; `[propext, Quot.sound]`-only. -/
theorem decodeWholeOne_eq {α : Type} (d : Codec α) (h : ConsumesByte d)
    (a : Array UInt8) (x : α) :
    decodeWholeOne d h a = some x ↔
      decodeFull d h a.size (arrayToBytes a) = some [x] := by
  unfold decodeWholeOne
  rw [decodeWhole_eq]
  cases hfull : decodeFull d h a.size (arrayToBytes a) with
  | none => simp
  | some xs => cases xs with
    | nil => simp
    | cons y ys => cases ys with
      | nil => simp
      | cons z zs => simp

/-- `decodeWholeOneBytes` is `decodeWholeOne` on the packed view of the bytes — the
one-line law tying the `Bytes`-indexed wrapper to the entry point it wraps. It is its
**own** law because §1.8's definition-coverage check is a *mention* proxy: a thin
wrapper no theorem names is indistinguishable, to that check, from a `def` nothing has
reasoned about. -/
theorem decodeWholeOneBytes_eq {α : Type} (d : Codec α) (h : ConsumesByte d) {n : Nat}
    (s : Bytes n) :
    decodeWholeOneBytes d h s = decodeWholeOne d h (bytesToArray s) :=
  rfl

/-- The packed full-consumption decoder equals the *first* spec `decode` result,
with its suffix packed as a `ByteArray` and its consumed count read back. (The
packed carrier takes the first match, exactly as the packed `head?`-projection of
`decode`; full backtracking is preserved by `decodeArray_eq`.) It uses both of the
two axioms the gate permits, and no other. -/
theorem decodeFullArray_spec {α : Type} (d : Codec α) (a : Array UInt8) (i : Nat) :
    (decodeFullArray d a i) =
      ((decode d (bdrop i (arrayToBytes a))).head?).map (fun (_, t) => (ByteArray.mk ((a.toList.drop (consumedAbs a i t)).toArray), consumedAbs a i t)) := by
  simp only [decodeFullArray]
  rw [decodeArray_eq d a i]
  cases hd : decode d (bdrop i (arrayToBytes a)) with
  | nil => simp
  | cons p tl => simp

/-! ## Refinement: the partial-remainder commit is definitional -/

/-- The partial-remainder commit is a definitional identity: `commitRemainder a c`
is exactly `ByteArray.mk (a.extract c.toNat a.size)`. No `Nat ↔ USize` roundtrip
the law needs to justify (the index is already `USize`, matching `byteSlice`'s own
index), so **no** `System.Platform.numBits` premise enters. The `byteSlice`→C trust
is a runtime contract invisible to Lean: `@[extern]` swaps only the emitted C, the
Lean body still reduces, so this law is **axiom-free** (`#print axioms` reports that
it depends on no axioms at all) with no `byteSlice`-related axiom. `rfl`-clean.
(**Measured.** This sentence used to state the two-axiom footprint, which the gate's
own `#guard_msgs` contradicted; corrected by `codec-audit-round-nine` §5.3a.)

This is `Codec.byteSlice_spec` at `ByteArray.mk a` — the seam law it rests on is
that theorem, not a re-derivation of the body here (see `Codec/ByteSlice.lean`, where
every Layer-2 seam carries its own `*_spec`). -/
theorem commitRemainder_spec (a : Array UInt8) (c : USize) :
    commitRemainder a c = ByteArray.mk (a.extract c.toNat a.size) := by
  rw [commitRemainder, byteSlice_spec]

/-! ## Task 6.7: the Layer-2 seam is measured faster, and is deliberately NOT wired

The two spellings of "the bytes of `a` at-or-after `c`" are
`ByteArray.mk ((a.toList.drop c).toArray)` — the `List` transport the refinement uses,
chosen because it consults no choice principle — and `commitRemainder a c.toUSize`, the
Layer-2 `memcpy` seam.

**The seam genuinely pays.** Measured `n` = 65536, same run, values checked identical
over six cursors including `0` and `n`:

| transport | cost |
| --- | --- |
| `ByteArray.mk ((a.toList.drop c).toArray)` | **~1.5 ms** |
| `commitRemainder a c.toUSize` | **~24 µs** |

So **~50–75×** (measured 36–63× across sizes and runs; the bench lane prints it live),
which is why task 6.7 went looking for a consumer rather than declaring the seam
pointless.

**Why there is still no theorem connecting them, and why the seam is not wired.** The
obvious proof needs `Array.extract`'s readback on the `List` side, i.e.
`Array.toList_extract` — and in this toolchain **`Array.toList_extract` and
`Array.getElem_extract` both report `[propext, Classical.choice, Quot.sound]`**. This
was checked with `#print axioms`, not assumed. There is therefore **no route to this
equality inside the `[propext, Quot.sound]`-only gate**, and a Layer-1 path may not
carry a transport that nothing axiom-clean connects to the refinement it is supposed
to refine.

Two consequences, both recorded rather than papered over:

1. **The seam stays unwired, on evidence.** The speed-up is real and quantified; the
   axiom cost is real and quantified; the decision is that the second outweighs the
   first for a path whose whole point is being axiom-clean. Task 2.4's
   header wording ("available but unused") is therefore still exactly right, and this
   note says *why* rather than leaving it looking like an oversight. If a future
   toolchain makes `Array.extract`'s readback axiom-clean, the wiring is one lemma and
   one call site away.
2. **A second, independent obstacle** is the cursor wrap: `c.toUSize.toNat` is
   `c % 2 ^ numBits`, so the two sides agree exactly when the cursor does not wrap, and
   discharging that needs `System.Platform.numBits = 64` — also outside the gate
   (`AGENTS.md`'s rail). It is satisfiable in practice (no buffer reaches `2^63`
   bytes), but it is a premise the clean route would have to carry as well.

`commitRemainder` remains exercised by the bench's Layer-2 lanes and pinned by
`commitRemainder_spec`, so its runtime contract is still evidence-backed — it simply
has no *library* caller, which is the state this section documents. -/

/-! ## Refinement: the packed encoder equals the spec `encode` -/

/-- If the readback equality holds, `encodeArray d x` is `none` exactly when
`encode d x` is `none`. This is the monadic-skeleton bridge that lets the
`seq`/`alt` cases of `encodeArray_eq` turn `encodeArray = none` into
`encode = none` (and back) without re-running the encoder. `[propext]`-only. -/
theorem map_toList_eq_ofFn_none_iff {α : Type} {d : Codec α} {x : α} :
    ((encodeArray d x).map (fun a : Array UInt8 => a.toList) = (encode d x).map (fun e => List.ofFn e.2)) →
    (encodeArray d x = none ↔ encode d x = none) := by
  intro h
  constructor
  · intro hnA
    cases e : encode d x with
    | none => rfl
    | some e' =>
        rcases e' with ⟨n, s⟩
        rw [hnA, e] at h
        simp only [Option.map] at h
        cases h
  · intro hn
    cases e : encodeArray d x with
    | none => rfl
    | some a =>
        rw [e, hn] at h
        simp only [Option.map] at h
        cases h

/-- The packed encoder equals the spec `encode`, up to the List-level readback:
`(encodeArray d x).map (·.toList) = (encode d x).map (List.ofFn ∘ snd)`. The
`Array.toList`/`List.ofFn` readback is the `[propext, Quot.sound]`-clean form (the
`Array.ofFn`/`Array.toList_ofFn` round-trip would leak `Classical.choice`); the
`seq` leaf is `Array.toList_append` + `ofFn_concat`. `[propext, Quot.sound]`-only. -/
theorem encodeArray_eq {α : Type} (d : Codec α) (x : α) :
    (encodeArray d x).map (fun a : Array UInt8 => a.toList) =
      (encode d x).map (fun e => List.ofFn e.2) := by
  induction d with
  | iso i d ih =>
      simp only [encodeArray, encode, Option.bind]
      cases hi : i.unapply x with
      | none => simp
      | some a => simpa [hi] using ih a
  | seq d₁ d₂ ih₁ ih₂ =>
      cases x with
      | mk x₁ x₂ =>
          simp only [encodeArray, encode, Option.bind]
          have h₁ := ih₁ x₁
          have h₂ := ih₂ x₂
          have hn₁ := (map_toList_eq_ofFn_none_iff (d := d₁) (x := x₁)) h₁
          have hn₂ := (map_toList_eq_ofFn_none_iff (d := d₂) (x := x₂)) h₂
          cases ha₁ : encodeArray d₁ x₁ with
          | none =>
              have he₁ : encode d₁ x₁ = none := hn₁.mp ha₁
              simp only [he₁, Option.map]
          | some a₁ =>
              have he₁ : encode d₁ x₁ ≠ none := by
                intro h; have := hn₁.mpr h; rw [ha₁] at this; cases this
              cases hx₁ : encode d₁ x₁ with
              | none => exfalso; exact he₁ hx₁
              | some e₁ =>
                  rcases e₁ with ⟨n₁, s₁⟩
                  cases ha₂ : encodeArray d₂ x₂ with
                  | none =>
                      have he₂ : encode d₂ x₂ = none := hn₂.mp ha₂
                      simp only [he₂, Option.map]
                  | some a₂ =>
                      have he₂ : encode d₂ x₂ ≠ none := by
                        intro h; have := hn₂.mpr h; rw [ha₂] at this; cases this
                      cases hx₂ : encode d₂ x₂ with
                      | none => exfalso; exact he₂ hx₂
                      | some e₂ =>
                          rcases e₂ with ⟨n₂, s₂⟩
                          have h₁' : a₁.toList = List.ofFn s₁ := by
                            rw [ha₁] at h₁
                            rw [hx₁] at h₁
                            simp only [Option.map] at h₁
                            exact Option.some.inj h₁
                          have h₂' : a₂.toList = List.ofFn s₂ := by
                            rw [ha₂] at h₂
                            rw [hx₂] at h₂
                            simp only [Option.map] at h₂
                            exact Option.some.inj h₂
                          simp only [Option.map]
                          rw [Array.toList_append, h₁', h₂']
                          exact congrArg some (ofFn_concat s₁ s₂).symm
  | alt d₁ d₂ ih₁ ih₂ =>
      simp only [encodeArray, encode]
      have h₁ := ih₁ x
      have h₂ := ih₂ x
      have hn₁ := (map_toList_eq_ofFn_none_iff (d := d₁) (x := x)) h₁
      cases ha₁ : encodeArray d₁ x with
      | none =>
          have he₁ : encode d₁ x = none := hn₁.mp ha₁
          simp only [he₁, Option.map]
          exact h₂
      | some a =>
          have he₁ : encode d₁ x ≠ none := by
            intro h
            have := hn₁.mpr h
            rw [ha₁] at this
            cases this
          simp only [Option.map]
          cases hx : encode d₁ x with
          | none => exfalso; exact he₁ hx
          | some e =>
              rcases e with ⟨n, s⟩
              rw [ha₁] at h₁
              simp only [Option.map] at h₁
              simpa [hx] using h₁
  | empty => simp [encodeArray, encode]
  | pure x₀ => by_cases h : x = x₀ <;> simp [encodeArray, encode, h]
  | byte => simp [encodeArray, encode, single]
  | satisfy p => by_cases h : p x <;> simp [encodeArray, encode, single, h]

/-- `ByteArray.push` projects to `Array.push` on the backing data. -/
theorem bpush_data (bs : ByteArray) (b : UInt8) : (bs.push b).data = bs.data.push b := by
  rfl

/-- `List.foldl` over `ByteArray.push` projects to `List.foldl` over `Array.push`
on the backing data. Free of axioms of every kind: measured, it depends on none. -/
theorem foldl_push_data (acc : ByteArray) (xs : List UInt8) :
    (List.foldl (fun a b => a.push b) acc xs).data = List.foldl (fun a b => a.push b) acc.data xs := by
  induction xs generalizing acc with
  | nil => rfl
  | cons b rest ih =>
      rw [List.foldl_cons, List.foldl_cons]
      rw [ih (acc.push b)]
      rw [bpush_data]

/-- `List.foldl` over `Array.push` is `acc ++ xs.toArray`. `[propext, Quot.sound]`-only. -/
theorem foldl_push_append (acc : Array UInt8) (xs : List UInt8) :
    List.foldl (fun a b => a.push b) acc xs = acc ++ xs.toArray := by
  induction xs generalizing acc with
  | nil => rw [List.foldl_nil, Array.append_empty]
  | cons b rest ih =>
      rw [List.foldl_cons, ih (acc.push b), List.toArray_cons]
      apply Array.ext'
      rw [Array.toList_append, Array.toList_append, Array.toList_push]
      rw [Array.toList_append]
      rw [List.append_assoc]

/-- The byte-sequence packer is the `List.toArray` materialization:
`encodeByteArrayBytes xs = ByteArray.mk xs.toArray`. `[propext, Quot.sound]`-only. -/
theorem encodeByteArrayBytes_eq (xs : List UInt8) :
    encodeByteArrayBytes xs = ByteArray.mk xs.toArray := by
  apply ByteArray.ext
  unfold encodeByteArrayBytes
  rw [foldl_push_data ByteArray.empty xs]
  change List.foldl (fun a b => a.push b) (#[] : Array UInt8) xs = (ByteArray.mk xs.toArray).data
  rw [foldl_push_append (#[] : Array UInt8) xs]
  rw [Array.empty_append]

/-! ## The wired fast encode surface (task 6.5)

The encode side had the same shape of defect 6.3 found on the decode side, and one
more: the fast encoder **existed and was proved** (`encodeArray`, `encodeArray_eq`)
but the repetition API did not use it. `encodeRepeat` builds a nested `concat`
closure per element — a `Bytes n := Fin n → UInt8` is a scalar-*read* substrate but a
nested-closure *bulk-write* substrate — and `fastEncodeRepeat`, which was supposed to
be the fast path, still calls `encode p x` per element and re-reads the resulting
`Bytes` through `pushBytes`. Measured, the two are within 1.3× of each other
(16 vs 20 MiB/s at 16 KiB), i.e. **the "fast" repetition encoder is not fast**: it
re-stages the accumulator but still pays the per-element `Bytes` intermediate.

`encodeArray`'s shape avoids that intermediate entirely — it accumulates directly
into `Array UInt8` with `++` and never materializes a `Bytes n`. These functions put
that shape behind a named surface, proved equal to the specification:

* **`encodeWhole`** — one value, packed carrier (`Array UInt8`), delegating to
  `encodeArray`;
* **`encodeWholeRepeat`** — a value list, accumulating through `encodeArray` with no
  per-element `Bytes` intermediate;
* **`encodeWholeBytes`** — the specification-carrier entry point (`Bytes n` out).

All three are tied to the existing specification (`encode`, `encodeRepeat`) by a law,
so every theorem about them reads off with no second set of proofs. -/

/-- **The wired encode surface, one value.** Delegates to `encodeArray`, whose shape
accumulates into `Array UInt8` with no per-element `Bytes` intermediate. -/
def encodeWhole {α : Type} (d : Codec α) (x : α) : Option (Array UInt8) :=
  encodeArray d x

/-- **`encodeWhole` is the specification, read back.** The `Array.toList` of the wired
surface's output is the spec `encode`'s byte list — literally `encodeArray_eq`, named
at the surface a caller reaches for, so the refinement cannot drift from the entry
point. `[propext, Quot.sound]`-only. -/
theorem encodeWhole_eq {α : Type} (d : Codec α) (x : α) :
    (encodeWhole d x).map (fun a : Array UInt8 => a.toList) =
      (encode d x).map (fun e => List.ofFn e.2) :=
  encodeArray_eq d x

/-- The `Array`-accumulating repetition encoder: fold `encodeArray` over the value
list, appending into one contiguous buffer.

This is the shape `fastEncodeRepeat` *intended* and did not achieve: it calls
`encode p x` per element (producing a `Bytes n` closure) and then re-reads that
closure byte-by-byte through `pushBytes`, so it pays a per-element intermediate.
Folding `encodeArray` removes the intermediate — the per-element write goes straight
into the accumulator. -/
def encodeWholeRepeatAcc {α : Type} (d : Codec α) :
    List α → Array UInt8 → Option (Array UInt8)
  | [], acc => some acc
  | x :: xs, acc =>
      (encodeArray d x).bind fun a => encodeWholeRepeatAcc d xs (acc ++ a)

/-- **The `Array`-accumulating repetition encoder, from an empty buffer.** -/
def encodeWholeRepeat {α : Type} (d : Codec α) (xs : List α) : Option (Array UInt8) :=
  encodeWholeRepeatAcc d xs #[]

/-- **A fold of `encodeArray` over a list, appended flat.** This is the pure `Array`
side of the accumulator: no `Bytes`, no `Sigma`, just the fold. -/
def encodeArrayFold {α : Type} (d : Codec α) : List α → Array UInt8 → Option (Array UInt8)
  | [], acc => some acc
  | x :: xs, acc => (encodeArray d x).bind fun a => encodeArrayFold d xs (acc ++ a)

/-- `encodeWholeRepeatAcc` *is* that fold — definitionally the same recursion. -/
theorem encodeWholeRepeatAcc_eq_fold {α : Type} (d : Codec α) (xs : List α)
    (acc : Array UInt8) :
    encodeWholeRepeatAcc d xs acc = encodeArrayFold d xs acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x rest ih =>
      simp only [encodeWholeRepeatAcc, encodeArrayFold]
      cases encodeArray d x <;> simp only [Option.bind] <;> exact ih _

/-- **The `Array` fold reads back as the flat append of `encode`'s bytes.** This is
`encodeArray_eq` lifted over the fold, and it is the *only* place the refinement is
used on the multi-value path: at each element the packed `Array` and the spec `Bytes`
are the same byte sequence, so folding one and appending equals folding the other.

Stated on the `List` readback (no `Bytes`-level cast, no `Fin n → UInt8` closure in the
statement), which is what keeps it `[propext, Quot.sound]`-only. -/
theorem encodeArrayFold_toList {α : Type} (d : Codec α) (xs : List α)
    (acc : Array UInt8) :
    (encodeArrayFold d xs acc).map (fun a : Array UInt8 => a.toList) =
      (encodeRepeat d xs).map (fun e : Sigma fun n => Bytes n =>
        acc.toList ++ List.ofFn e.2) := by
  -- A helper: the spec `encode` and the packed `encodeArray` agree on *failure* and,
  -- on success, on the byte list. Both directions are `encodeArray_eq`.
  have key : ∀ (x : α) (b : Array UInt8),
      encodeArray d x = some b →
      ∃ e : Sigma fun n => Bytes n, encode d x = some e ∧ b.toList = List.ofFn e.2 := by
    intro x b hb
    have hx := encodeArray_eq d x
    rw [hb] at hx
    cases he : encode d x with
    | none =>
        rw [he] at hx
        exact absurd hx (by simp)
    | some e =>
        rw [he] at hx
        simp only [Option.map, Option.some.injEq] at hx
        exact ⟨e, rfl, hx⟩
  have keyNone : ∀ (x : α), encodeArray d x = none → encode d x = none := by
    intro x hb
    have hx := encodeArray_eq d x
    rw [hb] at hx
    cases he : encode d x with
    | none => rfl
    | some e =>
        rw [he] at hx
        simp only [Option.map] at hx
        exact absurd hx (by simp)
  induction xs generalizing acc with
  | nil =>
      simp only [encodeArrayFold, encodeRepeat, Option.map]
      rw [show List.ofFn (emptyBytes : Bytes 0) = [] from
        List.eq_nil_of_length_eq_zero (by simp)]
      simp
  | cons x rest ih =>
      -- Unfold one step of each fold, keeping `Option.map` unexpanded so the
      -- induction hypothesis applies in its stated shape.
      simp only [encodeArrayFold, encodeRepeat]
      cases ha : encodeArray d x with
      | none =>
          have hspec : encode d x = none := keyNone x ha
          simp only [hspec, Option.map]
          simp
      | some a =>
          obtain ⟨e, he, hlist⟩ := key x a ha
          simp only [he, Option.bind]
          -- recurse on the tail; `ih` is stated on the `Option.map` form, so it is
          -- applied *before* `Option.map` is unfolded.
          rw [ih (acc ++ a)]
          simp only [Option.map]
          -- `a.toList` is `List.ofFn e.2`, so the packed side's append is the spec
          -- side's `concat` flattened (`ofFn_concat`). The two sides are both
          -- `Option.map` over `encodeRepeat rest`, so case on it to compare the
          -- payloads directly.
          cases hrp : encodeRepeat d rest with
          | none => simp
          | some rp =>
              simp only [Array.toList_append, hlist, ofFn_concat, List.append_assoc]

/-- **The accumulator equals the flat append of the per-element encodings.** Combines
the fold identity with the refinement above. `[propext, Quot.sound]`-only. -/
theorem encodeWholeRepeatAcc_toList {α : Type} (d : Codec α) (xs : List α)
    (acc : Array UInt8) :
    (encodeWholeRepeatAcc d xs acc).map (fun a : Array UInt8 => a.toList) =
      (encodeRepeat d xs).map (fun e : Sigma fun n => Bytes n =>
        acc.toList ++ List.ofFn e.2) := by
  rw [encodeWholeRepeatAcc_eq_fold]
  exact encodeArrayFold_toList d xs acc

/-- **The wired repetition encoder is the specification.** The `List` readback of
`encodeWholeRepeat` is exactly what `encodeRepeat` produces, so the fast route and the
spec produce the same bytes in the same order. `[propext, Quot.sound]`-only. -/
theorem encodeWholeRepeat_eq {α : Type} (d : Codec α) (xs : List α) :
    (encodeWholeRepeat d xs).map (fun a : Array UInt8 => a.toList) =
      (encodeRepeat d xs).map (fun e : Sigma fun n => Bytes n => List.ofFn e.2) := by
  have := encodeWholeRepeatAcc_toList d xs #[]
  simpa only [encodeWholeRepeat, Array.toList_empty, List.nil_append] using this

/-- **The specification-carrier encode entry point.** Returns a `Bytes n` directly, so
a caller that speaks `Bytes n` is not left to materialize the packing by hand. -/
def encodeWholeBytes {α : Type} (d : Codec α) (x : α) : Option (Sigma fun n => Bytes n) :=
  (encodeWhole d x).map fun a => ⟨a.size, fun i : Fin a.size => a[i]⟩

/-- **`encodeWholeBytes` encodes exactly the specification.** Its byte list is
`encodeWhole`'s, so reading the round trip through `encodeWhole_eq` gives the spec
`encode`'s bytes. `[propext, Quot.sound]`-only. -/
theorem encodeWholeBytes_toList {α : Type} (d : Codec α) (x : α) :
    (encodeWholeBytes d x).map (fun e : Sigma fun n => Bytes n => List.ofFn e.2) =
      (encode d x).map (fun e : Sigma fun n => Bytes n => List.ofFn e.2) := by
  simp only [encodeWholeBytes, Option.map]
  cases ha : encodeWhole d x with
  | none =>
      -- `encodeWhole` is `none`, so the spec is too (`encodeWhole_eq`).
      have hx := encodeWhole_eq d x
      simp only [ha, Option.map_none] at hx
      cases he : encode d x with
      | none => simp
      | some e =>
          rw [he] at hx
          simp at hx
  | some a =>
      have hx := encodeWhole_eq d x
      simp only [ha, Option.map_some] at hx
      cases he : encode d x with
      | none =>
          rw [he] at hx
          simp at hx
      | some e =>
          -- Reduce both sides of `hx` to the inner byte lists.
          rw [he, Option.map_some] at hx
          simp only [Option.some.injEq] at hx
          -- Reduce the nested `Option`s to the byte lists on both sides.
          simp only [Option.some.injEq]
          -- `List.ofFn (fun i => a[i])` is `a.toList` (the `Array` readback).
          have hread : List.ofFn (fun i : Fin a.size => a[i]) = a.toList := by
            apply List.ext_getElem
            · simp
            · intro n h1 h2
              simp only [List.getElem_ofFn, Array.getElem_toList]
              exact congrArg (fun i => a[i]) (Fin.ext rfl)
          rw [hread]
          exact hx

end Codec
