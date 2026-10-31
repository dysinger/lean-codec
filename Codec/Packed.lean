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
leak `Classical.choice`). -/
def arrayToBytes (a : Array UInt8) : Bytes a.size :=
  fun i => a[i.val]

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
(below), so its refinement stays `Classical.choice`-free without a trusted
`@[extern]`. `Codec/ByteSlice.lean` states the same thing from its side; the two
headers agree, and neither calls `commitRemainder` "the deferred commit" of a path
that never makes one.

The `Nat` cursor is a fixed binding decision (see the module header): it is the
proof carrier, kept `[propext, Quot.sound]`-clean; the `Nat → USize` conversion
happens once at the call site, if the caller ever commits a cursor. -/
def decodeArrayFast {α : Type} (d : Codec α) (a : Array UInt8) (i : Nat) : List (α × Nat) :=
  decodeArray d a i

/-! ## The packed full-consumption result -/

/-- The packed full-consumption decoder: a single suffix copy, never
`Option (List α × Suffix n)`. Its body is the `rfl`-clean
`ByteArray.mk ((a.toList.drop i).toArray)` — a list-materializing transport
(chosen so the refinement stays `Classical.choice`-free), **not**
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
the `hle` bound, which is proof-irrelevant). `[propext, Quot.sound]`-only. -/
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
`[propext, Quot.sound]`-only, zero `sorry`, zero `Classical.choice`. -/
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
never has to be invented. `[propext, Quot.sound]`-only, zero `Classical.choice`,
zero `sorry`. -/
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
`filterMap` over `attach` — never a `List.map`, so the membership witness survives. -/
def packedCands {α : Type} (d : Codec α) (_h : ConsumesByte d)
    (a : Array UInt8) (k : Nat) : List (PackedCand d a k) :=
  (decodeArray d a k).attach.filterMap fun p =>
    if hp : k < p.val.2 then
      if hq : p.val.2 ≤ a.size then some ⟨p.val, p.property, hp, hq⟩ else none
    else none

/-- **`filterMap` never lengthens.** The measure-side fact the packed search's
`termination_by` needs: `packedCands` is a `filterMap` of `(decodeArray d a k).attach`,
so its length is bounded by the candidate count. Stated for a general list because
the search's `decreasing_by` only ever needs the bound, never `packedCands`' body. -/
theorem length_filterMap_le {β γ : Type} (l : List β) (f : β → Option γ) :
    (l.filterMap f).length ≤ l.length := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    rw [List.filterMap_cons]
    split
    · simp only [List.length_cons]; omega
    · simpa using ih

/-- `packedCands` is no longer than the raw candidate list. -/
theorem length_packedCands_le {α : Type} (d : Codec α) (h : ConsumesByte d)
    (a : Array UInt8) (k : Nat) :
    (packedCands d h a k).length ≤ (decodeArray d a k).length := by
  unfold packedCands
  exact Nat.le_trans (length_filterMap_le _ _) (by simp)

mutual
def decodeFullArrayFast {α : Type} (d : Codec α) (h : ConsumesByte d)
    (a : Array UInt8) (k : Nat) (hk : k ≤ a.size) (acc : List α) : Option (List α) :=
  match _hm : a.size - k with
  | 0 => some acc.reverse
  | _ + 1 =>
    decodeFullArraySearch d h a k hk acc (packedCands d h a k)
termination_by (a.size - k, (packedCands d h a k).length + 1)

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
      decodeFullArraySearch d h a k hk acc (packedCands d h a k) := by
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
      ⟨pr, hpr, hkc, hlt⟩ ∈ packedCands d h a k := by
  have hkc : k < pr.2 := decodeArray_consumes d h a k pr.1 pr.2 hpr hk
  have hlt : pr.2 ≤ a.size :=
    decodeArray_bounded_upper d a k pr.2 pr.1 (Nat.le_of_lt hk) hpr
  refine ⟨hkc, hlt, ?_⟩
  unfold packedCands
  rw [List.mem_filterMap]
  refine ⟨⟨pr, hpr⟩, List.mem_attach _ _, ?_⟩
  simp only [hkc, hlt, ↓reduceDIte]

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

The proof is the recorded `match`-in-`match` recipe (`tasks.md` 6.1a trap 2): the
unfold is a `conv` on the LHS, then `simp only` to force the inner `match`, then
`split` for the outer one; `injection` on the discriminant equation re-aligns the
`split`-generated binders with the stated ones, after which the two sides are
syntactically equal and `rfl` closes it. -/
theorem decodeFullArraySearch_cons {α : Type} (d : Codec α) (h : ConsumesByte d)
    (a : Array UInt8) (k : Nat) (hk : k ≤ a.size) (acc : List α)
    (x : α) (c : Nat) (hmem : (x, c) ∈ decodeArray d a k ∧ k < c ∧ c ≤ a.size)
    (rest : List (PackedCand d a k)) :
    decodeFullArraySearch d h a k hk acc (⟨(x, c), hmem⟩ :: rest) =
      (match decodeFullArrayFast d h a c hmem.2.2 (x :: acc) with
       | none => decodeFullArraySearch d h a k hk acc rest
       | some xs => some xs) := by
  conv => lhs; rw [decodeFullArraySearch.eq_def]
  simp only
  split
  · simp at *
  · rename_i heq
    injection heq with h1 h2
    simp_all

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
`[propext, Quot.sound]`-only. -/
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
    packedCands d h a k =
      (decodeArray d a k).attach.map
        (fun p => (⟨p.val, p.property,
          decodeArray_consumes d h a k p.val.1 p.val.2 p.property hk,
          decodeArray_bounded_upper d a k p.val.2 p.val.1 (Nat.le_of_lt hk) p.property⟩ :
          PackedCand d a k)) := by
  unfold packedCands
  refine filterMap_eq_map_of_forall _ _ _ ?_
  intro p _
  have hp : k < p.val.2 := decodeArray_consumes d h a k p.val.1 p.val.2 p.property hk
  have hq : p.val.2 ≤ a.size :=
    decodeArray_bounded_upper d a k p.val.2 p.val.1 (Nat.le_of_lt hk) p.property
  simp only [hp, hq, ↓reduceDIte]

/-- **The two candidate lists have the same length.** A corollary of
`packedCands_eq_attach` and `decodeArray_eq`: nothing is dropped and nothing is
invented, so the packed search walks exactly as many candidates as the spec
backtracking step does. `[propext, Quot.sound]`-only. -/
theorem packedCands_length_eq {α : Type} (d : Codec α) (h : ConsumesByte d)
    (a : Array UInt8) (k : Nat) (hk : k < a.size) :
    (packedCands d h a k).length = (decode d (bdrop k (arrayToBytes a))).length := by
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
          omega⟩ : PackedCand d a k) ∈ packedCands d h a k := by
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
    CandAligned d a k (packedCands d h a k)
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
        decodeFullArraySearch d h a k (Nat.le_of_lt hk) acc (packedCands d h a k)
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
      rw [decodeFullArraySearch_eq_stepPacked d h a k (Nat.le_of_lt hk) acc (packedCands d h a k)]
      refine stepPacked_eq_step d h a (Nat.le_of_lt hk) acc (packedCands d h a k)
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
      rw [decodeFullArraySearch_eq_stepPacked d h a k (Nat.le_of_lt hk) acc (packedCands d h a k)]
      refine stepPacked_eq_step d h a (Nat.le_of_lt hk) acc (packedCands d h a k)
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
no gain. `[propext, Quot.sound]`-only, zero `sorry`, zero `Classical.choice`. -/
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


/-- The packed full-consumption decoder equals the *first* spec `decode` result,
with its suffix packed as a `ByteArray` and its consumed count read back. (The
packed carrier takes the first match, exactly as the packed `head?`-projection of
`decode`; full backtracking is preserved by `decodeArray_eq`.) `[propext,
Quot.sound]`-only. -/
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
Lean body still reduces, so `#print axioms Codec.commitRemainder_spec` reports
`[propext, Quot.sound]` with no `byteSlice`-related axiom. `rfl`-clean.

This is `Codec.byteSlice_spec` at `ByteArray.mk a` — the seam law it rests on is
that theorem, not a re-derivation of the body here (see `Codec/ByteSlice.lean`, where
every Layer-2 seam carries its own `*_spec`). -/
theorem commitRemainder_spec (a : Array UInt8) (c : USize) :
    commitRemainder a c = ByteArray.mk (a.extract c.toNat a.size) := by
  rw [commitRemainder, byteSlice_spec]

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
on the backing data. `[propext, Quot.sound]`-free (`#print axioms` ⇒ none). -/
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

end Codec
