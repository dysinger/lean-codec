/- Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later -/

import Codec.Codec

/-!
# The partial encoder

This file gives `encode`, the partial encoder, over the length-indexed byte
string:

    encode : Codec α → α → Option ({n : Nat} × Bytes n)

The encoded bytes *and* their length come back in one sigma, so `roundtrip` can
name the empty remainder `Bytes 0` without a separate length. Encoding is partial
by design: an out-of-domain value returns `none` (the paper's `Maybe` printer,
§4.2, kept as-is; we deliberately do not totalize it).
-/

namespace Codec

/-- The partial encoder: produce a length-indexed byte string for a value, or
`none` when the value is outside the description's domain. -/
def encode {α : Type} (d : Codec α) (x : α) : Option (Sigma fun n => Bytes n) :=
  match d with
  | Codec.iso i d =>
      (i.unapply x).bind fun a => encode d a
  | Codec.seq d₁ d₂ =>
      match x with
      | (x₁, x₂) =>
          (encode d₁ x₁).bind fun ⟨n₁, s₁⟩ =>
            (encode d₂ x₂).map fun ⟨n₂, s₂⟩ => ⟨n₁ + n₂, concat s₁ s₂⟩
  | Codec.alt d₁ d₂ => encode d₁ x <|> encode d₂ x
  | Codec.empty => none
  | Codec.pure x₀ => if x = x₀ then some ⟨0, emptyBytes⟩ else none
  | Codec.byte => some ⟨1, single x⟩

/-! ## The total encoder for repetition -/

/-- The total encoder for unbounded repetition: encode each element of `xs` with
`p` and concatenate, returning the total length and the concatenated bytes (a
`Fin`-sum concat, O(n) in the *type* index — no quadratic `List.append`). Recursion
is structural on the *value* list `xs`, so it is total for **every** `p` — encoding
needs no productivity witness (unlike `decodeRepeat`).

Its soundness law is `Codec.encodeRepeat_rel`. -/
def encodeRepeat {α : Type} (p : Codec α) (xs : List α) : Option (Sigma fun n => Bytes n) :=
  match xs with
  | [] => some ⟨0, emptyBytes⟩
  | x :: rest =>
      (encode p x).bind fun ⟨n₁, s₁⟩ =>
        (encodeRepeat p rest).map fun ⟨n₂, s₂⟩ => ⟨n₁ + n₂, concat s₁ s₂⟩

/-! ## The bulk fast path (`fastEncodeRepeat`)

`encodeRepeat` builds a nested `concat` closure per element (a pure `Bytes n :=
Fin n → UInt8` is a scalar-*read* substrate but a nested-closure *bulk-write*
substrate). `fastEncodeRepeat` re-stages the same denotation through a contiguous
`Array UInt8` accumulator behind the Lean runtime's `@[extern]` `Array.push`/
`append` (hand-written C compiled by the plain `cc`), then reads the result back
as a `Bytes` pointwise. The refinement lemma `fastEncodeRepeat_eq` proves the two
equal **without** `Classical.choice` (which the stdlib `Array.ofFn`/`List.toArray`/
`Array.toList` `GetElem` round-trip would leak) — the readback goes through a pure
`List.ofFn` read (`list_ofFn_getElem_clean`), never an `ofFn`-specialized bridge. -/

/-- Clean `List.ofFn` read: `(List.ofFn f)[i] = f ⟨i, ·⟩`, with the index bound
re-proved via `List.length_ofFn` — the `[propext, Quot.sound]`-clean replacement
for `List.getElem_ofFn` (whose output index proof carries `by simp_all`, a
`Classical.choice` leak). -/
theorem list_ofFn_getElem_clean {n : Nat} {α : Type} (f : Fin n → α) (i : Nat)
    (h : i < (List.ofFn f).length) :
    (List.ofFn f)[i] = f ⟨i, Nat.lt_of_lt_of_eq h (List.length_ofFn)⟩ := by
  induction n generalizing i with
  | zero => cases i <;> simp [List.ofFn_zero] at h
  | succ n ih =>
      cases i with
      | zero => simp [List.ofFn_succ]
      | succ i =>
          simp only [List.ofFn_succ, List.getElem_cons_succ]
          rw [ih (fun j => f j.succ) i]
          rfl

/-- `List.ofFn` distributes over `concat`: the enumeration of the `Fin`-sum
`concat s₀ s₁` is the append of the two enumerations. The keystone bridging the
spec's nested `concat` tree to a flat `List.append`. `[propext, Quot.sound]`-only. -/
theorem ofFn_concat {m n : Nat} (s₀ : Bytes m) (s₁ : Bytes n) :
    List.ofFn (concat s₀ s₁) = List.ofFn s₀ ++ List.ofFn s₁ := by
  apply List.ext_getElem
  · simp [List.length_ofFn]
  · intro i h₁ h₂
    rw [list_ofFn_getElem_clean (concat s₀ s₁) i h₁]
    rw [List.getElem_append]
    by_cases hi : i < m
    · simp [hi]; unfold concat; simp [hi]
    · simp [hi]; unfold concat; simp [hi]

/-- Byte-wise push: read `s ⟨·,·⟩` directly and `Array.push` each byte, with no
`List` enumeration in the loop (the whole point — the `(List.ofFn s).toArray`
append would materialize a `List` per element). Counter-indexed (thread `s`
unchanged, increment `i`), so the emitted IR allocates **no** per-byte `bdrop`
closure — just `lean_array_push` + `lean_nat_add` per byte. Terminating by the
well-founded measure `n - i`. -/
def pushBytesFrom {n : Nat} (i : Nat) (acc : Array UInt8) (s : Bytes n) : Array UInt8 :=
  if h : i < n then pushBytesFrom (i+1) (acc.push (s ⟨i, h⟩)) s else acc
termination_by n - i
decreasing_by simp_wf; omega

/-- Fresh byte-push from the front: `pushBytesFrom 0`. -/
def pushBytes {n : Nat} (acc : Array UInt8) (s : Bytes n) : Array UInt8 :=
  pushBytesFrom 0 acc s

/-- The byte string shifted to start at offset `i` (`s ⟨j + i, ·⟩`), of length
`n - i`. -/
def shiftedOfFn {n i : Nat} (h : i ≤ n) (s : Bytes n) : Bytes (n - i) :=
  fun j : Fin (n - i) => s ⟨j.val + i, by omega⟩

/-- `List.ofFn` of the shifted byte string is `List.drop i (List.ofFn s)`.
`[propext, Quot.sound]`-only. -/
theorem ofFn_shifted {n i : Nat} (h : i ≤ n) (s : Bytes n) :
    List.ofFn (shiftedOfFn h s) = List.drop i (List.ofFn s) := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_drop]
  · intro j hj₁ hj₂
    rw [list_ofFn_getElem_clean]
    rw [List.getElem_drop]
    rw [list_ofFn_getElem_clean]
    unfold shiftedOfFn
    congr 1
    apply Fin.ext
    exact Nat.add_comm j i

/-- The counter-indexed push invariant: pushing the suffix `s ⟨i..⟩` equals
appending `List.drop i (List.ofFn s)`. Proved by strong induction on the measure
`n - i` (each `Array.push` step is `cons` on the dropped list). `[propext, Quot.sound]`-only. -/
theorem pushBytesFrom_eq {n : Nat} (i : Nat) (acc : Array UInt8) (s : Bytes n) :
    pushBytesFrom i acc s = acc ++ (List.drop i (List.ofFn s)).toArray := by
  induction hn : n - i using Nat.strongRecOn generalizing i acc with
  | ind k ih =>
      rw [pushBytesFrom.eq_1]
      by_cases hlt : i < n
      · rw [dite_eq_left hlt]
        have hlt' : n - (i + 1) < k := by rw [← hn]; omega
        have hrec := ih (n - (i+1)) hlt' (i+1) (acc.push (s ⟨i, hlt⟩)) rfl
        rw [hrec]
        apply Array.ext'
        rw [Array.toList_append]
        rw [Array.toList_append]
        rw [Array.toList_push]
        rw [List.append_assoc]
        congr 1
        have hbound : i < (List.ofFn s).length := by
          simp only [List.length_ofFn]
          exact hlt
        rw [← List.getElem_cons_drop (as := List.ofFn s) (i := i) hbound]
        rw [list_ofFn_getElem_clean s i (by simp only [List.length_ofFn]; exact hlt)]
        rfl
      · rw [dite_eq_right hlt]
        have hge : n ≤ i := Nat.le_of_not_gt hlt
        have hdrop : List.drop i (List.ofFn s) = [] := by
          apply List.drop_eq_nil_of_le (as := List.ofFn s) (i := i) (by
            simp only [List.length_ofFn]
            exact hge)
        rw [hdrop]
        rfl

/-- Byte-wise push equals appending the whole enumeration: `pushBytes acc s =
acc ++ (List.ofFn s).toArray`. The bridge that lets the *fast* byte-push accumulator
keep the *same* refinement proof as the (slower) `List.ofFn`-append form (the
`pushBytesFrom_eq` case at `i = 0`). `[propext, Quot.sound]`-only. -/
theorem pushBytes_eq {n : Nat} (acc : Array UInt8) (s : Bytes n) :
    pushBytes acc s = acc ++ (List.ofFn s).toArray := by
  unfold pushBytes
  rw [pushBytesFrom_eq 0 acc s]
  rfl

/-- Tail-recursive `Array UInt8` accumulator for the bulk encoder: byte-wise
`Array.push` (an `@[extern]` contiguous write) reading `s ⟨·,·⟩` directly, no
`List` per element. `pushBytes_eq` re-states it in terms of `(List.ofFn s).toArray`
for the refinement proof. -/
def fastEncodeRepeatAcc {α : Type} (p : Codec α) : List α → Array UInt8 → Option (Array UInt8)
  | [], acc => some acc
  | x :: xs, acc =>
      (encode p x).bind fun ⟨_, s⟩ => fastEncodeRepeatAcc p xs (pushBytes acc s)

/-- Re-associating the accumulator append: `acc ++ (List.ofFn s₁).toArray ++
(List.ofFn s₂).toArray = acc ++ (List.ofFn (concat s₁ s₂)).toArray`. Proved
pointwise at the `List` level via `Array.ext'` + `ofFn_concat` — no
`Classical.choice`. -/
theorem append_toArray_ofFn_concat {m n : Nat} (acc : Array UInt8) (s₁ : Bytes m) (s₂ : Bytes n) :
    acc ++ (List.ofFn s₁).toArray ++ (List.ofFn s₂).toArray = acc ++ (List.ofFn (concat s₁ s₂)).toArray := by
  apply Array.ext'
  simp only [Array.toList_append, List.append_assoc]
  rw [ofFn_concat s₁ s₂]

/-- The accumulator equals `encodeRepeat` mapped onto `acc ++ (List.ofFn s).toArray`.
The tail recursion re-associates the `concat` tree into a flat array append;
`ofFn_concat` is the induction step (and `pushBytes_eq` re-states each byte-wise
push step as that append). `[propext, Quot.sound]`-only. -/
theorem fastEncodeRepeatAcc_eq {α : Type} (p : Codec α) (xs : List α) (acc : Array UInt8) :
    fastEncodeRepeatAcc p xs acc = (encodeRepeat p xs).map fun ⟨_, s⟩ => acc ++ (List.ofFn s).toArray := by
  induction xs generalizing acc with
  | nil => simp only [fastEncodeRepeatAcc, encodeRepeat, Option.map, List.ofFn_zero, Array.append_empty]
  | cons x xs ih =>
      cases hx : encode p x with
      | none => simp only [fastEncodeRepeatAcc, encodeRepeat, hx, Option.bind, Option.map]
      | some e =>
          rcases e with ⟨n₁, s₁⟩
          cases hr : encodeRepeat p xs with
          | none =>
              simp only [fastEncodeRepeatAcc, encodeRepeat, hx, hr, Option.bind, Option.map, pushBytes_eq]
              rw [ih (acc ++ (List.ofFn s₁).toArray)]
              simp only [hr, Option.map]
          | some er =>
              rcases er with ⟨n₂, s₂⟩
              simp only [fastEncodeRepeatAcc, encodeRepeat, hx, Option.bind, Option.map]
              rw [hr]
              change fastEncodeRepeatAcc p xs (pushBytes acc s₁)
                   = some (acc ++ (List.ofFn (concat s₁ s₂)).toArray)
              rw [ih (pushBytes acc s₁)]
              rw [hr]
              change some (pushBytes acc s₁ ++ (List.ofFn s₂).toArray)
                   = some (acc ++ (List.ofFn (concat s₁ s₂)).toArray)
              congr 1
              rw [pushBytes_eq acc s₁]
              exact append_toArray_ofFn_concat acc s₁ s₂

/-- Read back an `Array UInt8` as a `Bytes`, given its `toList` is `List.ofFn s`
and its size is the spec length: the sigma `⟨arr.size, fun i => arr[i]⟩` equals `⟨n, s⟩`.
The pointwise read is via `Array.getElem_toList` (no axioms) then the clean
`list_ofFn_getElem_clean` — never `Array.ofFn`/`List.toArray`/`Array.toList`
`GetElem` (which leak `Classical.choice`). `[propext, Quot.sound]`-only. -/
theorem array_readback {n : Nat} (s : Bytes n) (arr : Array UInt8)
    (h : arr.toList = List.ofFn s) (hl : arr.size = n) :
    (⟨arr.size, fun i : Fin arr.size => arr[i]⟩ : Sigma fun k => Bytes k) = ⟨n, s⟩ := by
  cases hl
  apply Sigma.ext
  · rfl
  · have hh : (fun i : Fin arr.size => arr[i]) = s := by
      apply Bytes.ext
      intro i
      change arr[i.val] = s i
      have hlen : arr.toList.length = (List.ofFn s).length := by rw [h]
      have hb : i.val < arr.toList.length := by
        rw [hlen]
        simpa only [List.length_ofFn] using i.isLt
      have hgt := Array.getElem_toList (xs := arr) (i := i.val) hb
      rw [← hgt]
      exact (by
        simpa only [h, List.length_ofFn] using
          (list_ofFn_getElem_clean s i.val (by simpa only [List.length_ofFn] using i.isLt)))
    exact heq_of_eq hh

/-- `#[] ++ arr` has the same `toList` as `arr`. -/
theorem nil_append_toList {α : Type} (arr : Array α) :
    (#[] ++ arr).toList = arr.toList := by
  simp only [Array.toList_append, List.nil_append]

/-- `#[] ++ arr` has the same size as `arr`. -/
theorem nil_append_size {α : Type} (arr : Array α) :
    (#[] ++ arr).size = arr.size := by
  simp only [Array.size_append, Array.size_empty, Nat.zero_add]

/-- The empty-accumulator fast path's `toList` is the spec enumeration. -/
theorem fastEncodeRepeatAcc_full_toList {n : Nat} (s : Bytes n) :
    (#[] ++ (List.ofFn s).toArray).toList = List.ofFn s := by
  rw [nil_append_toList]

/-- The empty-accumulator fast path's size is the spec length. -/
theorem fastEncodeRepeatAcc_full_size {n : Nat} (s : Bytes n) :
    (#[] ++ (List.ofFn s).toArray).size = n := by
  rw [nil_append_size]
  simp only [List.size_toArray, List.length_ofFn]

/-- The bulk fast path: accumulate into an `Array UInt8` and read back as a
`Bytes`. Denotationally identical to `encodeRepeat` (see `fastEncodeRepeat_eq`). -/
def fastEncodeRepeat {α : Type} (p : Codec α) (xs : List α) : Option (Sigma fun n => Bytes n) :=
  (fastEncodeRepeatAcc p xs #[]).map fun arr => ⟨arr.size, fun i : Fin arr.size => arr[i]⟩

/-- The refinement: `fastEncodeRepeat p xs = encodeRepeat p xs`, pointwise.
`[propext, Quot.sound]`-only, zero `Classical.choice`, zero `sorry`. -/
theorem fastEncodeRepeat_eq {α : Type} (p : Codec α) (xs : List α) :
    fastEncodeRepeat p xs = encodeRepeat p xs := by
  cases hx : encodeRepeat p xs with
  | none =>
      simp only [fastEncodeRepeat, fastEncodeRepeatAcc_eq, hx, Option.map]
  | some e =>
      rcases e with ⟨n, s⟩
      simp only [fastEncodeRepeat, fastEncodeRepeatAcc_eq, hx, Option.map]
      congr 1
      apply array_readback s (#[] ++ (List.ofFn s).toArray)
      · exact fastEncodeRepeatAcc_full_toList s
      · exact fastEncodeRepeatAcc_full_size s

end Codec
