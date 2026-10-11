/- Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later -/

import Codec.Decode

/-!
# The indexed array-carrier decoder (the F\* run-model)

The proven decoder `Codec.decode` is stated over `Bytes = List UInt8` because
`List` reduces under `simp`/`rfl`/`induction`; but every byte is a heap cons cell,
capping the running interpreter at ~30–100 ns/byte on the *carrier* alone.

This module supplies the F\* two-tier move: a **run-model** decoder recursing
natively over `Array UInt8` with a `Nat` index — reading `a[i]`, threading the
remainder as an index, never cons-peeling a byte list — plus **one** refinement
lemma `decodeArray_eq` proved by induction on `d`. Every spec law then transfers
by a one-line rewrite. `Array UInt8` is used rather than `ByteArray` because
`Array.toList` (hence `a.size`, `a[i]`) reduces to the stored `List`.

The refinement is staged: an internal decoder returns the *consumed length*
(relative to the start index), whose equality to the list spec closes by clean
`Nat.sub_add_sub_cancel` arithmetic; the public `decodeArray` then re-bases that
consumed length onto the absolute index `i`.
-/

namespace Codec

/-- The run-model decoder, returning the number of bytes *consumed* (relative to
the start index `i`, which is only used to read `a[i]` and to re-index recursive
calls). Structurally identical to `decode` but reading `a[i]` instead of
cons-peeling a `List`. -/
def decodeArrayRel {α : Type} (d : Codec α) (a : Array UInt8) (i : Nat) : List (α × Nat) :=
  match d with
  | Codec.iso is d =>
      (decodeArrayRel d a i).filterMap fun (x, n) => (is.apply x).map fun y => (y, n)
  | Codec.seq d₁ d₂ =>
      (decodeArrayRel d₁ a i).flatMap fun (x, m) =>
        (decodeArrayRel d₂ a (i + m)).map fun (y, n) => ((x, y), m + n)
  | Codec.alt d₁ d₂ => decodeArrayRel d₁ a i ++ decodeArrayRel d₂ a i
  | Codec.empty => []
  | Codec.pure x => [(x, 0)]
  | Codec.byte =>
      if h : i < a.size then [(a[i], 1)] else []

/-- A decoder result's remainder is a *suffix* of the input. -/
theorem decode_suffix {α : Type} (d : Codec α) (x : α) :
    ∀ (s r : Bytes), (x, r) ∈ decode d s → ∃ p, p ++ r = s := by
  induction d with
  | iso is d ih =>
      intro s r h
      rw [decode, List.mem_filterMap] at h
      rcases h with ⟨ab, hab, hf⟩
      rcases ab with ⟨a, s'⟩
      cases hia : is.apply a with
      | none => simp [hia] at hf
      | some y => simp [hia] at hf; rcases hf with ⟨_, hs'r⟩; subst r; exact ih a s s' hab
  | seq d₁ d₂ ih₁ ih₂ =>
      rcases x with ⟨x₁, x₂⟩
      intro s r h
      rw [decode, List.mem_flatMap] at h
      rcases h with ⟨ab, hab, hm⟩
      rcases ab with ⟨a₁, s₁⟩
      rw [List.mem_flatMap] at hm
      rcases hm with ⟨cd, hcd, hsing⟩
      rcases cd with ⟨a₂, s₂⟩
      rw [List.mem_singleton] at hsing
      cases hsing
      rcases ih₁ x₁ s s₁ hab with ⟨p₁, hp₁⟩
      rcases ih₂ x₂ s₁ r hcd with ⟨p₂, hp₂⟩
      exact ⟨p₁ ++ p₂, by rw [List.append_assoc, hp₂, hp₁]⟩
  | alt d₁ d₂ ih₁ ih₂ =>
      intro s r h
      rw [decode, List.mem_append] at h
      rcases h with hl | hr
      · exact ih₁ x s r hl
      · exact ih₂ x s r hr
  | empty => intro s r h; simp [decode] at h
  | pure x₀ => intro s r h; simp [decode] at h; rcases h with ⟨_, rfl⟩; exact ⟨[], rfl⟩
  | byte =>
      intro s r h
      cases s with
      | nil => simp [decode] at h
      | cons b rest => simp [decode] at h; rcases h with ⟨hxb, hr⟩; subst b; subst r; exact ⟨[x], rfl⟩

/-- A `flatMap` congruence: pointwise equality of the branch function on the
members of the list extends to the whole `flatMap`. -/
theorem flatMap_congr {α β : Type} {l : List α} {f g : α → List β}
    (h : ∀ a, a ∈ l → f a = g a) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.flatMap_cons]
      rw [h head (List.mem_cons_self (a := head) (l := tail)), ih (fun a ha => h a (List.mem_cons_of_mem head ha))]

/-- If `p ++ r = drop i l`, then `drop (i + p.length) l = r`. -/
theorem drop_add_length_of_append {l : List UInt8} {i : Nat} {p r : List UInt8}
    (h : p ++ r = List.drop i l) : List.drop (i + p.length) l = r := by
  have hdecomp : (List.take i l) ++ (List.drop i l) = l := List.take_append_drop i l
  rw [← hdecomp, ← h]
  rw [List.drop_append]
  rw [List.drop_eq_nil_of_le (by rw [List.length_take]; exact Nat.le_trans (Nat.min_le_left _ _) (Nat.le_add_right _ _))]
  simp
  rw [Nat.sub_add_comm (Nat.min_le_left i l.length)]
  rw [List.drop_append]
  rw [List.drop_eq_nil_of_le (show p.length ≤ i - min i l.length + p.length from Nat.le_add_left p.length (i - min i l.length))]
  simp
  have hmin : i ≤ l.length ∨ l.length ≤ i := Nat.le_total i l.length
  rcases hmin with hle_il | hl_li
  · rw [Nat.min_eq_left hle_il, Nat.sub_self]; simp
  · rw [Nat.min_eq_right hl_li]
    have hdropnil : List.drop i l = [] := List.drop_eq_nil_of_le hl_li
    rw [hdropnil] at h
    have hp : p = [] := by
      have := congrArg List.length h
      rw [List.length_append, List.length_nil] at this
      exact List.eq_nil_of_length_eq_zero (by omega)
    have hr : r = [] := by
      have := congrArg List.length h
      rw [List.length_append, List.length_nil] at this
      exact List.eq_nil_of_length_eq_zero (by omega)
    subst p r
    simp

/-- The relative-consumed run-model equals the list spec: a result `(x, n)` of
`decodeArrayRel d a i` carries the number of bytes consumed, matching a list
result `(x, r)` via `n = (a.toList.drop i).length - r.length`. -/
theorem decodeArrayRel_eq {α : Type} (d : Codec α) (a : Array UInt8) (i : Nat) :
    decodeArrayRel d a i =
      (decode d (a.toList.drop i)).map fun (x, r) => (x, (a.toList.drop i).length - r.length) := by
  induction d generalizing a i with
  | iso is d ih =>
      simp only [decodeArrayRel, decode]
      rw [ih]
      rw [List.filterMap_map]
      rw [List.map_filterMap]
      congr 1
      funext z
      rcases z with ⟨x, r⟩
      cases ho : is.apply x with
      | none => simp [ho]
      | some y => simp [ho]
  | alt d₁ d₂ ih₁ ih₂ =>
      simp only [decodeArrayRel, decode]
      rw [ih₁, ih₂, List.map_append]
  | empty => simp [decodeArrayRel, decode]
  | pure x => simp [decodeArrayRel, decode, Nat.sub_self]
  | byte =>
      unfold decodeArrayRel decode
      split
      · next h =>
          rw [show a.toList.drop i = a.toList[i] :: a.toList.drop (i + 1) from
            List.drop_eq_getElem_cons (by simpa using h)]
          change [(a[i], 1)] = [(a.toList[i], (a.toList[i] :: a.toList.drop (i+1)).length - (a.toList.drop (i+1)).length)]
          congr 1
          simp
      · next h =>
          rw [List.drop_eq_nil_iff.mpr (by
            by_cases hlt : i < a.toList.length
            · exfalso; exact h (by simpa using hlt)
            · omega)]
          rfl
  | seq d₁ d₂ ih₁ ih₂ =>
      simp only [decodeArrayRel, decode]
      rw [ih₁]
      rw [List.flatMap_map]
      rw [List.map_flatMap]
      apply flatMap_congr
      intro ab hab
      rcases ab with ⟨x, s₁⟩
      dsimp only
      rcases decode_suffix d₁ x (a.toList.drop i) s₁ hab with ⟨p, hp⟩
      have hj : (a.toList.drop i).length - s₁.length = p.length := by
        rw [← hp, List.length_append, Nat.add_sub_cancel_right]
      have hdrop : a.toList.drop (i + p.length) = s₁ := drop_add_length_of_append hp
      rw [hj]
      have h₂ := ih₂ (a := a) (i := i + p.length)
      rw [h₂]
      rw [hdrop]
      rw [List.map_map]
      rw [List.map_flatMap]
      rw [List.map_eq_flatMap]
      apply flatMap_congr
      intro cd hcd
      rcases cd with ⟨y, r⟩
      dsimp only
      rcases decode_suffix d₂ y s₁ r hcd with ⟨q, hq⟩
      have hlen_s : s₁.length = q.length + r.length := by rw [← hq, List.length_append]
      have hlen_dropi : (a.toList.drop i).length = p.length + s₁.length := by rw [← hp, List.length_append]
      change [((x, y), p.length + (s₁.length - r.length))] = [((x, y), (a.toList.drop i).length - r.length)]
      congr 1
      have hsle : s₁.length ≤ (a.toList.drop i).length := by omega
      have hrle : r.length ≤ s₁.length := by omega
      rw [← hj, Nat.sub_add_sub_cancel hsle hrle]

/-- The public indexed array-carrier decoder: every `(value, remaining-index)`
pair derivable from `d` against `a` starting at absolute position `i`. -/
def decodeArray {α : Type} (d : Codec α) (a : Array UInt8) (i : Nat) : List (α × Nat) :=
  (decodeArrayRel d a i).map fun (x, n) => (x, i + n)

/-- The single refinement law: absolute-index form. The index is `i` plus the
number of bytes consumed (relative), i.e. the position after the match. -/
theorem decodeArray_eq {α : Type} (d : Codec α) (a : Array UInt8) (i : Nat) :
    decodeArray d a i =
      (decode d (a.toList.drop i)).map fun (x, r) => (x, i + ((a.toList.drop i).length - r.length)) := by
  rw [decodeArray, decodeArrayRel_eq]
  rw [List.map_map]
  rfl

/-- The single-byte reading. -/
theorem decodeArray_byte (a : Array UInt8) (i : Nat) :
    decodeArray Codec.byte a i =
      if h : i < a.size then [(a[i], i + 1)] else [] := by
  unfold decodeArray decodeArrayRel
  split
  · simp
  · simp

/-! ## The full-consumption array repetition decoder (Tier-B analogue)

The array-carrier analogue of `decodeFull` (`Codec.Decode`): a single `Option`
thread over the *remaining length* `a.size - i`, returning `some (xs, j)` exactly
when `many p` — realized as the full-consumption list `xs` — matches the whole
remaining input and ends at absolute index `j` (necessarily `a.toList.length`).
It is **defined by composition**: the proven, already-efficient `decodeFull` is run
on `a.toList.drop i` (the `Array`'s stored `List`, reached without copying), and the
single result is re-based onto the absolute index. Because `decodeFull` is total and
`#eval`-able for every productive `p` (the same `ConsumesByte` guard), so is
`decodeFullArray`; its equality law transfers from `decodeFull_spec` in one line. -/

/-- The full-consumption repetition decoder over the array carrier: `some (xs, j)`
iff `decodeFull p h` fully consumes `a.toList.drop i` as `xs`, with `j = a.toList.length`
the absolute index after full consumption. Total and `#eval`-able for productive `p`.
(Defined by composition over the proven `decodeFull`; the run-model is the `Array`'s
stored `List`, not a per-byte cons-peel re-derived here.) -/
def decodeFullArray {α : Type} (p : Codec α) (h : ConsumesByte p) (a : Array UInt8) (i : Nat) :
    Option (List α × Nat) :=
  (decodeFull p h (a.toList.drop i)).map fun xs => (xs, a.toList.length)

/-- The full-consumption law for the array carrier: `decodeFullArray p h a i = some (xs, j)`
iff `xs` is the (unique, under `huniq`) list that fully consumes `a.toList.drop i` via
`decodeRepeat`, and `j = a.toList.length`. Transferred from `decodeFull_spec` through the
compositional definition in one line; no new induction. -/
theorem decodeFullArray_spec {α : Type} (p : Codec α) (h : ConsumesByte p)
    (huniq : ∀ {x y : List α} {s : Bytes},
      (x, []) ∈ decodeRepeat p h s → (y, []) ∈ decodeRepeat p h s → x = y)
    (a : Array UInt8) (i : Nat) (xs : List α) (j : Nat) :
    decodeFullArray p h a i = some (xs, j) ↔
      (xs, []) ∈ decodeRepeat p h (a.toList.drop i) ∧ j = a.toList.length := by
  rw [decodeFullArray]
  constructor
  · intro hm
    cases hf : decodeFull p h (a.toList.drop i) with
    | none => rw [hf] at hm; cases hm
    | some ys =>
        rw [hf] at hm
        simp at hm
        rcases hm with ⟨hxs, hj⟩
        subst xs
        subst j
        exact ⟨decodeFull_some p h ys (a.toList.drop i) hf, rfl⟩
  · intro hm
    rcases hm with ⟨hmem, hj⟩
    subst j
    have hful : decodeFull p h (a.toList.drop i) = some xs := (decodeFull_spec p h huniq xs (a.toList.drop i)).2 hmem
    rw [hful]
    rfl

end Codec
