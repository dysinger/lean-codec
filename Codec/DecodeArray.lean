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

/-! ## The full-consumption array repetition decoder (native)

The array-carrier analogue of `decodeFull` (`Codec.Decode`): a single `Option`
thread over the *remaining length* `a.size - i`, returning `some (xs, j)` exactly
when `many p` — realized as the full-consumption list `xs` — matches the whole
remaining input and ends at absolute index `j` (necessarily `a.size`). It is a
**native `WellFounded.fix`** reading `a[i]` (the O(1) `Array.get!`) — *not*
`decodeFull` over `a.toList.drop i` — so no full `List` is materialized from the
array (decision #2 in the `bytearray-carrier-decoders` design: composition over
`decodeFull` defeats the carrier). Its spec law closes by the same
`WellFounded.induction` + candidate-correspondence machinery as
`decodeFullByteArray_spec`, routed through `decodeArrayRel_eq`. -/

/-- A result `(x, m) ∈ decodeArrayRel p a i` consumes `0 < m` bytes. -/
theorem decodeArrayRel_pos {α : Type} (p : Codec α) (h : ConsumesByte p) (a : Array UInt8) (i : Nat) (x : α) (m : Nat) :
    (x, m) ∈ decodeArrayRel p a i → 0 < m := by
  intro hmem
  rw [decodeArrayRel_eq] at hmem
  rw [List.mem_map] at hmem
  rcases hmem with ⟨pr, hpr, heq⟩
  rcases pr with ⟨x', r⟩
  have hx : x' = x := congrArg Prod.fst heq
  have hm : (a.toList.drop i).length - r.length = m := congrArg Prod.snd heq
  subst x'
  have hlt : r.length < (a.toList.drop i).length := h x r (a.toList.drop i) hpr
  rw [← hm]
  omega

/-- A result `(x, m) ∈ decodeArrayRel p a i` never overruns: `m ≤ a.size - i`. -/
theorem decodeArrayRel_le_size {α : Type} (p : Codec α) (a : Array UInt8) (i : Nat) (x : α) (m : Nat) :
    (x, m) ∈ decodeArrayRel p a i → m ≤ a.size - i := by
  intro hmem
  rw [decodeArrayRel_eq] at hmem
  rw [List.mem_map] at hmem
  rcases hmem with ⟨pr, hpr, heq⟩
  rcases pr with ⟨x', r⟩
  have hm : (a.toList.drop i).length - r.length = m := congrArg Prod.snd heq
  rw [← hm]
  rw [List.length_drop]
  have hsize : a.toList.length = a.size := rfl
  rw [hsize]
  omega

/-- The conjunction: productivity + in-bounds. -/
theorem decodeArrayRel_bounds {α : Type} (p : Codec α) (h : ConsumesByte p) (a : Array UInt8) (i : Nat) (x : α) (m : Nat) :
    (x, m) ∈ decodeArrayRel p a i → 0 < m ∧ i + m ≤ a.size := by
  intro hmem
  exact ⟨decodeArrayRel_pos p h a i x m hmem, by
      have hmle := decodeArrayRel_le_size p a i x m hmem
      have hpos := decodeArrayRel_pos p h a i x m hmem
      omega⟩

/-- The well-foundedness witness for the recursion step. -/
theorem decodeFullArray_lt {α : Type} (p : Codec α) (h : ConsumesByte p) (a : Array UInt8) (i : Nat)
    (x : α) (m : Nat) (hm : (x, m) ∈ decodeArrayRel p a i) :
    InvImage (· < ·) (fun j : Nat => a.size - j) (i + m) i := by
  have hb := decodeArrayRel_bounds p h a i x m hm
  rcases hb with ⟨_hm_pos, hm_le⟩
  change a.size - (i + m) < a.size - i
  omega

/-- Forward candidate correspondence: `(x, m)` (relative) maps to the `Bytes`
result `(x, drop (i + m))`. -/
theorem mem_decodeArrayRel_to_decode {α : Type} (p : Codec α) (a : Array UInt8) (i m : Nat) (x : α)
    (hm : (x, m) ∈ decodeArrayRel p a i) :
    ((x, a.toList.drop (i + m)) ∈ decode p (a.toList.drop i)) := by
  rw [decodeArrayRel_eq] at hm
  rw [List.mem_map] at hm
  rcases hm with ⟨pr, hpr, heq⟩
  rcases pr with ⟨x', r⟩
  have hx : x' = x := congrArg Prod.fst heq
  have hm' : (a.toList.drop i).length - r.length = m := congrArg Prod.snd heq
  subst x'
  have hsuffix := decode_suffix p x (a.toList.drop i) r hpr
  rcases hsuffix with ⟨q, hq⟩
  have hqlen : q.length = m := by
    have hlen := congrArg List.length hq
    rw [List.length_append] at hlen
    have : q.length = (a.toList.drop i).length - r.length := by omega
    rw [this]
    exact hm'
  have hr : r = a.toList.drop (i + m) := by
    have hdrop : a.toList.drop (i + q.length) = r := drop_add_length_of_append hq
    rw [hqlen] at hdrop
    exact hdrop.symm
  rw [← hr]
  exact hpr

/-- Reverse candidate correspondence: `(x, s₁)` maps to `(x, (drop i).length - s₁.length)`. -/
theorem mem_decodeArrayRel_of_decode {α : Type} (p : Codec α) (a : Array UInt8) (i : Nat)
    (x : α) (s₁ : Bytes) (hm : (x, s₁) ∈ decode p (a.toList.drop i)) :
    (x, (a.toList.drop i).length - s₁.length) ∈ decodeArrayRel p a i := by
  rw [decodeArrayRel_eq]
  rw [List.mem_map]
  refine ⟨(x, s₁), hm, rfl⟩

/-- The suffix `s₁` of `drop i` is `drop (i+m)` for `m = (drop i).length - s₁.length`. -/
theorem drop_of_mem_decode {α : Type} (p : Codec α) (a : Array UInt8) (i : Nat)
    (x : α) (s₁ : Bytes) (hm : (x, s₁) ∈ decode p (a.toList.drop i)) :
    a.toList.drop (i + ((a.toList.drop i).length - s₁.length)) = s₁ := by
  have hsuffix := decode_suffix p x (a.toList.drop i) s₁ hm
  rcases hsuffix with ⟨q, hq⟩
  have hqd : a.toList.drop (i + q.length) = s₁ := drop_add_length_of_append hq
  have hqlen : q.length = (a.toList.drop i).length - s₁.length := by
    have hlen := congrArg List.length hq
    rw [List.length_append] at hlen
    omega
  rw [hqlen] at hqd
  exact hqd

/-- The native full-consumption step: thread the `attach`-ed candidate steps,
picking the first whose strictly-shorter recursion yields a full consumption. -/
def decodeFullArrayStep {α : Type} (p : Codec α) (h : ConsumesByte p) (a : Array UInt8) (i : Nat)
    (ih : (j : Nat) → InvImage (· < ·) (fun j => a.size - j) j i → Option (List α × Nat)) :
    List { pr : α × Nat // pr ∈ decodeArrayRel p a i } → Option (List α × Nat)
  | [] => none
  | ⟨(x, m), hm⟩ :: rest =>
      match ih (i + m) (decodeFullArray_lt p h a i x m hm) with
      | none => decodeFullArrayStep p h a i ih rest
      | some (xs, j) => some (x :: xs, j)

/-- The native full-consumption repetition decoder over the array carrier:
`some (xs, j)` iff the productive `p` fully consumes the remaining bytes of `a`
from index `i` as `xs`, ending at `j = a.size`. A `WellFounded.fix` on the
remaining length `a.size - i`, reading `a[i]` — the index mirror of `decodeFull`,
with no `List` materialized from the array. Total and `#eval`-able for productive
`p`. -/
def decodeFullArray {α : Type} (p : Codec α) (h : ConsumesByte p) (a : Array UInt8) (i : Nat) :
    Option (List α × Nat) :=
  WellFounded.fix (InvImage.wf (fun j : Nat => a.size - j) Nat.lt_wfRel.wf)
    (fun i ih =>
      if _hge : a.size ≤ i then some ([], a.size)
      else decodeFullArrayStep p h a i ih (decodeArrayRel p a i).attach)
    i

/-- Forward soundness of the native step. -/
theorem decodeFullArrayStep_some {α : Type} (p : Codec α) (h : ConsumesByte p)
    (a : Array UInt8) (i : Nat)
    (ih : (j : Nat) → InvImage (· < ·) (fun j => a.size - j) j i → Option (List α × Nat)) :
    ∀ (l : List { pr : α × Nat // pr ∈ decodeArrayRel p a i }) (ys : List α) (j : Nat),
      decodeFullArrayStep p h a i ih l = some (ys, j) →
        ∃ (x : α) (xs : List α) (m : Nat) (hm : (x, m) ∈ decodeArrayRel p a i),
          ⟨(x, m), hm⟩ ∈ l ∧
            ih (i + m) (decodeFullArray_lt p h a i x m hm) = some (xs, j) ∧ ys = x :: xs := by
  intro l ys j
  induction l generalizing ys j with
  | nil => simp [decodeFullArrayStep]
  | cons hd tl ihL =>
      rcases hd with ⟨⟨x, m⟩, hm⟩
      rw [decodeFullArrayStep]
      cases ho : ih (i + m) (decodeFullArray_lt p h a i x m hm) with
      | none =>
          intro h
          rcases ihL _ _ h with ⟨x', xs', m', hm', hmem, hih', hys⟩
          refine ⟨x', xs', m', hm', ?_, hih', hys⟩
          rw [List.mem_cons]
          right
          exact hmem
      | some pr =>
          intro h
          rcases pr with ⟨xs₀, j₀⟩
          simp only at h
          cases h
          refine ⟨x, xs₀, m, hm, ?_, ho, rfl⟩
          simp

/-- **Forward soundness** of the native full-consumption array decoder. -/
theorem decodeFullArray_some {α : Type} (p : Codec α) (h : ConsumesByte p) :
    ∀ (xs : List α) (a : Array UInt8) (i : Nat) (j : Nat),
      decodeFullArray p h a i = some (xs, j) →
        (xs, []) ∈ decodeRepeat p h (a.toList.drop i) ∧ j = a.size := by
  intro xs a i j
  revert xs j
  induction i using WellFounded.induction
      (hwf := InvImage.wf (fun j : Nat => a.size - j) Nat.lt_wfRel.wf) with
  | h i ih =>
      intro xs j he
      have hfix : decodeFullArray p h a i = some (xs, j) := he
      unfold decodeFullArray at hfix
      rw [WellFounded.fix_eq] at hfix
      by_cases hge : a.size ≤ i
      · have hdrop : a.toList.drop i = [] := List.drop_eq_nil_of_le (by simpa using hge)
        simp [hge] at hfix
        rcases hfix with ⟨rfl, rfl⟩
        constructor
        · rw [hdrop, decodeRepeat_eq]
          simp
        · rfl
      · simp [hge] at hfix
        rcases (decodeFullArrayStep_some p h a i (fun j _hlt => decodeFullArray p h a j)
            (decodeArrayRel p a i).attach xs j hfix) with ⟨x, xs', m, hm, hmem, hih', hxs⟩
        subst xs
        constructor
        · rw [decodeRepeat_eq, List.mem_cons]
          right
          have hcorr : (x, a.toList.drop (i + m)) ∈ decode p (a.toList.drop i) :=
            mem_decodeArrayRel_to_decode p a i m x hm
          rw [List.mem_flatMap]
          refine ⟨⟨(x, a.toList.drop (i + m)), hcorr⟩, ?_, ?_⟩
          · exact List.mem_attach (decode p (a.toList.drop i)) ⟨(x, a.toList.drop (i + m)), hcorr⟩
          · rw [List.mem_map]
            refine ⟨(xs', []), ?_, rfl⟩
            exact (ih (i + m) (decodeFullArray_lt p h a i x m hm) xs' j hih').1
        · exact (ih (i + m) (decodeFullArray_lt p h a i x m hm) xs' j hih').2

/-- Completeness of the native step. -/
theorem decodeFullArrayStep_ne_none {α : Type} (p : Codec α) (h : ConsumesByte p)
    (a : Array UInt8) (i : Nat)
    (ih : (j : Nat) → InvImage (· < ·) (fun j => a.size - j) j i → Option (List α × Nat)) :
    ∀ (l : List { pr : α × Nat // pr ∈ decodeArrayRel p a i }),
      (∃ (x : α) (pr : List α × Nat) (m : Nat) (hm : (x, m) ∈ decodeArrayRel p a i),
        ⟨(x, m), hm⟩ ∈ l ∧ ih (i + m) (decodeFullArray_lt p h a i x m hm) = some pr) →
      decodeFullArrayStep p h a i ih l ≠ none := by
  intro l
  induction l with
  | nil =>
      intro hnone
      rcases hnone with ⟨x, pr, m, hm, hmem, _⟩
      cases hmem
  | cons hd tl ihL =>
      rcases hd with ⟨⟨x, m⟩, hm⟩
      intro hex
      rw [decodeFullArrayStep]
      cases ho : ih (i + m) (decodeFullArray_lt p h a i x m hm) with
      | none =>
          rcases hex with ⟨x', pr', m', hm', hmem, hih'⟩
          rw [List.mem_cons] at hmem
          rcases hmem with hmem | hmem
          · cases hmem
            rw [ho] at hih'
            cases hih'
          · exact ihL ⟨x', pr', m', hm', hmem, hih'⟩
      | some pr =>
          simp

/-- **Completeness** of the native full-consumption array decoder. -/
theorem decodeFullArray_ne_none {α : Type} (p : Codec α) (h : ConsumesByte p) :
    ∀ (xs : List α) (a : Array UInt8) (i : Nat),
      (xs, []) ∈ decodeRepeat p h (a.toList.drop i) → decodeFullArray p h a i ≠ none := by
  intro xs a i
  revert xs
  induction i using WellFounded.induction
      (hwf := InvImage.wf (fun j : Nat => a.size - j) Nat.lt_wfRel.wf) with
  | h i ih =>
      intro xs hmem
      unfold decodeFullArray
      rw [WellFounded.fix_eq]
      by_cases hge : a.size ≤ i
      · simp [hge]
      · simp [hge]
        rw [decodeRepeat_eq] at hmem
        rw [List.mem_cons] at hmem
        rcases hmem with hmem | hmem
        · have hdr : a.toList.drop i = [] := (congrArg Prod.snd hmem).symm
          have hlen0 : (a.toList.drop i).length = 0 := by rw [hdr]; rfl
          have : a.size - i = 0 := by simpa using hlen0
          omega
        · rw [List.mem_flatMap] at hmem
          rcases hmem with ⟨a', ha', hres⟩
          rcases a' with ⟨⟨x, s₁⟩, hm⟩
          rw [List.mem_map] at hres
          rcases hres with ⟨pr, hpr, hprmap⟩
          rcases pr with ⟨xs', r⟩
          cases hprmap
          let m := (a.toList.drop i).length - s₁.length
          have hmba : (x, m) ∈ decodeArrayRel p a i := mem_decodeArrayRel_of_decode p a i x s₁ hm
          have hsdrop : a.toList.drop (i + m) = s₁ := drop_of_mem_decode p a i x s₁ hm
          have hltstep := decodeFullArray_lt p h a i x m hmba
          have hne_s₁ : decodeFullArray p h a (i + m) ≠ none := by
            have : (xs', []) ∈ decodeRepeat p h (a.toList.drop (i + m)) := by
              rw [hsdrop]
              exact hpr
            exact ih (i + m) hltstep xs' this
          cases ho : decodeFullArray p h a (i + m) with
          | none => exact False.elim (hne_s₁ ho)
          | some pr =>
              apply decodeFullArrayStep_ne_none p h a i
                (fun j _hlt => decodeFullArray p h a j) (decodeArrayRel p a i).attach
              refine ⟨x, pr, m, hmba, ?_, ?_⟩
              · exact List.mem_attach (decodeArrayRel p a i) ⟨(x, m), hmba⟩
              · rw [ho]

/-- The full-consumption law for the **native** array carrier: `decodeFullArray
p h a i = some (xs, j)` iff `xs` is the (unique, under `huniq`) list that fully
consumes `a.toList.drop i` via `decodeRepeat`, ending at `j = a.size`. The index
mirror of `decodeFull_spec`, with the same uniqueness hypothesis. -/
theorem decodeFullArray_spec {α : Type} (p : Codec α) (h : ConsumesByte p)
    (huniq : ∀ {x y : List α} {s : Bytes},
      (x, []) ∈ decodeRepeat p h s → (y, []) ∈ decodeRepeat p h s → x = y)
    (a : Array UInt8) (i : Nat) (xs : List α) (j : Nat) :
    decodeFullArray p h a i = some (xs, j) ↔
      (xs, []) ∈ decodeRepeat p h (a.toList.drop i) ∧ j = a.size := by
  constructor
  · exact decodeFullArray_some p h xs a i j
  · intro hmemj
    rcases hmemj with ⟨hmem, hj⟩
    subst j
    have hne : decodeFullArray p h a i ≠ none := decodeFullArray_ne_none p h xs a i hmem
    cases ho : decodeFullArray p h a i with
    | none => exact False.elim (hne ho)
    | some pr =>
        rcases pr with ⟨ys, j'⟩
        have hys : (ys, []) ∈ decodeRepeat p h (a.toList.drop i) ∧ j' = a.size :=
          decodeFullArray_some p h ys a i j' ho
        have hxy : ys = xs := huniq hys.1 hmem
        subst ys
        have hj' : j' = a.size := hys.2
        subst j'
        rfl

end Codec
