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

The full-consumption repetition `decodeFullByteArray` is likewise **native**: a
`WellFounded.fix` on the remaining length `a.size - i`, threading one
`Option (List α × Nat)` and reading `a[i]`, not `decodeFull` over `a.data.toList.drop i`.
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

/-! ## The native full-consumption repetition decoder -/

/-- The productivity/bounds bridge: a step result `(x, m)` of the native decoder
consumes `0 < m` bytes and stays in bounds `i + m ≤ a.size`. -/
theorem decodeByteArrayRel_pos {α : Type} (p : Codec α) (h : ConsumesByte p) (a : ByteArray) (i : Nat) (x : α) (m : Nat) :
    (x, m) ∈ decodeByteArrayRel p a i → 0 < m := by
  intro hmem
  rw [decodeByteArrayRel_eq] at hmem
  rw [decodeArrayRel_eq] at hmem
  rw [List.mem_map] at hmem
  rcases hmem with ⟨pr, hpr, heq⟩
  rcases pr with ⟨x', r⟩
  have hx : x' = x := congrArg Prod.fst heq
  have hm : (a.data.toList.drop i).length - r.length = m := congrArg Prod.snd heq
  subst x'
  have hlt : r.length < (a.data.toList.drop i).length := h x r (a.data.toList.drop i) hpr
  rw [← hm]
  omega

/-- A step result `(x, m)` never overruns the buffer: `m ≤ a.size - i`. -/
theorem decodeByteArrayRel_le_size {α : Type} (p : Codec α) (a : ByteArray) (i : Nat) (x : α) (m : Nat) :
    (x, m) ∈ decodeByteArrayRel p a i → m ≤ a.size - i := by
  intro hmem
  rw [decodeByteArrayRel_eq] at hmem
  rw [decodeArrayRel_eq] at hmem
  rw [List.mem_map] at hmem
  rcases hmem with ⟨pr, hpr, heq⟩
  rcases pr with ⟨x', r⟩
  have hm : (a.data.toList.drop i).length - r.length = m := congrArg Prod.snd heq
  rw [← hm]
  rw [List.length_drop]
  have hsize : a.data.toList.length = a.size := rfl
  rw [hsize]
  omega

/-- The well-foundedness witness for the native full-consumption recursion. -/
theorem decodeByteArrayRel_bounds {α : Type} (p : Codec α) (h : ConsumesByte p) (a : ByteArray) (i : Nat) (x : α) (m : Nat) :
    (x, m) ∈ decodeByteArrayRel p a i → 0 < m ∧ i + m ≤ a.size := by
  intro hmem
  exact ⟨decodeByteArrayRel_pos p h a i x m hmem, by
      have hmle := decodeByteArrayRel_le_size p a i x m hmem
      have hpos := decodeByteArrayRel_pos p h a i x m hmem
      omega⟩

/-- The well-foundedness witness for the recursion step: from a candidate
`(x, m) ∈ decodeByteArrayRel p a i` (with `p` productive), the remaining length
`a.size - (i + m)` is strictly below `a.size - i`. -/
theorem decodeFullByteArray_lt {α : Type} (p : Codec α) (h : ConsumesByte p) (a : ByteArray) (i : Nat)
    (x : α) (m : Nat) (hm : (x, m) ∈ decodeByteArrayRel p a i) :
    InvImage (· < ·) (fun j : Nat => a.size - j) (i + m) i := by
  have hb := decodeByteArrayRel_bounds p h a i x m hm
  rcases hb with ⟨_hm_pos, hm_le⟩
  change a.size - (i + m) < a.size - i
  omega

/-- The native full-consumption step: thread the `attach`-ed candidate steps,
picking the first whose strictly-shorter recursion yields a full consumption. -/
def decodeFullByteArrayStep {α : Type} (p : Codec α) (h : ConsumesByte p) (a : ByteArray) (i : Nat)
    (ih : (j : Nat) → InvImage (· < ·) (fun j => a.size - j) j i → Option (List α × Nat)) :
    List { pr : α × Nat // pr ∈ decodeByteArrayRel p a i } → Option (List α × Nat)
  | [] => none
  | ⟨(x, m), hm⟩ :: rest =>
      match ih (i + m) (decodeFullByteArray_lt p h a i x m hm) with
      | none => decodeFullByteArrayStep p h a i ih rest
      | some (xs, j) => some (x :: xs, j)

/-- The native full-consumption repetition decoder: `some (xs, j)` iff the
productive `p` fully consumes the remaining bytes of `a` from index `i` as the list
`xs`, ending at `j = a.size`. A `WellFounded.fix` on the remaining length
`a.size - i`, reading `a[i]` — the index mirror of `decodeFull`. Total and
`#eval`-able for productive `p`. -/
def decodeFullByteArray {α : Type} (p : Codec α) (h : ConsumesByte p) (a : ByteArray) (i : Nat) :
    Option (List α × Nat) :=
  WellFounded.fix (InvImage.wf (fun j : Nat => a.size - j) Nat.lt_wfRel.wf)
    (fun i ih =>
      if _hge : a.size ≤ i then some ([], a.size)
      else decodeFullByteArrayStep p h a i ih (decodeByteArrayRel p a i).attach)
    i

/-! ## The native full-consumption spec proof

The native `decodeFullByteArray` is the `WellFounded.fix` mirror of `decodeFull`
over the index measure `a.size - i`. Its full-consumption law `decodeFullByteArray_spec`
closes by the same `WellFounded.induction` + step-correspondence machinery.
The candidate correspondence threads `decodeByteArrayRel p a i` (relative-consumed
`Nat`) against `decode p (a.data.toList.drop i)` (remainder `Bytes`) through the
`decodeByteArrayRel_eq`/`decodeArrayRel_eq` refinement. -/

/-- A candidate `(x, m) ∈ decodeByteArrayRel p a i` corresponds to a result
`(x, drop (i + m)) ∈ decode p (drop i)` — the `m` bytes consumed relative to `i`
are exactly the `m`-length prefix dropped from the list spec. -/
theorem mem_decodeByteArrayRel_to_decode {α : Type} (p : Codec α) (a : ByteArray) (i m : Nat) (x : α)
    (hm : (x, m) ∈ decodeByteArrayRel p a i) :
    ((x, a.data.toList.drop (i + m)) ∈ decode p (a.data.toList.drop i)) := by
  rw [decodeByteArrayRel_eq, decodeArrayRel_eq] at hm
  rw [List.mem_map] at hm
  rcases hm with ⟨pr, hpr, heq⟩
  rcases pr with ⟨x', r⟩
  have hx : x' = x := congrArg Prod.fst heq
  have hm' : (a.data.toList.drop i).length - r.length = m := congrArg Prod.snd heq
  subst x'
  have hsuffix := decode_suffix p x (a.data.toList.drop i) r hpr
  rcases hsuffix with ⟨q, hq⟩
  have hqlen : q.length = m := by
    have hlen := congrArg List.length hq
    rw [List.length_append] at hlen
    have : q.length = (a.data.toList.drop i).length - r.length := by omega
    rw [this]
    exact hm'
  have hr : r = a.data.toList.drop (i + m) := by
    have hdrop : a.data.toList.drop (i + q.length) = r := drop_add_length_of_append hq
    rw [hqlen] at hdrop
    exact hdrop.symm
  rw [← hr]
  exact hpr

/-- The reverse candidate correspondence: a result `(x, s₁) ∈ decode p (drop i)`
maps to `(x, (drop i).length - s₁.length) ∈ decodeByteArrayRel p a i`. -/
theorem mem_decodeByteArrayRel_of_decode {α : Type} (p : Codec α) (a : ByteArray) (i : Nat)
    (x : α) (s₁ : Bytes) (hm : (x, s₁) ∈ decode p (a.data.toList.drop i)) :
    (x, (a.data.toList.drop i).length - s₁.length) ∈ decodeByteArrayRel p a i := by
  rw [decodeByteArrayRel_eq, decodeArrayRel_eq]
  rw [List.mem_map]
  refine ⟨(x, s₁), hm, rfl⟩

/-- The suffix `s₁` of `drop i` (from a decode step) is exactly `drop (i+m)` for
`m = (drop i).length - s₁.length`. -/
theorem drop_of_mem_decode_byteArray {α : Type} (p : Codec α) (a : ByteArray) (i : Nat)
    (x : α) (s₁ : Bytes) (hm : (x, s₁) ∈ decode p (a.data.toList.drop i)) :
    a.data.toList.drop (i + ((a.data.toList.drop i).length - s₁.length)) = s₁ := by
  have hsuffix := decode_suffix p x (a.data.toList.drop i) s₁ hm
  rcases hsuffix with ⟨q, hq⟩
  have hqd : a.data.toList.drop (i + q.length) = s₁ := drop_add_length_of_append hq
  have hqlen : q.length = (a.data.toList.drop i).length - s₁.length := by
    have hlen := congrArg List.length hq
    rw [List.length_append] at hlen
    omega
  rw [hqlen] at hqd
  exact hqd

/-- Forward soundness of the native step: if it returns `some (ys, j)`, then
`ys = x :: xs` for some attached candidate `⟨(x, m), hm⟩` with a fully-consuming
recursion `ih (i+m) … = some (xs, j)`. The index mirror of `decodeFullStep_some`. -/
theorem decodeFullByteArrayStep_some {α : Type} (p : Codec α) (h : ConsumesByte p)
    (a : ByteArray) (i : Nat)
    (ih : (j : Nat) → InvImage (· < ·) (fun j => a.size - j) j i → Option (List α × Nat)) :
    ∀ (l : List { pr : α × Nat // pr ∈ decodeByteArrayRel p a i }) (ys : List α) (j : Nat),
      decodeFullByteArrayStep p h a i ih l = some (ys, j) →
        ∃ (x : α) (xs : List α) (m : Nat) (hm : (x, m) ∈ decodeByteArrayRel p a i),
          ⟨(x, m), hm⟩ ∈ l ∧
            ih (i + m) (decodeFullByteArray_lt p h a i x m hm) = some (xs, j) ∧ ys = x :: xs := by
  intro l ys j
  induction l generalizing ys j with
  | nil => simp [decodeFullByteArrayStep]
  | cons hd tl ihL =>
      rcases hd with ⟨⟨x, m⟩, hm⟩
      rw [decodeFullByteArrayStep]
      cases ho : ih (i + m) (decodeFullByteArray_lt p h a i x m hm) with
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

/-- **Forward soundness** of the native full-consumption decoder: if
`decodeFullByteArray p h a i = some (xs, j)`, then `xs` is a full-consumption result
of `decodeRepeat` over `drop i`, ending at `j = a.size`. Proved by well-founded
induction on `a.size - i`, threading through `decodeFullByteArrayStep_some` and the
candidate correspondence. -/
theorem decodeFullByteArray_some {α : Type} (p : Codec α) (h : ConsumesByte p) :
    ∀ (xs : List α) (a : ByteArray) (i : Nat) (j : Nat),
      decodeFullByteArray p h a i = some (xs, j) →
        (xs, []) ∈ decodeRepeat p h (a.data.toList.drop i) ∧ j = a.size := by
  intro xs a i j
  revert xs j
  induction i using WellFounded.induction
      (hwf := InvImage.wf (fun j : Nat => a.size - j) Nat.lt_wfRel.wf) with
  | h i ih =>
      intro xs j he
      have hfix : decodeFullByteArray p h a i = some (xs, j) := he
      unfold decodeFullByteArray at hfix
      rw [WellFounded.fix_eq] at hfix
      by_cases hge : a.size ≤ i
      · have hdrop : a.data.toList.drop i = [] := List.drop_eq_nil_of_le (by simpa using hge)
        simp [hge] at hfix
        rcases hfix with ⟨rfl, rfl⟩
        constructor
        · rw [hdrop, decodeRepeat_eq]
          simp
        · rfl
      · have hlt : i < a.size := Nat.lt_of_not_ge hge
        simp [hge] at hfix
        rcases (decodeFullByteArrayStep_some p h a i (fun j _hlt => decodeFullByteArray p h a j)
            (decodeByteArrayRel p a i).attach xs j hfix) with ⟨x, xs', m, hm, hmem, hih', hxs⟩
        subst xs
        constructor
        · rw [decodeRepeat_eq, List.mem_cons]
          right
          have hcorr : (x, a.data.toList.drop (i + m)) ∈ decode p (a.data.toList.drop i) :=
            mem_decodeByteArrayRel_to_decode p a i m x hm
          rw [List.mem_flatMap]
          refine ⟨⟨(x, a.data.toList.drop (i + m)), hcorr⟩, ?_, ?_⟩
          · exact List.mem_attach (decode p (a.data.toList.drop i)) ⟨(x, a.data.toList.drop (i + m)), hcorr⟩
          · rw [List.mem_map]
            refine ⟨(xs', []), ?_, rfl⟩
            exact (ih (i + m) (decodeFullByteArray_lt p h a i x m hm) xs' j hih').1
        · exact (ih (i + m) (decodeFullByteArray_lt p h a i x m hm) xs' j hih').2

/-- Completeness of the native step: succeeds whenever some candidate has a
fully-consuming recursion. The index mirror of `decodeFullStep_ne_none`. -/
theorem decodeFullByteArrayStep_ne_none {α : Type} (p : Codec α) (h : ConsumesByte p)
    (a : ByteArray) (i : Nat)
    (ih : (j : Nat) → InvImage (· < ·) (fun j => a.size - j) j i → Option (List α × Nat)) :
    ∀ (l : List { pr : α × Nat // pr ∈ decodeByteArrayRel p a i }),
      (∃ (x : α) (pr : List α × Nat) (m : Nat) (hm : (x, m) ∈ decodeByteArrayRel p a i),
        ⟨(x, m), hm⟩ ∈ l ∧ ih (i + m) (decodeFullByteArray_lt p h a i x m hm) = some pr) →
      decodeFullByteArrayStep p h a i ih l ≠ none := by
  intro l
  induction l with
  | nil =>
      intro hnone
      rcases hnone with ⟨x, pr, m, hm, hmem, _⟩
      cases hmem
  | cons hd tl ihL =>
      rcases hd with ⟨⟨x, m⟩, hm⟩
      intro hex
      rw [decodeFullByteArrayStep]
      cases ho : ih (i + m) (decodeFullByteArray_lt p h a i x m hm) with
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

/-- **Completeness** of the native full-consumption decoder: if `xs` is a
full-consumption result of `decodeRepeat` over `drop i`, then `decodeFullByteArray`
succeeds (`≠ none`). -/
theorem decodeFullByteArray_ne_none {α : Type} (p : Codec α) (h : ConsumesByte p) :
    ∀ (xs : List α) (a : ByteArray) (i : Nat),
      (xs, []) ∈ decodeRepeat p h (a.data.toList.drop i) → decodeFullByteArray p h a i ≠ none := by
  intro xs a i
  revert xs
  induction i using WellFounded.induction
      (hwf := InvImage.wf (fun j : Nat => a.size - j) Nat.lt_wfRel.wf) with
  | h i ih =>
      intro xs hmem
      unfold decodeFullByteArray
      rw [WellFounded.fix_eq]
      by_cases hge : a.size ≤ i
      · simp [hge]
      · have hlt : i < a.size := Nat.lt_of_not_ge hge
        simp [hge]
        rw [decodeRepeat_eq] at hmem
        rw [List.mem_cons] at hmem
        rcases hmem with hmem | hmem
        · have hdr : a.data.toList.drop i = [] :=
            (congrArg Prod.snd hmem).symm
          have hlen0 : (a.data.toList.drop i).length = 0 := by rw [hdr]; rfl
          have : a.size - i = 0 := by simpa using hlen0
          omega
        · rw [List.mem_flatMap] at hmem
          rcases hmem with ⟨a', ha', hres⟩
          rcases a' with ⟨⟨x, s₁⟩, hm⟩
          rw [List.mem_map] at hres
          rcases hres with ⟨pr, hpr, hprmap⟩
          rcases pr with ⟨xs', r⟩
          cases hprmap
          let m := (a.data.toList.drop i).length - s₁.length
          have hmba : (x, m) ∈ decodeByteArrayRel p a i := mem_decodeByteArrayRel_of_decode p a i x s₁ hm
          have hsdrop : a.data.toList.drop (i + m) = s₁ := drop_of_mem_decode_byteArray p a i x s₁ hm
          have hltstep := decodeFullByteArray_lt p h a i x m hmba
          have hne_s₁ : decodeFullByteArray p h a (i + m) ≠ none := by
            have : (xs', []) ∈ decodeRepeat p h (a.data.toList.drop (i + m)) := by
              rw [hsdrop]
              exact hpr
            exact ih (i + m) hltstep xs' this
          cases ho : decodeFullByteArray p h a (i + m) with
          | none => exact False.elim (hne_s₁ ho)
          | some pr =>
              apply decodeFullByteArrayStep_ne_none p h a i
                (fun j _hlt => decodeFullByteArray p h a j) (decodeByteArrayRel p a i).attach
              refine ⟨x, pr, m, hmba, ?_, ?_⟩
              · exact List.mem_attach (decodeByteArrayRel p a i) ⟨(x, m), hmba⟩
              · rw [ho]

/-- The full-consumption law for the native `ByteArray` carrier: `decodeFullByteArray
p h a i = some (xs, j)` iff `xs` is the (unique, under `huniq`) list that fully
consumes `drop i` via `decodeRepeat`, ending at `j = a.size`. The index mirror of
`decodeFull_spec`, with the same uniqueness hypothesis. -/
theorem decodeFullByteArray_spec {α : Type} (p : Codec α) (h : ConsumesByte p)
    (huniq : ∀ {x y : List α} {s : Bytes},
      (x, []) ∈ decodeRepeat p h s → (y, []) ∈ decodeRepeat p h s → x = y)
    (a : ByteArray) (i : Nat) (xs : List α) (j : Nat) :
    decodeFullByteArray p h a i = some (xs, j) ↔
      (xs, []) ∈ decodeRepeat p h (a.data.toList.drop i) ∧ j = a.size := by
  constructor
  · exact decodeFullByteArray_some p h xs a i j
  · intro hmemj
    rcases hmemj with ⟨hmem, hj⟩
    subst j
    have hne : decodeFullByteArray p h a i ≠ none := decodeFullByteArray_ne_none p h xs a i hmem
    cases ho : decodeFullByteArray p h a i with
    | none => exact False.elim (hne ho)
    | some pr =>
        rcases pr with ⟨ys, j'⟩
        have hys : (ys, []) ∈ decodeRepeat p h (a.data.toList.drop i) ∧ j' = a.size :=
          decodeFullByteArray_some p h ys a i j' ho
        have hxy : ys = xs := huniq hys.1 hmem
        subst ys
        have hj' : j' = a.size := hys.2
        subst j'
        rfl

end Codec
