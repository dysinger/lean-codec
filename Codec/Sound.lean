/- Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later -/

import Codec.Decode
import Codec.Encode

/-!
# Soundness: the roundtrip and bidirectional laws

The theorems that make "one description, two directions" precise, now over the
paper's **nondeterministic** decoding relation (see `Codec.Decode`):

  * `encode_rel` — encoder soundness: `encode d x = some s → Rel d x s`
    (hypothesis-free, inductive on `d`).
  * `decode_spec` — the bidirectional law: `(x, r) ∈ decode d s ↔ ∃ s₀,
    s = s₀ ++ r ∧ Rel d x s₀`. Soundness (→) and completeness (←) of the
    list decoder w.r.t. `Rel`.
  * `bidir` — the `r = []` case: `Rel d x s ↔ (x, []) ∈ decode d s`.
  * `decode_encode` — the strong invariant: `encode d x = some s →
    (x, r) ∈ decode d (s ++ r)`.
  * `roundtrip` — `encode d x = some s → (x, []) ∈ decode d s`.

All of these hold **unconditionally** (no `NoAlt`, no `Disjoint`, no
prefix-disjointness). They are the point of the backtracking-union semantics:
`Rel (d₁ | d₂) = Rel d₁ ∨ Rel d₂` and `decode (d₁ | d₂) = decode d₁ ++ decode d₂`
agree by construction, so the committed-choice `alt` gate — and the
prefix-disjointness machinery it required — is unnecessary and has been dropped.
-/

namespace Codec

/-- Encoder soundness: any value the encoder prints is in the description's
denotational domain (`Rel d x s`). Inductive on `d`, no hypothesis. -/
theorem encode_rel {α : Type} (d : Codec α) (x : α) :
    ∀ {s : List UInt8}, encode d x = some s → Rel d x s := by
  induction d with
  | iso i d ih =>
      intro s he
      cases hua : i.unapply x with
      | none => simp [encode, hua] at he
      | some a =>
          have hs : encode d a = some s := by simpa [encode, hua] using he
          have hia : i.apply a = some x := (i.law a x).2 hua
          exact ⟨a, hia, ih a hs⟩
  | seq d₁ d₂ ih₁ ih₂ =>
      intro s he
      rcases x with ⟨x₁, x₂⟩
      cases h₁ : encode d₁ x₁ with
      | none => simp [encode, h₁] at he
      | some s₁ =>
          cases h₂ : encode d₂ x₂ with
          | none => simp [encode, h₁, h₂] at he
          | some s₂ =>
              have hs : s₁ ++ s₂ = s := by simpa [encode, h₁, h₂] using he
              rw [hs.symm]
              exact ⟨s₁, s₂, rfl, ih₁ x₁ h₁, ih₂ x₂ h₂⟩
  | alt d₁ d₂ ih₁ ih₂ =>
      intro s he
      cases h₁ : encode d₁ x with
      | some s₁ =>
          have hs : s₁ = s := by simpa [encode, h₁] using he
          subst s₁
          exact Or.inl (ih₁ x h₁)
      | none =>
          have he' : encode d₂ x = some s := by simpa [encode, h₁] using he
          exact Or.inr (ih₂ x he')
  | empty =>
      intro s he
      simp [encode] at he
  | pure x₀ =>
      intro s he
      by_cases hx : x = x₀
      · subst x
        have hs : s = [] := by simpa [encode] using he
        subst s
        simp [Rel]
      · simp [encode, hx] at he
  | byte =>
      intro s he
      have hs : single x = s := by simpa [encode] using he
      subst s
      rw [Rel_byte]

/-- The sequential decoder threads the remaining bytes: `((x, y), r)` is a result
of `seq d₁ d₂` exactly when `(x, t)` is a result of `d₁` and `(y, r)` of `d₂`
on the leftover `t`. (Membership lemma for the `seq` case of `decode_spec`.) -/
theorem decode_seq_mem {α β : Type} (d₁ : Codec α) (d₂ : Codec β) (x : α × β)
    (s r : List UInt8) :
    (x, r) ∈ decode (Codec.seq d₁ d₂) s ↔
      ∃ t, (x.1, t) ∈ decode d₁ s ∧ (x.2, r) ∈ decode d₂ t := by
  rcases x with ⟨x₁, x₂⟩
  rw [decode]
  rw [List.mem_flatMap]
  constructor
  · intro h
    rcases h with ⟨ab, hab, hm⟩
    rcases ab with ⟨a, t⟩
    rw [List.mem_flatMap] at hm
    rcases hm with ⟨ys, hys, hsing⟩
    rcases ys with ⟨y, s₂⟩
    rw [List.mem_singleton] at hsing
    cases hsing
    exact ⟨t, hab, hys⟩
  · intro h
    rcases h with ⟨t, hd₁, hd₂⟩
    refine ⟨(x₁, t), hd₁, ?_⟩
    rw [List.mem_flatMap]
    refine ⟨(x₂, r), hd₂, ?_⟩
    rw [List.mem_singleton]

/-- The bidirectional law: decoding yields `x` with exactly `r` remaining iff the
input splits as a relating prefix plus `r`. Unconditional — soundness and
completeness of the *nondeterministic* decoder against `Rel`, for every
description. -/
theorem decode_spec {α : Type} (d : Codec α) (x : α) :
    ∀ {s r : List UInt8}, (x, r) ∈ decode d s ↔
      ∃ s₀, s = s₀ ++ r ∧ Rel d x s₀ := by
  induction d with
  | iso i d ih =>
      intro s r
      rw [decode, List.mem_filterMap]
      constructor
      · intro h
        rcases h with ⟨a, ha, hf⟩
        rcases a with ⟨a₀, s'⟩
        cases hia : i.apply a₀ with
        | none => simp [hia] at hf
        | some y =>
            simp [hia] at hf
            rcases hf with ⟨rfl, hs'r⟩
            subst s'
            rcases (ih a₀).1 ha with ⟨s₀, hs, hrel⟩
            exact ⟨s₀, hs, a₀, hia, hrel⟩
      · intro h
        rcases h with ⟨s₀, hs, a₀, hia, hrel⟩
        refine ⟨(a₀, r), ?_, ?_⟩
        · exact (ih a₀).2 ⟨s₀, hs, hrel⟩
        · simp [hia]
  | seq d₁ d₂ ih₁ ih₂ =>
      intro s r
      rw [decode_seq_mem]
      constructor
      · intro h
        rcases h with ⟨t, hd₁, hd₂⟩
        rcases (ih₁ x.1).1 hd₁ with ⟨s₁, hs₁, hrel₁⟩
        rcases (ih₂ x.2).1 hd₂ with ⟨s₂, hs₂, hrel₂⟩
        refine ⟨s₁ ++ s₂, ?_, s₁, s₂, rfl, hrel₁, hrel₂⟩
        rw [hs₁, hs₂]
        simp [List.append_assoc]
      · intro h
        rcases h with ⟨s₀, hs, s₁, s₂, hs₀, hrel₁, hrel₂⟩
        refine ⟨s₂ ++ r, ?_, ?_⟩
        · exact (ih₁ x.1).2 ⟨s₁, by rw [hs, hs₀, List.append_assoc], hrel₁⟩
        · exact (ih₂ x.2).2 ⟨s₂, rfl, hrel₂⟩
  | alt d₁ d₂ ih₁ ih₂ =>
      intro s r
      rw [decode, List.mem_append]
      constructor
      · intro h
        rcases h with hl | hr
        · rcases (ih₁ x).1 hl with ⟨s₀, hs, hrel⟩
          exact ⟨s₀, hs, Or.inl hrel⟩
        · rcases (ih₂ x).1 hr with ⟨s₀, hs, hrel⟩
          exact ⟨s₀, hs, Or.inr hrel⟩
      · intro h
        rcases h with ⟨s₀, hs, hrel⟩
        rcases hrel with hl | hr
        · exact Or.inl ((ih₁ x).2 ⟨s₀, hs, hl⟩)
        · exact Or.inr ((ih₂ x).2 ⟨s₀, hs, hr⟩)
  | empty =>
      intro s r
      simp [decode, Rel]
  | pure x₀ =>
      intro s r
      simp [decode, Rel]
      constructor
      · rintro ⟨hx, hr⟩; exact ⟨hr.symm, hx⟩
      · rintro ⟨hsr, hx⟩; exact ⟨hx, hsr.symm⟩
  | byte =>
      intro s r
      cases s with
      | nil =>
          simp [decode, Rel, single]
      | cons b bs =>
          simp [decode, Rel, single]
          constructor
          · rintro ⟨hxb, hr⟩; exact ⟨hxb.symm, hr.symm⟩
          · rintro ⟨hbx, hbs⟩; exact ⟨hbx.symm, hbs.symm⟩

/-- The bidirectional law over whole strings (the `r = []` case of
`decode_spec`): `Rel d x s` holds exactly when the nondeterministic decoder
accepts `s` fully as `x`. Unconditional. -/
theorem bidir {α : Type} (d : Codec α) (x : α) (s : List UInt8) :
    Rel d x s ↔ (x, []) ∈ decode d s := by
  have hspec := decode_spec d x (s := s) (r := [])
  constructor
  · intro hr
    exact hspec.2 ⟨s, by simp, hr⟩
  · intro hd
    rcases hspec.1 hd with ⟨s₀, hs, hr⟩
    simpa [hs] using hr

/-- The strong roundtrip invariant: a value encoded to `s` decodes back to
`(x, r)` (with `x` fully consumed and `r` left over) from any suffixing input
`s ++ r`. Unconditional. -/
theorem decode_encode {α : Type} (d : Codec α) (x : α) :
    ∀ {s : List UInt8}, encode d x = some s → ∀ r, (x, r) ∈ decode d (s ++ r) := by
  intro s he r
  have hrel : Rel d x s := encode_rel d x he
  exact (decode_spec d x (s := s ++ r) (r := r)).2 ⟨s, rfl, hrel⟩

/-- The byte-exact roundtrip: a value encoded to `s` decodes back to `x` with
no remainder. Unconditional. -/
theorem roundtrip {α : Type} (d : Codec α) (x : α) (s : List UInt8) :
    encode d x = some s → (x, []) ∈ decode d s := by
  intro he
  simpa using (decode_encode d x he [])

/-! ## Repetition: the totality boundary and the decoder law

These complete the *computable* reading of the derived `many` combinator. Its
denotation is the least fixpoint `relRepeat (Rel p)` (see `Codec.Codec`); its
decoder is `decodeRepeat` (see `Codec.Decode`), well-founded on `s.length`.
The `many`-case law is `decodeRepeat_spec`, and the totality boundary is
`productive_iff_consumesByte` — both unconditional. -/

/-- The totality boundary: `decode p` strictly shortens the input exactly when
`p` is productive (every value it relates sits on a non-empty string). This is
the theorem that makes `decodeRepeat p h` a *total* function for productive `p`
and locates the genuine non-totality (empty-matching `p`, e.g. `pure ()`) as the
only case where no such witness `h` exists. -/
theorem productive_iff_consumesByte {α : Type} (p : Codec α) :
    Productive p ↔ ConsumesByte p := by
  constructor
  · intro hprod x s₁ s₀ hmem
    rcases (decode_spec p x).1 hmem with ⟨s₀', hs, hrel⟩
    have hs₀' : s₀' ≠ [] := hprod x s₀' hrel
    rw [hs]
    cases s₀' with
    | nil => contradiction
    | cons b rest => simp; omega
  · intro hcons x s hrel
    intro hs
    subst s
    have hmem : (x, []) ∈ decode p [] := (bidir p x []).1 hrel
    have hlt : [].length < [].length := hcons x [] [] hmem
    simp at hlt

/-- The `many`-case of the bidirectional law (the analogue of `decode_spec` for
the derived repetition combinator): `(xs, r) ∈ decodeRepeat p h s` exactly when
the input splits as a `relRepeat`-prefix plus `r`. Proved by well-founded
induction on `s.length` — the same measure that makes `decodeRepeat` terminate. -/
theorem decodeRepeat_spec {α : Type} (p : Codec α) (h : ConsumesByte p) :
    ∀ (xs : List α) (s r : List UInt8), (xs, r) ∈ decodeRepeat p h s ↔
      ∃ s₀, s = s₀ ++ r ∧ relRepeat (Rel p) xs s₀ := by
  have hwf : WellFounded (InvImage (· < ·) (fun s : List UInt8 => s.length)) :=
    InvImage.wf (fun s : List UInt8 => s.length) Nat.lt_wfRel.wf
  intro xs s r
  revert xs r
  induction s using WellFounded.induction (hwf := hwf) with
  | h s ih =>
      intro xs r
      rw [decodeRepeat_eq]
      rw [List.mem_cons]
      constructor
      · intro hm
        rcases hm with hm | hm
        · cases hm
          refine ⟨[], ?_, ?_⟩
          · simp
          · simp [relRepeat]
        · rw [List.mem_flatMap] at hm
          rcases hm with ⟨a, _ha_mem, hm_in_map⟩
          rcases a with ⟨ab, hmem⟩
          rcases ab with ⟨x, s₁⟩
          rw [List.mem_map] at hm_in_map
          rcases hm_in_map with ⟨pr, hpr, hprmap⟩
          rcases pr with ⟨xs', r'⟩
          cases hprmap
          have hlt : InvImage (· < ·) (fun s : List UInt8 => s.length) s₁ s := h x s₁ s hmem
          rcases (ih s₁ hlt xs' r).1 hpr with ⟨s₀', hs₁, hrel'⟩
          rcases (decode_spec p x).1 hmem with ⟨s₀'', hs, hrelx⟩
          refine ⟨s₀'' ++ s₀', ?_, ?_⟩
          · rw [hs, hs₁]
            simp [List.append_assoc]
          · rw [relRepeat_cons]
            exact ⟨s₀'', s₀', rfl, hrelx, hrel'⟩
      · intro hm
        rcases hm with ⟨s₀, hs, hrel⟩
        cases xs with
        | nil =>
            simp [relRepeat] at hrel
            subst s₀
            rw [hs]
            left
            rfl
        | cons x xs' =>
            rw [relRepeat_cons] at hrel
            rcases hrel with ⟨sa, sb, hs₀, hrelx, hrel'⟩
            right
            rw [List.mem_flatMap]
            have hmem : (x, sb ++ r) ∈ decode p s := by
              rw [hs, hs₀]
              exact (decode_spec p x).2 ⟨sa, by simp [List.append_assoc], hrelx⟩
            refine ⟨⟨(x, sb ++ r), hmem⟩, ?_, ?_⟩
            · simp [List.mem_attach]
            · rw [List.mem_map]
              refine ⟨(xs', r), ?_, by rfl⟩
              have hlt : InvImage (· < ·) (fun s : List UInt8 => s.length) (sb ++ r) s :=
                h x (sb ++ r) s hmem
              exact (ih (sb ++ r) hlt xs' r).2 ⟨sb, rfl, hrel'⟩

/-- The contrapositive statement concretized: when a step `p` matches the empty
string (`Rel p x []` for some `x`), repetition has *arbitrarily many* results —
for every `n` the `n`-fold list `replicate n x` relates to the empty string. So
no strict-`List` decoder can enumerate them all (the results are unbounded),
which is why `decodeRepeat` is only total for *productive* `p` (see
`productive_iff_consumesByte`). A lemma, not a gate. -/
theorem relRepeat_unbounded_of_empty {α : Type} (p : Codec α) (x : α) (hx : Rel p x []) :
    ∀ n : Nat, relRepeat (Rel p) (List.replicate n x) [] := by
  intro n
  induction n with
  | zero => simp [relRepeat]
  | succ n ih =>
      change relRepeat (Rel p) (x :: List.replicate n x) []
      rw [relRepeat_cons]
      exact ⟨[], [], rfl, hx, ih⟩

/-- The canonical empty-matching description: `pure x` relates `x` to `[]`, so it
is *not* productive — there is no `ConsumesByte (pure x)` witness, hence no
total `decodeRepeat (pure x) _`. This is the (constructively stated) reason
`decode (many (pure ())) []` is genuinely infinite, never faked with a finite
result. -/
theorem not_productive_pure {α : Type} [DecidableEq α] (x : α) :
    ¬ Productive (Codec.pure x : Codec α) := by
  intro hp
  have hrel : Rel (Codec.pure x : Codec α) x [] := by simp [Rel]
  have h := hp x [] hrel
  exact (h rfl)

end Codec
