/- Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later -/

import Codec.Decode
import Codec.Encode

/-!
# Soundness: the roundtrip law

The theorem that makes "one description, two directions" precise:

  * `decode_encode` — the strong invariant `encode d x = some s → decode d (s ++ r) = .ok (x, r)`.
  * `roundtrip` — `encode d x = some s → decode d s = .ok (x, [])`.
  * `decode_rel` / `bidir` — the bidirectional law relating `decode` to `Rel`.

Both hold *unconditionally* for the `alt`-free fragment (`$`, `*`, `empty`,
`pure`, `byte`): encoding then decoding reproduces the value byte-for-byte, with
no "modulo equivalence classes" weakening, because the core has no lossy
`ignore` primitive.

For `alt` (committed choice, a documented departure from the paper's
backtracking — §4.4), the deterministic decoder is sound-and-complete only on
prefix-disjointness domain not yet formalized (a deferred condition); the
predicate `NoAlt` below singles out the fragment where the laws hold
unconditionally.
-/

namespace Codec

/-- A description is *unambiguous* when every byte string relates to at most one
value. Per-codec proof obligation; the deterministic decoder (committed `|`) is
sound-and-complete on this domain. -/
def Unambiguous {α : Type} (d : Codec α) : Prop :=
  ∀ s x y, Rel d x s → Rel d y s → x = y

/-- `NoAlt d` says the description `d` uses no committed-choice (`alt`)
constructor. On this fragment the roundtrip holds unconditionally. -/
def NoAlt {α : Type} (d : Codec α) : Prop :=
  match d with
  | @Codec.iso _ _ _ d => NoAlt d
  | @Codec.seq _ _ d₁ d₂ => NoAlt d₁ ∧ NoAlt d₂
  | @Codec.alt _ _ _ => False
  | @Codec.empty _ => True
  | @Codec.pure _ _ _ => True
  | @Codec.byte => True

/-- The strong roundtrip invariant, on the `alt`-free fragment. -/
theorem decode_encode {α : Type} (d : Codec α) (x : α) (h : NoAlt d) :
    ∀ {s : List UInt8}, encode d x = some s → ∀ r, decode d (s ++ r) = .ok (x, r) := by
  induction d with
  | iso i d ih =>
      intro s he r
      by_cases hua : i.unapply x = none
      · simp [encode, hua] at he
      · rcases Option.ne_none_iff_exists.mp hua with ⟨a, hua⟩
        have hia : i.apply a = some x := (i.law a x).2 hua.symm
        have hs : encode d a = some s := by simpa [encode, hua.symm] using he
        have hd : decode d (s ++ r) = .ok (a, r) := ih a h hs r
        simp [decode, hd, hia]
  | seq d₁ d₂ ih₁ ih₂ =>
      intro s he r
      rcases x with ⟨x₁, x₂⟩
      rcases h with ⟨hna₁, hna₂⟩
      cases h₁ : encode d₁ x₁ with
      | none => simp [encode, h₁] at he
      | some s₁ =>
          cases h₂ : encode d₂ x₂ with
          | none => simp [encode, h₁, h₂] at he
          | some s₂ =>
              have hs : s₁ ++ s₂ = s := by simpa [encode, h₁, h₂] using he
              subst s
              have hd₂ : decode d₂ (s₂ ++ r) = .ok (x₂, r) := ih₂ x₂ hna₂ h₂ r
              have hd₁ : decode d₁ (s₁ ++ (s₂ ++ r)) = .ok (x₁, s₂ ++ r) := ih₁ x₁ hna₁ h₁ (s₂ ++ r)
              simp [decode, hd₁, hd₂, List.append_assoc]
  | alt d₁ d₂ ih₁ ih₂ =>
      intro s he r
      cases h
  | empty =>
      intro s he r
      simp [encode] at he
  | pure x₀ =>
      intro s he r
      by_cases hx : x = x₀
      · subst x
        have hs : s = [] := by simpa [encode] using he
        subst s
        simp [decode]
      · simp [encode, hx] at he
  | byte =>
      intro s he r
      have hs : single x = s := by simpa [encode] using he
      subst s
      simp [decode, single]

/-- The byte-exact roundtrip on the `alt`-free fragment. -/
theorem roundtrip {α : Type} (d : Codec α) (x : α) (h : NoAlt d) :
    encode d x = some s → decode d s = .ok (x, []) := by
  intro he
  simpa using (decode_encode d x h he [])


/-! ## The bidirectional law -/

/-- The bidirectional law, generalized over the remaining suffix `r`: decoding `s`
yields `x` leaving exactly `r` unconsumed iff `s` splits as a relating prefix plus
`r`. Soundness (→) and completeness (←) of the deterministic decoder w.r.t. `Rel`,
on the `alt`-free (`NoAlt`) fragment. -/
theorem decode_spec {α : Type} (d : Codec α) (x : α) (h : NoAlt d) :
    ∀ {s r : List UInt8}, decode d s = .ok (x, r) ↔
      ∃ s₀, s = s₀ ++ r ∧ Rel d x s₀ := by
  induction d with
  | iso i d ih =>
      intro s r
      constructor
      · intro hd
        cases hd' : decode d s with
        | error e => simp [decode, hd'] at hd
        | ok val =>
            rcases val with ⟨a, s'⟩
            cases hia : i.apply a with
            | none => simp [decode, hd', hia] at hd
            | some y =>
                simp [decode, hd', hia] at hd
                rcases hd with ⟨hyx, hsr⟩
                subst x
                subst s'
                rcases (ih a h).1 hd' with ⟨s₀, hs, hr⟩
                exact ⟨s₀, hs, a, hia, hr⟩
      · intro hd
        rcases hd with ⟨s₀, hs, a, hia, hr⟩
        have hdec : decode d s = .ok (a, r) := (ih a h).2 ⟨s₀, hs, hr⟩
        simp [decode, hdec, hia]
  | seq d₁ d₂ ih₁ ih₂ =>
      intro s r
      rcases x with ⟨x₁, x₂⟩
      constructor
      · intro hd
        cases h₁ : decode d₁ s with
        | error e => simp [decode, h₁] at hd
        | ok val₁ =>
            rcases val₁ with ⟨a, t⟩
            cases h₂ : decode d₂ t with
            | error e => simp [decode, h₁, h₂] at hd
            | ok val₂ =>
                rcases val₂ with ⟨b, r'⟩
                simp [decode, h₁, h₂] at hd
                rcases hd with ⟨⟨hax₁, hbx₂⟩, hr'⟩
                subst a; subst b; subst r'
                rcases (ih₁ x₁ h.1).1 h₁ with ⟨s₁, hs₁, hr₁⟩
                rcases (ih₂ x₂ h.2).1 h₂ with ⟨s₂, hs₂, hr₂⟩
                refine ⟨s₁ ++ s₂, ?_, s₁, s₂, rfl, hr₁, hr₂⟩
                rw [hs₁, hs₂]
                simp [List.append_assoc]
      · intro hd
        rcases hd with ⟨s₀, hs, s₁₀, s₂₀, hs₀, hr₁, hr₂⟩
        have hdec₁ : decode d₁ s = .ok (x₁, s₂₀ ++ r) := by
          rw [hs, hs₀, List.append_assoc]
          exact (ih₁ x₁ h.1).2 ⟨s₁₀, rfl, hr₁⟩
        have hdec₂ : decode d₂ (s₂₀ ++ r) = .ok (x₂, r) :=
          (ih₂ x₂ h.2).2 ⟨s₂₀, rfl, hr₂⟩
        simp [decode, hdec₁, hdec₂]
  | alt d₁ d₂ ih₁ ih₂ =>
      intro s r
      cases h
  | empty =>
      intro s r
      constructor <;> intro hd <;> simp [decode, Rel] at hd
  | pure x₀ =>
      intro s r
      constructor
      · intro hd
        simp [decode] at hd
        rcases hd with ⟨hx₀x, hsr⟩
        refine ⟨[], ?_, hx₀x.symm, rfl⟩
        simpa using hsr
      · intro hd
        rcases hd with ⟨s₀, hs, hx, hs₀⟩
        subst s₀
        rw [hs]
        simp [decode, hx]
  | byte =>
      intro s r
      constructor
      · intro hd
        simp [decode] at hd
        cases s with
        | nil => simp at hd
        | cons b bs =>
            simp [Rel, single] at hd ⊢
            rcases hd with ⟨hb, hbs⟩
            subst b
            subst bs
            exact ⟨rfl, rfl⟩
      · intro hd
        rcases hd with ⟨s₀, hs, hs₀⟩
        simp [Rel, single] at hs₀
        subst s₀
        rw [hs]
        simp [decode]

/-- The bidirectional law relating `decode` and `Rel` over whole strings (the
`r = []` case of `decode_spec`): on the `alt`-free fragment, `Rel d x s` holds
exactly when the deterministic decoder accepts `s` fully as `x`. -/
theorem bidir {α : Type} (d : Codec α) (x : α) (s : List UInt8) (h : NoAlt d) :
    Rel d x s ↔ decode d s = .ok (x, []) := by
  have hspec := decode_spec d x h (s := s) (r := [])
  constructor
  · intro hr
    exact hspec.2 ⟨s, by simp, hr⟩
  · intro hd
    rcases hspec.1 hd with ⟨s₀, hs, hr⟩
    simpa [hs] using hr

end Codec

