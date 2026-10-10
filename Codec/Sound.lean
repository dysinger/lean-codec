/- Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later -/

import Codec.Decode
import Codec.Encode

/-!
# Soundness: the roundtrip law

The theorem that makes "one description, two directions" precise:

  * `decode_encode` — the strong invariant `encode d x = some s → decode d (s ++ r) = .ok (x, r)`.
  * `roundtrip` — `encode d x = some s → decode d s = .ok (x, [])`.

Both hold *unconditionally* for the `alt`-free fragment (`$`, `*`, `empty`,
`pure`, `byte`): encoding then decoding reproduces the value byte-for-byte, with
no "modulo equivalence classes" weakening, because the core has no lossy
`ignore` primitive.

For `alt` (committed choice, a documented departure from the paper's
backtracking — §4.4), the deterministic decoder is sound-and-complete only on
the `Unambiguous` domain; a per-description proof obligation (task 4.3). The
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

end Codec
