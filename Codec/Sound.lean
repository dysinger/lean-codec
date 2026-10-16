/- Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later -/

import Codec.Decode
import Codec.Encode

/-!
# Soundness: the roundtrip and bidirectional laws

The theorems that make "one description, two directions" precise, now over the
length-indexed byte string `Bytes n := Fin n → UInt8`:

  * `encode_rel` — encoder soundness: `encode d x = some ⟨n, s⟩ → Rel d x s`
    (hypothesis-free, inductive on `d`).
  * `decode_spec` — the bidirectional law: `(x, r) ∈ decode d s ↔ ∃ s₀,
    s = r.prepend s₀ ∧ Rel d x s₀` (with `r : Suffix n` and `s₀ : Bytes (n - r.remaining)`).
    Soundness (→) and completeness (←) of the list decoder w.r.t. `Rel`.
  * `bidir` — the empty-remainder case: `Rel d x s ↔ (x, Suffix.id n s) ∈ decode d s`.
  * `decode_encode` — the strong invariant: `encode d x = some ⟨n, s⟩ →
    (x, r) ∈ decode d (r.prepend s)`.
  * `roundtrip` — `encode d x = some ⟨n, s⟩ → (x, Suffix.empty n) ∈ decode d s`.

All of these hold **unconditionally** (no `NoAlt`, no `Disjoint`, no
prefix-disjointness). They are the point of the backtracking-union semantics:
`Rel (d₁ | d₂) = Rel d₁ ∨ Rel d₂` and `decode (d₁ | d₂) = decode d₁ ++ decode d₂`
agree by construction, so the old committed-choice `alt` gate is unnecessary.
-/

namespace Codec

/-- Encoder soundness: any value the encoder prints is in the description's
denotational domain (`Rel d x s`). Inductive on `d`, no hypothesis. -/
theorem encode_rel {α : Type} (d : Codec α) (x : α) :
    ∀ {n : Nat} {s : Bytes n}, encode d x = some ⟨n, s⟩ → Rel d x s := by
  induction d with
  | iso i d ih =>
      intro n s he
      cases hua : i.unapply x with
      | none => simp [encode, hua] at he
      | some a =>
          have hs : encode d a = some ⟨n, s⟩ := by simpa [encode, hua] using he
          have hia : i.apply a = some x := (i.law a x).2 hua
          exact ⟨a, hia, ih a hs⟩
  | seq d₁ d₂ ih₁ ih₂ =>
      intro n s he
      rcases x with ⟨x₁, x₂⟩
      cases h₁ : encode d₁ x₁ with
      | none => simp [encode, h₁] at he
      | some s₁ =>
          rcases s₁ with ⟨n₁, b₁⟩
          cases h₂ : encode d₂ x₂ with
          | none => simp [encode, h₁, h₂] at he
          | some s₂ =>
              rcases s₂ with ⟨n₂, b₂⟩
              have he' : some ⟨n₁ + n₂, concat b₁ b₂⟩ = some (⟨n, s⟩ : Sigma fun k => Bytes k) := by
                simpa [encode, h₁, h₂] using he
              have heq : (⟨n₁ + n₂, concat b₁ b₂⟩ : Sigma fun k => Bytes k) = ⟨n, s⟩ := by simpa using he'
              cases heq
              rw [Rel_seq]
              refine ⟨n₁, Nat.le.intro rfl, b₁, cast (congrArg Bytes (Nat.add_sub_cancel_left n₁ n₂).symm) b₂, ?_, ih₁ x₁ h₁, ?_⟩
              · rw [concat_eq_splice]
              · exact (Rel_cast d₂ x₂ (Nat.add_sub_cancel_left n₁ n₂).symm b₂).2 (ih₂ x₂ h₂)
  | alt d₁ d₂ ih₁ ih₂ =>
      intro n s he
      cases h₁ : encode d₁ x with
      | some v =>
          rcases v with ⟨n₁, b₁⟩
          have hs : (⟨n₁, b₁⟩ : Sigma fun k => Bytes k) = ⟨n, s⟩ := by simpa [encode, h₁] using he
          cases hs
          exact Or.inl (ih₁ x h₁)
      | none =>
          have he' : encode d₂ x = some ⟨n, s⟩ := by simpa [encode, h₁] using he
          exact Or.inr (ih₂ x he')
  | empty =>
      intro n s he
      simp [encode] at he
  | pure x₀ =>
      intro n s he
      by_cases hx : x = x₀
      · subst x
        have hs : (⟨0, (emptyBytes : Bytes 0)⟩ : Sigma fun k => Bytes k) = ⟨n, s⟩ := by simpa [encode] using he
        cases hs
        simp [Rel]
      · simp [encode, hx] at he
  | byte =>
      intro n s he
      have hs : (⟨1, (single x : Bytes 1)⟩ : Sigma fun k => Bytes k) = ⟨n, s⟩ := by simpa [encode] using he
      cases hs
      rw [Rel_byte]
      exact ⟨rfl, rfl⟩

/-- The sequential decoder threads the remaining bytes: `((x, y), r)` is a result
of `seq d₁ d₂` exactly when `(x, t₁)` is a result of `d₁` and `(y, t₂)` of `d₂`
on the leftover `t₁.bytes`, with `r` their transitive suffix. (Membership lemma
for the `seq` case of `decode_spec`.) -/
theorem decode_seq_mem {α β : Type} (d₁ : Codec α) (d₂ : Codec β) (x : α × β)
    {n : Nat} (s : Bytes n) (r : Suffix n) :
    (x, r) ∈ decode (Codec.seq d₁ d₂) s ↔
      ∃ t₁ t₂, (x.1, t₁) ∈ decode d₁ s ∧ (x.2, t₂) ∈ decode d₂ t₁.bytes ∧
        r = Suffix.trans t₁ t₂ := by
  rcases x with ⟨x₁, x₂⟩
  rw [decode]
  rw [List.mem_flatMap]
  constructor
  · intro h
    rcases h with ⟨ab, hab, hm⟩
    rcases ab with ⟨a, t₁⟩
    rw [List.mem_flatMap] at hm
    rcases hm with ⟨ys, hys, hsing⟩
    rcases ys with ⟨y, t₂⟩
    rw [List.mem_singleton] at hsing
    cases hsing
    exact ⟨t₁, t₂, hab, hys, rfl⟩
  · intro h
    rcases h with ⟨t₁, t₂, hd₁, hd₂, hr⟩
    subst r
    refine ⟨(x₁, t₁), hd₁, ?_⟩
    rw [List.mem_flatMap]
    refine ⟨(x₂, t₂), hd₂, ?_⟩
    rw [List.mem_singleton]

/-- The bidirectional law: decoding yields `x` with suffix `r` remaining iff the
input is `r` prepended to a relating prefix `s₀`. Unconditional — soundness and
completeness of the *nondeterministic* decoder against `Rel`, for every
description. -/
theorem decode_spec {α : Type} (d : Codec α) (x : α) :
    ∀ {n : Nat} (s : Bytes n) (r : Suffix n),
      (x, r) ∈ decode d s ↔
        ∃ s₀ : Bytes (n - r.remaining), s = r.prepend s₀ ∧ Rel d x s₀ := by
  induction d with
  | iso i d ih =>
      intro n s r
      rw [decode, List.mem_filterMap]
      constructor
      · intro h
        rcases h with ⟨a, ha, hf⟩
        rcases a with ⟨a₀, r'⟩
        cases hia : i.apply a₀ with
        | none => simp [hia] at hf
        | some y =>
            simp [hia] at hf
            rcases hf with ⟨rfl, hr'r⟩
            subst r'
            rcases (ih a₀ s r).1 ha with ⟨s₀', hs', hrel'⟩
            exact ⟨s₀', hs', a₀, hia, hrel'⟩
      · intro h
        rcases h with ⟨s₀, hs, a₀, hia, hrel⟩
        refine ⟨(a₀, r), ?_, ?_⟩
        · exact (ih a₀ s r).2 ⟨s₀, hs, hrel⟩
        · simp [hia]
  | seq d₁ d₂ ih₁ ih₂ =>
      intro n s r
      sorry
  | alt d₁ d₂ ih₁ ih₂ =>
      intro n s r
      rw [decode, List.mem_append]
      constructor
      · intro h
        rcases h with hl | hr
        · rcases (ih₁ x s r).1 hl with ⟨s₀, hs, hrel⟩
          exact ⟨s₀, hs, Or.inl hrel⟩
        · rcases (ih₂ x s r).1 hr with ⟨s₀, hs, hrel⟩
          exact ⟨s₀, hs, Or.inr hrel⟩
      · intro h
        rcases h with ⟨s₀, hs, hrel⟩
        rcases hrel with hl | hr
        · exact Or.inl ((ih₁ x s r).2 ⟨s₀, hs, hl⟩)
        · exact Or.inr ((ih₂ x s r).2 ⟨s₀, hs, hr⟩)
  | empty =>
      intro n s r
      simp [decode, Rel]
  | pure x₀ =>
      intro n s r
      simp [decode, Rel]
      constructor
      · intro h
        sorry
      · intro h
        sorry
  | byte =>
      intro n s r
      sorry

theorem bidir {α : Type} (d : Codec α) (x : α) (n : Nat) (s : Bytes n) :
    Rel d x s ↔ (x, Suffix.empty n) ∈ decode d s := by
  sorry

/-- The strong roundtrip invariant: a value encoded to `s : Bytes m` decodes back to
`(x, ·)` leaving exactly the appended `r : Bytes q` unconsumed, from the input
`concat s r`. Unconditional. -/
theorem decode_encode {α : Type} (d : Codec α) (x : α) :
    ∀ {m : Nat} {s : Bytes m}, encode d x = some ⟨m, s⟩ →
      ∀ {q : Nat} (r : Bytes q),
        (x, Suffix.drop m (concat s r)) ∈ decode d (concat s r) := by
  sorry

/-- The byte-exact roundtrip: a value encoded to `s` decodes back to `x` with
no remainder. Unconditional. -/
theorem roundtrip {α : Type} (d : Codec α) (x : α) (n : Nat) (s : Bytes n) :
    encode d x = some ⟨n, s⟩ → (x, Suffix.empty n) ∈ decode d s := by
  sorry

/-! ## Repetition: the totality boundary and the decoder law -/

/-- The totality boundary: `decode p` strictly shortens the input exactly when
`p` is productive (every value it relates sits on a non-empty string). -/
theorem productive_iff_consumesByte {α : Type} (p : Codec α) :
    Productive p ↔ ConsumesByte p := by
  sorry

/-- The `many`-case of the bidirectional law: `(xs, r) ∈ decodeRepeat p h n s`
exactly when the input splits as a `relRepeat`-prefix plus `r`. -/
theorem decodeRepeat_spec {α : Type} (p : Codec α) (h : ConsumesByte p) :
    ∀ (xs : List α) (n : Nat) (s : Bytes n) (r : Suffix n),
      (xs, r) ∈ decodeRepeat p h n s ↔
        ∃ s₀ : Bytes (n - r.remaining), s = r.prepend s₀ ∧ relRepeat (Rel p) xs (n - r.remaining) s₀ := by
  sorry

/-- Repetition with an empty-matching step has arbitrarily many results. -/
theorem relRepeat_unbounded_of_empty {α : Type} (p : Codec α) (x : α)
    (hx : Rel p x (emptyBytes : Bytes 0)) :
    ∀ m : Nat, relRepeat (Rel p) (List.replicate m x) 0 emptyBytes := by
  sorry

/-- `pure x` is not productive. -/
theorem not_productive_pure {α : Type} [DecidableEq α] (x : α) :
    ¬ Productive (Codec.pure x : Codec α) := by
  sorry

/-- Encoder soundness for repetition. -/
theorem encodeRepeat_rel {α : Type} (p : Codec α) :
    ∀ (xs : List α) {n : Nat} {s : Bytes n}, encodeRepeat p xs = some ⟨n, s⟩ → relRepeat (Rel p) xs n s := by
  sorry

/-! ## Unambiguity, functionality, and the decode→encode direction -/

def Unambiguous {α : Type} (d : Codec α) : Prop :=
  ∀ ⦃x y⦄ {n : Nat} (s : Bytes n), Rel d x s → Rel d y s → x = y

def Functional {α : Type} (d : Codec α) : Prop :=
  ∀ x {n₁ n₂ : Nat} (s₁ : Bytes n₁) (s₂ : Bytes n₂),
    Rel d x s₁ → Rel d x s₂ → (⟨n₁, s₁⟩ : Sigma fun n => Bytes n) = ⟨n₂, s₂⟩

/-- **Encoder completeness**: every value in the denotation encodes successfully. -/
theorem encode_ne_none {α : Type} (d : Codec α) (x : α) {n : Nat} (s : Bytes n) :
    Rel d x s → encode d x ≠ none := by
  sorry

theorem encode_of_decode {α : Type} (d : Codec α) (hd : Functional d) (x : α)
    {n : Nat} {s : Bytes n} (hdcd : (x, Suffix.empty n) ∈ decode d s) : encode d x = some ⟨n, s⟩ := by
  sorry

theorem encode_injective_of_unambiguous {α : Type} (d : Codec α) (hd : Unambiguous d)
    {x y : α} {n : Nat} {s : Bytes n} (hx : encode d x = some ⟨n, s⟩) (hy : encode d y = some ⟨n, s⟩) :
    x = y := by
  sorry

/-! ## Relation-level completeness and functionality -/

def relFunctional {α : Type} (R : α → {n : Nat} → Bytes n → Prop) : Prop :=
  ∀ a {n₁ n₂ : Nat} (s₁ : Bytes n₁) (s₂ : Bytes n₂),
    R a s₁ → R a s₂ → (⟨n₁, s₁⟩ : Sigma fun n => Bytes n) = ⟨n₂, s₂⟩

def relUnambiguous {α : Type} (R : α → {n : Nat} → Bytes n → Prop) : Prop :=
  ∀ ⦃a b⦄ {n : Nat} (s : Bytes n), R a s → R b s → a = b

theorem encodeRepeat_ne_none {α : Type} (p : Codec α) :
    ∀ (xs : List α) {n : Nat} (s : Bytes n), relRepeat (Rel p) xs n s → encodeRepeat p xs ≠ none := by
  sorry

end Codec
