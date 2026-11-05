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
  | satisfy p =>
      intro n s he
      by_cases hp : p x
      · have hs : (⟨1, (single x : Bytes 1)⟩ : Sigma fun k => Bytes k) = ⟨n, s⟩ := by simpa [encode, hp] using he
        cases hs
        rw [Rel_satisfy]
        exact ⟨hp, rfl, rfl⟩
      · simp [encode, hp] at he

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

/-! ### `ConsumesByte` for composed codecs

`ConsumesByte` (`Codec.Decode`) is the productivity witness every whole-buffer
decoder takes as a parameter. Until this section it was supplied **only** for
leaves (`byteConsumesByte`, `satisfyConsumesByte`) and — as of the `k > 1` bench
work — for `alt` (`Codec.altConsumesByte`). Nothing derived it for `seq` or `iso`,
so the shape *every real format takes* (a sequence of fields, viewed through an
`Iso`) had no witness at all: a downstream author defining a 2-byte integer as
`iso … (byte * byte)` had to prove productivity by hand.

They live here rather than beside `altConsumesByte` in `Codec/Decode.lean`
because the `seq` case reuses `decode_seq_mem`, which is defined above and is the
membership lemma for `seq`. `Codec/Decode.lean` cannot import `Codec/Sound.lean`
without a cycle.

Both are `[propext, Quot.sound]`-only, zero `sorry`, zero `Classical.choice`. -/

/-- **`seq` of two consumers consumes.** The composition case: `seq d₁ d₂` threads
two suffixes, so the second step's remaining length is bounded by the first's,
which is bounded by `n`. -/
theorem seqConsumesByte {α β : Type} (d₁ : Codec α) (d₂ : Codec β)
    (h₁ : ConsumesByte d₁) (h₂ : ConsumesByte d₂) : ConsumesByte (Codec.seq d₁ d₂) := by
  intro x n s t hmem
  obtain ⟨t₁, t₂, hd₁, hd₂, rfl⟩ := (decode_seq_mem d₁ d₂ x s t).1 hmem
  have hlt₁ : t₁.remaining < n := h₁ x.1 s t₁ hd₁
  have hlt₂ : t₂.remaining < t₁.remaining := h₂ x.2 t₁.bytes t₂ hd₂
  -- `(Suffix.trans t₁ t₂).remaining` is `t₂.remaining` by `rfl`.
  show t₂.remaining < n
  omega

/-- **`iso` of a consumer consumes.** An `Iso` only *renames* the value — the
consumed-length is untouched — so the inner witness transfers directly. -/
theorem isoConsumesByte {α β : Type} (i : Iso α β) (d : Codec α)
    (h : ConsumesByte d) : ConsumesByte (Codec.iso i d) := by
  intro x n s t hmem
  rw [decode, List.mem_filterMap] at hmem
  obtain ⟨cand, hmem', hf⟩ := hmem
  rcases cand with ⟨a, tr⟩
  cases happ : i.apply a with
  | none => simp [happ] at hf
  | some y =>
      -- `hf : (i.apply a).map (fun y => (y, tr)) = some (x, t)`, so `tr = t`. Use the
      -- equality to move the membership onto `t`; a `rfl` pattern here would
      -- *eliminate* `tr` (substituting it away) and then the rewrite has no name.
      simp only [happ, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨-, htr⟩ := hf
      exact h a s t (htr ▸ hmem')

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
      rw [decode_seq_mem]
      constructor
      · intro h
        rcases h with ⟨t₁, t₂, hd₁, hd₂, hr⟩
        subst r
        rcases (ih₁ x.1 s t₁).1 hd₁ with ⟨s₁, hs₁, hrel₁⟩
        rcases (ih₂ x.2 t₁.bytes t₂).1 hd₂ with ⟨s₂, hs₂, hrel₂⟩
        refine ⟨cast (congrArg Bytes (sub_sub_add n t₁.remaining t₂.remaining t₁.hle t₂.hle)) (concat s₁ s₂), ?_, ?_⟩
        · rw [hs₁]
          exact (prepend_assoc t₁ t₂ s₁ s₂ hs₂.symm).symm
        · rw [Rel_seq]
          have hcast : t₁.remaining - t₂.remaining = n - t₂.remaining - (n - t₁.remaining) := by
            have ht₁ : t₁.remaining ≤ n := t₁.hle
            have ht₂ : t₂.remaining ≤ t₁.remaining := t₂.hle
            omega
          refine ⟨n - t₁.remaining, Nat.le.intro (by rw [sub_sub_add n t₁.remaining t₂.remaining t₁.hle t₂.hle]; rfl), s₁, cast (congrArg Bytes hcast) s₂, ?_, hrel₁, ?_⟩
          · rw [concat_eq_splice s₁ s₂]
            dsimp [Suffix.trans]
            rw [splice_cast_commute (sub_sub_add n t₁.remaining t₂.remaining t₁.hle t₂.hle) (Nat.le.intro rfl) s₁ _]
            congr 1
            simp
          · exact (Rel_cast d₂ x.2 hcast s₂).2 hrel₂
      · intro h
        rcases h with ⟨s₀, hs, hrel⟩
        rw [Rel_seq] at hrel
        rcases hrel with ⟨m, hm, s₁, s₂, hs₀, hrel₁, hrel₂⟩
        subst s₀
        -- s = r.prepend (splice hm s₁ s₂), Rel d₁ x.1 s₁, Rel d₂ x.2 s₂
        have hrle : r.remaining ≤ n := r.hle
        refine ⟨Suffix.drop m s, Suffix.drop ((n - r.remaining) - m) (bdrop m s), ?_, ?_, ?_⟩
        · -- (x.1, Suffix.drop m s) ∈ decode d₁ s
          refine (ih₁ x.1 s (Suffix.drop m s)).2 ⟨
            cast (congrArg Bytes (Nat.sub_sub_self (Nat.le_trans hm (Nat.sub_le n r.remaining))).symm) s₁,
            ?_, ?_⟩
          · rw [hs]
            exact prepend_drop_of_prepend_splice r m hm s₁ s₂
          · exact (Rel_cast d₁ x.1 (Nat.sub_sub_self (Nat.le_trans hm (Nat.sub_le n r.remaining))).symm s₁).2 hrel₁
        · -- (x.2, t₂) ∈ decode d₂ t₁.bytes
          refine (ih₂ x.2 (bdrop m s) (Suffix.drop ((n - r.remaining) - m) (bdrop m s))).2 ⟨
            cast (congrArg Bytes (Nat.sub_sub_self (Nat.sub_le_sub_right (Nat.sub_le n r.remaining) m)).symm) s₂,
            ?_, ?_⟩
          · rw [hs]
            exact prepend_eq_of_eq_splice (bdrop m (r.prepend (splice hm s₁ s₂))) (Nat.sub_le_sub_right (Nat.sub_le n r.remaining) m) s₂ (cast (congrArg Bytes (bdrop_prepend_splice_snd_len r.hle hm).symm) r.bytes) (bdrop_prepend_splice_eq_splice r m hm s₁ s₂)
          · exact (Rel_cast d₂ x.2 (Nat.sub_sub_self (Nat.sub_le_sub_right (Nat.sub_le n r.remaining) m)).symm s₂).2 hrel₂
        · -- r = trans t₁ t₂
          refine Suffix.ext (t₁ := r) (t₂ := Suffix.trans (Suffix.drop m s) (Suffix.drop ((n - r.remaining) - m) (bdrop m s))) ?_ ?_
          · exact (bdrop_prepend_splice_snd_len r.hle hm).symm
          · rw [hs]
            exact (bdrop_drop_eq_bytes r m hm s₁ s₂).symm
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
      constructor
      · intro h
        simp [decode] at h
      · intro h
        rcases h with ⟨s₀, hs, hr⟩
        simpa [decode] using (Rel_empty x s₀).1 hr
  | pure x₀ =>
      intro n s r
      simp [decode, Rel_pure]
      constructor
      · intro h
        rcases h with ⟨hx, hr⟩
        subst hr
        dsimp [Suffix.id]
        refine ⟨⟨cast (congrArg Bytes (Nat.sub_self n).symm) (emptyBytes : Bytes 0), ?_⟩, hx, Nat.sub_self n⟩
        · exact (prepend_id s).symm
      · intro h
        rcases h with ⟨hexist, hx, hn⟩
        rcases hexist with ⟨s₀, hs⟩
        have hrle : r.remaining ≤ n := r.hle
        have hrem : r.remaining = n := by omega
        -- r.bytes (transported to Bytes n) equals s
        have hbytes : cast (congrArg Bytes hrem) r.bytes = s := by
          rw [hs]
          apply Bytes.ext
          intro j
          unfold Suffix.prepend
          rw [splice_apply]
          unfold concat
          rw [cast_bytes_val' (e := hrem)]
          rw [cast_fin_symm]
          · dsimp
            have hn0 : n - r.remaining = 0 := hn
            simp [hn0]
            rw [cast_bytes_val_symm (e := Nat.sub_sub_self r.hle)]
          · omega

        refine ⟨hx, ?_⟩
        cases r with | mk remaining hle bytes =>
          change (Suffix.mk remaining hle bytes : Suffix n) = Suffix.id n s
          have hrem' : remaining = n := by simpa using hrem
          cases hrem'
          have hbytes' : bytes = s := by simpa using hbytes
          cases hbytes'
          rfl
  | byte =>
      intro n s r
      by_cases hn : n = 0
      · subst n
        have hr0 : r.remaining = 0 := by
          have := r.hle
          omega
        simp [decode, Rel, hr0]
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
        rw [decode]
        simp [hn]
        constructor
        · intro h
          rcases h with ⟨hx, hr⟩
          subst x
          subst r
          refine ⟨cast (congrArg Bytes (Nat.sub_sub_self (Nat.succ_le_of_lt hnpos)).symm) (single (s ⟨0, hnpos⟩)), ?_, ?_⟩
          · simpa using (prepend_drop_single hn s).symm
          · rw [Rel_byte]
            exact rel_byte_cast (Nat.sub_sub_self (Nat.succ_le_of_lt hnpos)) (s ⟨0, hnpos⟩)
        · intro h
          rcases h with ⟨s₀, hs, hrel⟩
          rw [Rel_byte] at hrel
          rcases hrel with ⟨hn1, hs₀⟩
          -- hn1 : n - r.remaining = 1, hs₀ : hn1 ▸ s₀ = single x
          have hs₀' : s₀ = cast (congrArg Bytes hn1.symm) (single x) := cast_bytes_eq_single hn1 s₀ x hs₀
          constructor
          · -- x = s ⟨0, hnpos⟩
            rw [hs]
            rw [prepend_apply]
            unfold concat
            have hne : n - r.remaining ≠ 0 := by
              rw [hn1]
              decide
            have hlt : 0 < n - r.remaining := Nat.pos_of_ne_zero hne
            rw [cast_fin_symm]
            · dsimp
              have hb : s₀ ⟨0, hlt⟩ = x := by
                rw [hs₀']
                rw [cast_bytes_val' (e := hn1.symm)]
                dsimp
                rfl
              simp [hb]
              intro hzero
              have : n - r.remaining = 1 := hn1
              rw [hzero] at this
              contradiction
            · omega
          · -- r = Suffix.drop 1 s
            have hdrop : Suffix.drop (n - r.remaining) (r.prepend s₀) = r := drop_prepend r s₀
            rw [hn1] at hdrop
            rw [hs]
            exact hdrop.symm
  | satisfy p =>
      intro n s r
      by_cases hn : n = 0
      · subst n
        have hr0 : r.remaining = 0 := by
          have := r.hle
          omega
        simp [decode, Rel, hr0]
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
        by_cases hp : p (s ⟨0, hnpos⟩)
        · rw [decode]
          simp [hn, hp]
          constructor
          · intro h
            rcases h with ⟨hx, hr⟩
            subst x
            subst r
            refine ⟨cast (congrArg Bytes (Nat.sub_sub_self (Nat.succ_le_of_lt hnpos)).symm) (single (s ⟨0, hnpos⟩)), ?_, ?_⟩
            · simpa using (prepend_drop_single hn s).symm
            · rw [Rel_satisfy]
              exact ⟨hp, rel_byte_cast (Nat.sub_sub_self (Nat.succ_le_of_lt hnpos)) (s ⟨0, hnpos⟩)⟩
          · intro h
            rcases h with ⟨s₀, hs, hrel⟩
            rw [Rel_satisfy] at hrel
            rcases hrel with ⟨hpx, hn1, hs₀⟩
            -- hn1 : n - r.remaining = 1, hs₀ : hn1 ▸ s₀ = single x
            have hs₀' : s₀ = cast (congrArg Bytes hn1.symm) (single x) := cast_bytes_eq_single hn1 s₀ x hs₀
            constructor
            · -- x = s ⟨0, hnpos⟩
              rw [hs]
              rw [prepend_apply]
              unfold concat
              have hne : n - r.remaining ≠ 0 := by
                rw [hn1]
                decide
              have hlt : 0 < n - r.remaining := Nat.pos_of_ne_zero hne
              rw [cast_fin_symm]
              · dsimp
                have hb : s₀ ⟨0, hlt⟩ = x := by
                  rw [hs₀']
                  rw [cast_bytes_val' (e := hn1.symm)]
                  dsimp
                  rfl
                simp [hb]
                intro hzero
                have : n - r.remaining = 1 := hn1
                rw [hzero] at this
                contradiction
              · omega
            · -- r = Suffix.drop 1 s
              have hdrop : Suffix.drop (n - r.remaining) (r.prepend s₀) = r := drop_prepend r s₀
              rw [hn1] at hdrop
              rw [hs]
              exact hdrop.symm
        · have hdec : decode (Codec.satisfy p) s = [] := by
            simp [decode, hn, hp]
          rw [hdec]
          constructor
          · intro h
            cases h
          · intro h
            rcases h with ⟨s₀, hs, hrel⟩
            rw [Rel_satisfy] at hrel
            rcases hrel with ⟨hpx, hn1, hs₀⟩
            have hne : n - r.remaining ≠ 0 := by rw [hn1]; decide
            have hlt : 0 < n - r.remaining := Nat.pos_of_ne_zero hne
            have hs₀' : s₀ = cast (congrArg Bytes hn1.symm) (single x) := cast_bytes_eq_single hn1 s₀ x hs₀
            have hb' : s₀ ⟨0, hlt⟩ = x := by
              rw [hs₀']
              rw [cast_bytes_val' (e := hn1.symm)]
              rfl
            have hs' : s ⟨0, hnpos⟩ = (r.prepend s₀) ⟨0, hnpos⟩ := by rw [hs]
            have hpp : s ⟨0, hnpos⟩ = x := by
              rw [hs']
              rw [prepend_prefix_read r s₀ ⟨0, hnpos⟩ hlt]
              exact hb'
            have hpx' : p (s ⟨0, hnpos⟩) = true := by
              exact hpp ▸ hpx
            exact False.elim (hp hpx')

theorem bidir {α : Type} (d : Codec α) (x : α) (n : Nat) (s : Bytes n) :
    Rel d x s ↔ (x, Suffix.empty n) ∈ decode d s := by
  have hspec := decode_spec d x (s := s) (r := Suffix.empty n)
  constructor
  · intro hr
    refine hspec.2 ⟨cast (congrArg Bytes (Nat.sub_zero n).symm) s, ?_, ?_⟩
    · exact (prepend_empty_eq s).symm
    · exact (Rel_cast d x (Nat.sub_zero n).symm s).2 hr
  · intro hd
    rcases hspec.1 hd with ⟨s₀, hs, hr⟩
    have hscast : cast (congrArg Bytes (Nat.sub_zero n).symm) s = s₀ := by
      rw [hs]
      rw [prepend_empty s₀]
      cases (Nat.sub_zero n)
      rfl
    rw [← hscast] at hr
    exact (Rel_cast d x (Nat.sub_zero n).symm s).1 hr

/-- The strong roundtrip invariant: a value encoded to `s : Bytes m` decodes back to
`(x, ·)` leaving exactly the appended `r : Bytes q` unconsumed, from the input
`concat s r`. Unconditional. -/
theorem decode_encode {α : Type} (d : Codec α) (x : α) :
    ∀ {m : Nat} {s : Bytes m}, encode d x = some ⟨m, s⟩ →
      ∀ {q : Nat} (r : Bytes q),
        (x, Suffix.drop m (concat s r)) ∈ decode d (concat s r) := by
  intro m s he q r
  have hrel : Rel d x s := encode_rel d x he
  have hspre : concat s r = (Suffix.drop m (concat s r)).prepend
      (cast (congrArg Bytes (Nat.sub_sub_self (Nat.le.intro rfl)).symm) s) :=
    prepend_eq_of_eq_splice (concat s r) (Nat.le.intro rfl) s
      (cast (congrArg Bytes (Nat.add_sub_cancel_left m q).symm) r) (concat_eq_splice s r)
  refine (decode_spec d x (s := concat s r) (r := Suffix.drop m (concat s r))).2 ⟨cast (congrArg Bytes (Nat.sub_sub_self (Nat.le.intro rfl)).symm) s, hspre, ?_⟩
  exact (Rel_cast d x (Nat.sub_sub_self (Nat.le.intro rfl)).symm s).2 hrel

/-- The byte-exact roundtrip: a value encoded to `s` decodes back to `x` with
no remainder. Unconditional. -/
theorem roundtrip {α : Type} (d : Codec α) (x : α) (n : Nat) (s : Bytes n) :
    encode d x = some ⟨n, s⟩ → (x, Suffix.empty n) ∈ decode d s := by
  intro he
  exact (bidir d x n s).1 (encode_rel d x he)

/-! ## Repetition: the totality boundary and the decoder law -/

/-- The totality boundary: `decode p` strictly shortens the input exactly when
`p` is productive (every value it relates sits on a non-empty string). -/
theorem productive_iff_consumesByte {α : Type} (p : Codec α) :
    Productive p ↔ ConsumesByte p := by
  constructor
  · intro hprod x n s t hmem
    rcases (decode_spec p x (s := s) (r := t)).1 hmem with ⟨s₀, hs, hrel⟩
    have hn0 : n - t.remaining ≠ 0 := hprod x s₀ hrel
    have hlt : t.remaining < n := by omega
    exact hlt
  · intro hcons x n s hrel hn
    subst n
    have hmem : (x, Suffix.empty 0) ∈ decode p s := (bidir p x 0 s).1 hrel
    have hlt : (Suffix.empty 0).remaining < 0 := hcons x s (Suffix.empty 0) hmem
    omega

/-- The `many`-case of the bidirectional law: `(xs, r) ∈ decodeRepeat p h n s`
exactly when the input splits as a `relRepeat`-prefix plus `r`. -/
theorem decodeRepeat_spec {α : Type} (p : Codec α) (h : ConsumesByte p) :
    ∀ (xs : List α) (n : Nat) (s : Bytes n) (r : Suffix n),
      (xs, r) ∈ decodeRepeat p h n s ↔
        ∃ s₀ : Bytes (n - r.remaining), s = r.prepend s₀ ∧ relRepeat (Rel p) xs (n - r.remaining) s₀ := by
  intro xs
  intro n
  revert xs
  refine Nat.strongRecOn n ?_
  intro n ih
  intro xs s r
  rw [decodeRepeat_eq]
  constructor
  · intro hmem
    rw [List.mem_cons] at hmem
    rcases hmem with hm | hm
    · -- (xs, r) = ([], Suffix.id n s)
      rcases hm with ⟨hxs, hr⟩
      refine ⟨cast (congrArg Bytes (Nat.sub_self n).symm) (emptyBytes : Bytes 0), ?_, ?_⟩
      · exact (prepend_id s).symm
      · dsimp [Suffix.id]
        simp [relRepeat]
    · -- (xs, r) ∈ (decode p s).attach.flatMap ...
      rw [List.mem_flatMap] at hm
      rcases hm with ⟨a, ha, hm'⟩
      rcases a with ⟨⟨x, t⟩, ha'⟩
      rw [List.mem_map] at hm'
      rcases hm' with ⟨b, hb, hmap⟩
      rcases b with ⟨rest, r'⟩
      cases hmap
      rcases (ih t.remaining (h x s t ha') rest t.bytes r').1 hb with ⟨s₂, hs₂, hrr⟩
      rcases (decode_spec p x s t).1 ha' with ⟨s₁, hs₁, hrel₁⟩
      -- want (x :: rest, Suffix.trans t r') with s₀ = concat s₁ s₂ (cast)
      refine ⟨cast (congrArg Bytes (sub_sub_add n t.remaining r'.remaining t.hle r'.hle)) (concat s₁ s₂), ?_, ?_⟩
      · -- s = (Suffix.trans t r').prepend (cast ... (concat s₁ s₂))
        rw [hs₁]
        exact (prepend_assoc t r' s₁ s₂ hs₂.symm).symm
      · -- relRepeat (Rel p) (x::rest) (n - r'.remaining) (cast ... (concat s₁ s₂))
        rw [relRepeat_cons]
        refine ⟨n - t.remaining, Nat.sub_le_sub_left r'.hle n, s₁, cast (congrArg Bytes (sub_sub_sub n t.remaining r'.remaining t.hle r'.hle).symm) s₂, ?_, hrel₁, ?_⟩
        · -- cast ... (concat s₁ s₂) = splice ... s₁ (cast ... s₂)
          exact cast_concat_splice_sub t.hle r'.hle s₁ s₂
        · exact (relRepeat_cast (Rel p) rest (sub_sub_sub n t.remaining r'.remaining t.hle r'.hle).symm s₂).2 hrr
  · intro h
    rcases h with ⟨s₀, hs, hrel⟩
    cases xs with
    | nil =>
        rw [relRepeat_nil] at hrel
        -- hrel : n - r.remaining = 0
        rw [List.mem_cons]
        left
        congr
        -- r = Suffix.id n s
        have hdrop : Suffix.drop 0 s = r := by
          rw [hs]
          rw [← hrel]
          exact drop_prepend r s₀
        rw [← hdrop]
        exact drop_zero_eq_id s
    | cons x rest =>
        rw [relRepeat_cons] at hrel
        rcases hrel with ⟨m, hm, s₁, s₂, hs₀, hrel₁, hrel₂⟩
        subst s₀
        -- s = r.prepend (splice hm s₁ s₂), hrel₁ : Rel p x s₁, hrel₂ : relRepeat (Rel p) rest (n - r.remaining - m) s₂
        rw [List.mem_cons]
        right
        rw [List.mem_flatMap]
        have hmem₁ : (x, Suffix.drop m s) ∈ decode p s :=
          (decode_spec p x s (Suffix.drop m s)).2 ⟨
            cast (congrArg Bytes (Nat.sub_sub_self (Nat.le_trans hm (Nat.sub_le n r.remaining))).symm) s₁,
            by rw [hs]; exact prepend_drop_of_prepend_splice r m hm s₁ s₂,
            (Rel_cast p x (Nat.sub_sub_self (Nat.le_trans hm (Nat.sub_le n r.remaining))).symm s₁).2 hrel₁⟩
        have hlt : n - m < n := by
          have := h x s (Suffix.drop m s) hmem₁
          simpa [Suffix.drop] using this
        let r' : Suffix (n - m) := Suffix.drop ((n - r.remaining) - m) (bdrop m s)
        have hmem₂ : (rest, r') ∈ decodeRepeat p h (n - m) (bdrop m s) :=
          (ih (n - m) hlt rest (bdrop m s) r').2 ⟨
            cast (congrArg Bytes (Nat.sub_sub_self (Nat.sub_le_sub_right (Nat.sub_le n r.remaining) m)).symm) s₂,
            by
              dsimp [r']
              rw [hs]
              exact prepend_eq_of_eq_splice (bdrop m (r.prepend (splice hm s₁ s₂))) (Nat.sub_le_sub_right (Nat.sub_le n r.remaining) m) s₂ (cast (congrArg Bytes (bdrop_prepend_splice_snd_len r.hle hm).symm) r.bytes) (bdrop_prepend_splice_eq_splice r m hm s₁ s₂),
            (relRepeat_cast (Rel p) rest (Nat.sub_sub_self (Nat.sub_le_sub_right (Nat.sub_le n r.remaining) m)).symm s₂).2 hrel₂⟩
        have htrans : (Suffix.drop m s).trans r' = r := by
          refine Suffix.ext (t₁ := (Suffix.drop m s).trans r') (t₂ := r) ?_ ?_
          · dsimp [r', Suffix.trans]
            exact bdrop_prepend_splice_snd_len r.hle hm
          · dsimp [r', Suffix.trans, Suffix.drop]
            rw [hs]
            rw [bdrop_drop_eq_bytes r m hm s₁ s₂]
            change cast (congrArg Bytes (bdrop_prepend_splice_snd_len r.hle hm)) (cast (congrArg Bytes (bdrop_prepend_splice_snd_len r.hle hm).symm) r.bytes) = r.bytes
            simp
        refine ⟨⟨(x, Suffix.drop m s), hmem₁⟩, List.mem_attach (p.decode s) ⟨(x, Suffix.drop m s), hmem₁⟩, ?_⟩
        rw [List.mem_map]
        refine ⟨(rest, r'), hmem₂, ?_⟩
        exact congrArg (fun y => (x :: rest, y)) htrans

/-- Repetition with an empty-matching step has arbitrarily many results. -/
theorem relRepeat_unbounded_of_empty {α : Type} (p : Codec α) (x : α)
    (hx : Rel p x (emptyBytes : Bytes 0)) :
    ∀ m : Nat, relRepeat (Rel p) (List.replicate m x) 0 emptyBytes := by
  intro m
  induction m with
  | zero => simp [relRepeat]
  | succ m ih =>
      change relRepeat (Rel p) (x :: List.replicate m x) 0 emptyBytes
      rw [relRepeat_cons]
      refine ⟨0, Nat.zero_le 0, emptyBytes, emptyBytes, ?_, hx, ih⟩
      apply Bytes.ext
      intro i
      exact Fin.elim0 i

/-- `pure x` is not productive. -/
theorem not_productive_pure {α : Type} [DecidableEq α] (x : α) :
    ¬ Productive (Codec.pure x : Codec α) := by
  intro hp
  have hrel : Rel (Codec.pure x : Codec α) x (emptyBytes : Bytes 0) := by
    simp [Rel]
  have h := hp x (emptyBytes : Bytes 0) hrel
  exact (h rfl)

/-- Encoder soundness for repetition. -/
theorem encodeRepeat_rel {α : Type} (p : Codec α) :
    ∀ (xs : List α) {n : Nat} {s : Bytes n}, encodeRepeat p xs = some ⟨n, s⟩ → relRepeat (Rel p) xs n s := by
  intro xs
  induction xs with
  | nil =>
      intro n s he
      have hs : (⟨0, (emptyBytes : Bytes 0)⟩ : Sigma fun k => Bytes k) = ⟨n, s⟩ := by
        simpa [encodeRepeat] using he
      cases hs
      simp [relRepeat]
  | cons x rest ih =>
      intro n s he
      rw [encodeRepeat] at he
      cases hx : encode p x with
      | none => simp [hx] at he
      | some sx =>
          rw [hx] at he
          rcases sx with ⟨n₁, s₁⟩
          cases hr : encodeRepeat p rest with
          | none => simp [hr] at he
          | some sr =>
              rw [hr] at he
              rcases sr with ⟨n₂, s₂⟩
              have heq : (⟨n₁ + n₂, concat s₁ s₂⟩ : Sigma fun k => Bytes k) = ⟨n, s⟩ := by
                simpa using he
              cases heq
              rw [relRepeat_cons]
              refine ⟨n₁, Nat.le.intro rfl, s₁, cast (congrArg Bytes (Nat.add_sub_cancel_left n₁ n₂).symm) s₂, ?_, encode_rel p x hx, ?_⟩
              · exact concat_eq_splice s₁ s₂
              · exact (relRepeat_cast (Rel p) rest (Nat.add_sub_cancel_left n₁ n₂).symm s₂).2 (ih hr)

/-! ## Unambiguity, functionality, and the decode→encode direction -/

def Unambiguous {α : Type} (d : Codec α) : Prop :=
  ∀ ⦃x y⦄ {n : Nat} (s : Bytes n), Rel d x s → Rel d y s → x = y

def Functional {α : Type} (d : Codec α) : Prop :=
  ∀ x {n₁ n₂ : Nat} (s₁ : Bytes n₁) (s₂ : Bytes n₂),
    Rel d x s₁ → Rel d x s₂ → (⟨n₁, s₁⟩ : Sigma fun n => Bytes n) = ⟨n₂, s₂⟩

/-- **Encoder completeness**: every value in the denotation encodes successfully. -/
theorem encode_ne_none {α : Type} (d : Codec α) (x : α) {n : Nat} (s : Bytes n) :
    Rel d x s → encode d x ≠ none := by
  induction d generalizing n s with
  | iso i d ih =>
      intro hrel
      rcases hrel with ⟨a, hia, hda⟩
      rw [encode]
      have hua : i.unapply x = some a := (i.law a x).1 hia
      rw [hua]
      exact ih a s hda
  | seq d₁ d₂ ih₁ ih₂ =>
      rcases x with ⟨x₁, x₂⟩
      intro hrel
      rw [Rel_seq] at hrel
      rcases hrel with ⟨m, hm, s₁, s₂, hs, hr₁, hr₂⟩
      rw [encode]
      have hne₁ : encode d₁ x₁ ≠ none := ih₁ x₁ s₁ hr₁
      cases h₁ : encode d₁ x₁ with
      | none => exact False.elim (hne₁ h₁)
      | some e₁ =>
          rcases e₁ with ⟨n₁, b₁⟩
          have hne₂ : encode d₂ x₂ ≠ none := ih₂ x₂ s₂ hr₂
          cases h₂ : encode d₂ x₂ with
          | none => exact False.elim (hne₂ h₂)
          | some e₂ => simp
  | alt d₁ d₂ ih₁ ih₂ =>
      intro hrel
      rw [encode]
      rw [Rel_alt] at hrel
      rcases hrel with hr | hr
      · have hne : encode d₁ x ≠ none := ih₁ x s hr
        cases h₁ : encode d₁ x with
        | none => exact False.elim (hne h₁)
        | some e₁ => simp
      · have hne : encode d₂ x ≠ none := ih₂ x s hr
        cases h₂ : encode d₂ x with
        | none => exact False.elim (hne h₂)
        | some e₂ => simp
  | empty =>
      intro hrel
      simp [Rel] at hrel
  | pure x₀ =>
      intro hrel
      rw [encode]
      rw [Rel_pure] at hrel
      rcases hrel with ⟨hx, hs⟩
      simp [hx]
  | byte =>
      intro hrel
      rw [encode]
      rw [Rel_byte] at hrel
      rcases hrel with ⟨h, hs⟩
      subst h
      simp
  | satisfy p =>
      intro hrel
      rw [encode]
      rw [Rel_satisfy] at hrel
      rcases hrel with ⟨hp, h, hs⟩
      subst h
      simp [hp]

/-- `Unambiguous` is **satisfiable**, not decorative: `byte` relates every value to
exactly one byte string (`Rel_byte`). This is a base instance the definition needs
(a typo in it — quantifying over the wrong `s`, say — would otherwise go unnoticed,
because nothing in-tree established it for any `d`). Axiom-free. -/
theorem unambiguous_byte : Unambiguous Codec.byte := by
  intro x y n s hx hy
  rw [Rel_byte] at hx hy
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  subst hx1
  have hp := congrFun hx2 ⟨0, by omega⟩
  have hq := congrFun hy2 ⟨0, by omega⟩
  simp only [single] at hp hq
  rw [hp] at hq
  exact hq

/-- `Functional` is satisfiable for the same reason: one byte value determines one
byte string, hence one `(length, bytes)` sigma. The companion of
`unambiguous_byte`. Axiom-free. -/
theorem functional_byte : Functional Codec.byte := by
  intro x n₁ n₂ s₁ s₂ h₁ h₂
  rw [Rel_byte] at h₁ h₂
  obtain ⟨h11, h12⟩ := h₁
  obtain ⟨h21, h22⟩ := h₂
  subst h11
  subst h21
  have hss : s₁ = s₂ := by
    have hp := congrFun h12 ⟨0, by omega⟩
    have hq := congrFun h22 ⟨0, by omega⟩
    simp only [single] at hp hq
    funext i
    have hi : i = ⟨0, by omega⟩ := by
      apply Fin.ext
      have := i.isLt
      omega
    rw [hi, hp, hq]
  rw [hss]

theorem encode_of_decode {α : Type} (d : Codec α) (hd : Functional d) (x : α)
    {n : Nat} {s : Bytes n} (hdcd : (x, Suffix.empty n) ∈ decode d s) : encode d x = some ⟨n, s⟩ := by
  have hne : encode d x ≠ none := encode_ne_none d x s ((bidir d x n s).2 hdcd)
  cases he : encode d x with
  | none => exact False.elim (hne he)
  | some e =>
      rcases e with ⟨n', s'⟩
      have hrel' : Rel d x s' := encode_rel d x he
      have hrels : Rel d x s := (bidir d x n s).2 hdcd
      congr 1
      exact (hd x s s' hrels hrel').symm

theorem encode_injective_of_unambiguous {α : Type} (d : Codec α) (hd : Unambiguous d)
    {x y : α} {n : Nat} {s : Bytes n} (hx : encode d x = some ⟨n, s⟩) (hy : encode d y = some ⟨n, s⟩) :
    x = y := by
  have hrelx : Rel d x s := encode_rel d x hx
  have hrely : Rel d y s := encode_rel d y hy
  exact hd s hrelx hrely

/-! ## Relation-level completeness and functionality -/

def relFunctional {α : Type} (R : α → {n : Nat} → Bytes n → Prop) : Prop :=
  ∀ a {n₁ n₂ : Nat} (s₁ : Bytes n₁) (s₂ : Bytes n₂),
    R a s₁ → R a s₂ → (⟨n₁, s₁⟩ : Sigma fun n => Bytes n) = ⟨n₂, s₂⟩

def relUnambiguous {α : Type} (R : α → {n : Nat} → Bytes n → Prop) : Prop :=
  ∀ ⦃a b⦄ {n : Nat} (s : Bytes n), R a s → R b s → a = b

/-! ## Full-consumption uniqueness: what it needs, and what it does NOT follow from

`decodeFull_spec` (in `Codec.Decode`) takes as a hypothesis

    huniq : ∀ {x y} {n} (s : Bytes n),
      (x, Suffix.empty n) ∈ decodeRepeat p h n s →
      (y, Suffix.empty n) ∈ decodeRepeat p h n s → x = y

i.e. *at most one value list fully consumes a given string*. It is a real
precondition, not a restatement of anything already in the tree.

**`huniq` does NOT follow from `relUnambiguous` plus productivity.** That was the
belief when the gap was first recorded (task 2.6 of `codec-review-remediation`), and
it is **false** — machine-checked below as `huniq_not_derivable`. The counterexample
(`uniqCounterexampleRel`) relates one value to every 2-byte string and another to
every 1-byte string. It is unambiguous (`uniqCounterexample_unambiguous`, one value
per string at a fixed length) and productive (`uniqCounterexample_productive`, no
value sits on the empty string), yet at `n = 2` **both** `[a]` (one 2-byte step) and
`[b, b]` (two 1-byte steps) inhabit `relRepeat` — two distinct fully-consuming lists
of the same string.

So the honest statement needs **two** extra hypotheses beyond unambiguity, and this
section proves the law for that pair:

* `LengthDet R` — each value relates only to strings of one length.
* `RelAligned R` — values are identified by their shared byte prefix; unambiguity
  extended *across* lengths, so the induction can compare two first steps whose
  lengths differ.

**Which hypothesis excludes the counterexample, stated correctly:** it is the
**length index**, not `LengthDet`. `uniqCounterexampleRel` is *already* `LengthDet`
(each value sits at exactly one length), so saying `LengthDet` "rules it out" would
be false; what rules it out is that `[a]` and `[b, b]` differ in *list length*, and
`relRepeat_unique_same_length` concludes only for equal-length lists.

**Scope of the result, stated precisely.** `relRepeat_unique_same_length` is
uniqueness **indexed by list length**:

    relRepeat R xs n s → relRepeat R ys n s → xs.length = ys.length → xs = ys

It is therefore **strictly weaker** than `huniq`, which has no length hypothesis, and
it does **not** by itself discharge `decodeFull_spec`'s premise. **The bridge is
below and is proved, not outlined:** for a *constant*-length step relation
(`LengthConst R c`) the consuming list's length is pinned by the input length
(`relRepeat_length_of_const`, hence `lengths_eq_of_const`), so the index is
discharged. `huniq_byte` applies that chain at `Codec.byte`, and
`decodeFull_spec_byte` — which needs no hypothesis at all — is the result. So
`huniq` now **has** an in-tree supplier, at one concrete codec, and the original
finding ("an unproved premise") is closed.

Lemmas, all `[propext, Quot.sound]`-only with zero `Classical.choice`:
`relRepeat_prefix_inj` / `relRepeat_suffix_inj` (same-length splices agree in their
prefix / suffix), `splice_prefix_agree` (cross-length prefix agreement),
`relRepeat_cons_eq` (the oriented core of the induction, with the IH as a parameter so
its footprint is checkable standalone), `relRepeat_unique_same_length`, and the
`LengthConst` bridge into `huniq_byte` / `decodeFull_spec_byte`. -/


/-- **Two splices of one string at the same length have the same prefix.** Reading
every index below `m` recovers the prefix through `splice_prefix_read`, so equality
of the whole strings forces equality of the prefixes. The workhorse the uniqueness
argument reduces to. `[propext, Quot.sound]`-only. -/
theorem relRepeat_prefix_inj {n m : Nat} (hm : m ≤ n)
    (s₁ s₁' : Bytes m) (s₂ s₂' : Bytes (n - m))
    (h : splice hm s₁ s₂ = splice hm s₁' s₂') : s₁ = s₁' := by
  apply Bytes.ext
  intro i
  have hi : i.val < m := i.isLt
  have key := congrFun h ⟨i.val, Nat.lt_of_lt_of_le hi hm⟩
  rw [splice_prefix_read hm s₁ s₂ ⟨i.val, _⟩ hi,
      splice_prefix_read hm s₁' s₂' ⟨i.val, _⟩ hi] at key
  exact key

/-- **Two splices of one string at the same length have the same suffix.** The dual
of `relRepeat_prefix_inj`, via `bdrop_splice`. `[propext, Quot.sound]`-only. -/
theorem relRepeat_suffix_inj {n m : Nat} (hm : m ≤ n)
    (s₁ : Bytes m) (s₂ s₂' : Bytes (n - m))
    (h : splice hm s₁ s₂ = splice hm s₁ s₂') : s₂ = s₂' := by
  have := congrArg (bdrop m) h
  rw [bdrop_splice hm s₁ s₂, bdrop_splice hm s₁ s₂'] at this
  exact this

/-- A step relation is **length-determinate** when each value relates only to strings
of a single length. It is one of the two hypotheses
`relRepeat_unique_same_length` needs beyond unambiguity, and it is *not* implied by
it. It holds for `byte` (which lives only at `Bytes 1`) and for any codec whose
leaves are fixed-width in their *value*.

Note what it does **not** say: it does not pin the length of a *list* of steps — two
values may each sit at one length while a list of them has any number of elements.
Pinning the list length needs the stronger, constant-length form `LengthConst`
(defined and used below), and the usable chain is `LengthConst → LengthDet`, proved
as `lengthDet_of_lengthConst`. `LengthDet → RelAligned` would need a `DecidableEq α`
and is deliberately not proved. -/
def LengthDet {α : Type} (R : α → {m : Nat} → Bytes m → Prop) : Prop :=
  ∀ ⦃a : α⦄ {m₁ m₂ : Nat} (t₁ : Bytes m₁) (t₂ : Bytes m₂), R a t₁ → R a t₂ → m₁ = m₂

/-- **Values are identified by their shared prefix.** Two values related to byte
strings that agree on the shorter one are equal. This is `relUnambiguous` *extended
across lengths*: at equal lengths it is exactly unambiguity, and the extra content is
that a value cannot be distinguished by bytes beyond its own step length. It is what
lets the uniqueness induction compare the two decompositions' first steps when their
lengths may differ. Satisfied by `byte` (`relUnambiguous` at `Bytes 1`).

**Strength ordering, stated as theorems rather than prose.** `RelAligned R →
relUnambiguous R` (proved as `relUnambiguous_of_relAligned`, immediately below); the
converse is what
"at equal lengths it is exactly unambiguity" says, so `RelAligned` is *not
strictly* stronger than `relUnambiguous` — there is no relation that is unambiguous
and not aligned, and no such witness is worth hunting for. It is however strictly
stronger than `LengthDet` in the useful direction: `LengthDet R → RelAligned R`
needs a `DecidableEq α`, i.e. a classical axiom, and is therefore **deliberately
not** proved in this tree. The usable chain is `LengthConst → LengthDet`, proved as
`lengthDet_of_lengthConst` (`codec-review-remediation` 2.6). -/
def RelAligned {α : Type} (R : α → {m : Nat} → Bytes m → Prop) : Prop :=
  ∀ ⦃a b : α⦄ {m₁ m₂ : Nat} (t₁ : Bytes m₁) (t₂ : Bytes m₂) (hle : m₁ ≤ m₂),
    R a t₁ → R b t₂ →
    (∀ (i : Fin m₁), t₁ i = t₂ ⟨i.val, Nat.lt_of_lt_of_le i.isLt hle⟩) → a = b

/-- **`RelAligned` implies `relUnambiguous`**: at one fixed length a value is
identified by its own bytes, so two values related to the same `s` are equal — the
`t₁ = t₂` case of alignment, where the shared-prefix premise is `rfl` at every
index. This is the lemma `RelAligned`'s docstring cites as proved; it used to cite
it while it did not exist (`codec-audit-remediation` 3.1, design D4).
`[propext, Quot.sound]`-only. -/
theorem relUnambiguous_of_relAligned {α : Type} {R : α → {m : Nat} → Bytes m → Prop}
    (hal : RelAligned R) : relUnambiguous R := by
  intro a b n s hra hrb
  exact hal s s (Nat.le_refl n) hra hrb (fun _ => rfl)

/-- Two splices of one string at lengths `m₁ ≤ m₂` agree on their `m₁`-prefix, read
index-by-index. `[propext, Quot.sound]`-only. -/
theorem splice_prefix_agree {n m₁ m₂ : Nat} (h₁ : m₁ ≤ n) (h₂ : m₂ ≤ n) (hle : m₁ ≤ m₂)
    (s₁ : Bytes m₁) (s₂ : Bytes (n - m₁)) (s₁' : Bytes m₂) (s₂' : Bytes (n - m₂))
    (heq : splice h₁ s₁ s₂ = splice h₂ s₁' s₂') :
    ∀ (i : Fin m₁), s₁ i = s₁' ⟨i.val, Nat.lt_of_lt_of_le i.isLt hle⟩ := by
  intro i
  have hi : i.val < m₁ := i.isLt
  have hlt2 : i.val < m₂ := Nat.lt_of_lt_of_le hi hle
  have key := congrFun heq ⟨i.val, Nat.lt_of_lt_of_le hi h₁⟩
  rw [splice_prefix_read h₁ s₁ s₂ ⟨i.val, _⟩ hi,
      splice_prefix_read h₂ s₁' s₂' ⟨i.val, _⟩ hlt2] at key
  exact key

/-- A length-determinate-free step relation: `true` on any 2-byte string, `false` on
any 1-byte string. Unambiguous at fixed length and productive, yet it admits two
distinct fully-consuming lists at `n = 2`. -/
def uniqCounterexampleRel : Bool → {m : Nat} → Bytes m → Prop
  | true, m, _ => m = 2
  | false, m, _ => m = 1

theorem uniqCounterexample_unambiguous :
    ∀ ⦃a b : Bool⦄ {m : Nat} (t : Bytes m), uniqCounterexampleRel a t →
      uniqCounterexampleRel b t → a = b := by
  intro a b m t ha hb
  cases a <;> cases b <;> simp_all [uniqCounterexampleRel]

theorem uniqCounterexample_productive :
    ∀ a {m : Nat} (t : Bytes m), uniqCounterexampleRel a t → m ≠ 0 := by
  intro a m t h
  cases a <;> simp_all [uniqCounterexampleRel]

theorem uniqCounterexample_single :
    relRepeat uniqCounterexampleRel [true] 2 (fun _ => 0) :=
  ⟨2, by omega, (fun _ => 0), (fun i : Fin 0 => i.elim0), by ext i; simp [splice, concat],
   rfl, (relRepeat_nil _ _).2 rfl⟩

theorem uniqCounterexample_pair :
    relRepeat uniqCounterexampleRel [false, false] 2 (fun _ => 0) :=
  ⟨1, by omega, (fun _ => 0), (fun _ => 0), by ext i; simp [splice, concat], rfl,
   ⟨1, by omega, (fun _ => 0), (fun i : Fin 0 => i.elim0), by ext i; simp [splice, concat],
    rfl, (relRepeat_nil _ _).2 rfl⟩⟩

/-- **`huniq` is not derivable from unambiguity + productivity.** Two distinct
fully-consuming lists of the same string, for a step relation that is both
unambiguous and productive. What is missing is `LengthDet`; the lists also differ in
*length*, which is why the honest uniqueness law is length-indexed. -/
theorem huniq_not_derivable :
    ¬ (∀ (xs ys : List Bool), relRepeat uniqCounterexampleRel xs 2 (fun _ => 0) →
        relRepeat uniqCounterexampleRel ys 2 (fun _ => 0) → xs = ys) := by
  intro h
  have := h [true] [false, false] uniqCounterexample_single uniqCounterexample_pair
  exact absurd this (by simp)

/-- `LengthDet` holds for `byte`: `Rel byte a s` forces `s` to be the one-byte string
`[a]`, so both `m₁` and `m₂` are `1`. The first in-tree discharge of the extra
hypothesis, and the reason it is not vacuous. `[propext, Quot.sound]`-only. -/
theorem lengthDet_byte : LengthDet (Rel Codec.byte) := by
  intro a m₁ m₂ t₁ t₂ h₁ h₂
  rw [Rel_byte] at h₁ h₂
  obtain ⟨ha₁, -⟩ := h₁
  obtain ⟨ha₂, -⟩ := h₂
  subst ha₁
  subst ha₂
  rfl

/-- `RelAligned` holds for `byte`: both related strings are the one-byte `single`, so
the shared prefix (index `0`) already determines the value. Proved directly from
`Rel_byte` (no appeal to `relUnambiguous`); the companion of `lengthDet_byte` for
the uniqueness hypothesis pair. `[propext, Quot.sound]`-only. -/
theorem relAligned_byte : RelAligned (Rel Codec.byte) := by
  intro a b m₁ m₂ t₁ t₂ _hle h₁ h₂ hagree
  rw [Rel_byte] at h₁ h₂
  obtain ⟨hm₁, ht₁⟩ := h₁
  obtain ⟨hm₂, ht₂⟩ := h₂
  subst hm₁
  subst hm₂
  have e := hagree ⟨0, by omega⟩
  simp only [] at ht₁ ht₂
  rw [ht₁] at e
  rw [ht₂] at e
  exact e

/-- The **oriented core** of the uniqueness induction: two decompositions of one
string, with the first step no longer than the second, and an induction hypothesis
supplied as a parameter (so this lemma is provable standalone and its footprint is
checkable). `[propext, Quot.sound]`-only. -/
theorem relRepeat_cons_eq {α : Type} (R : α → {m : Nat} → Bytes m → Prop)
    (hld : LengthDet R) (hal : RelAligned R)
    (n : Nat) (ih : ∀ (k : Nat), k < n → ∀ (t : Bytes k) (xs ys : List α),
        relRepeat R xs k t → relRepeat R ys k t → xs.length = ys.length → xs = ys)
    (a₀ b₀ : α) (us vs : List α) (m m' : Nat) (hm : m ≤ n) (hm' : m' ≤ n) (hle : m ≤ m')
    (a : Bytes m) (b : Bytes (n - m)) (a' : Bytes m') (b' : Bytes (n - m'))
    (hspl : splice hm a b = splice hm' a' b')
    (hRa : R a₀ a) (hRa' : R b₀ a')
    (hra : relRepeat R us (n - m) b) (hra' : relRepeat R vs (n - m') b')
    (hne : m ≠ 0) (hltq : us.length = vs.length) : (a₀ :: us) = (b₀ :: vs) := by
  have hxy : a₀ = b₀ := hal a a' hle hRa hRa'
    (splice_prefix_agree hm hm' hle a b a' b' hspl)
  have hmm : m = m' := hld a a' hRa (hxy ▸ hRa')
  have hlt : n - m < n :=
    Nat.sub_lt (Nat.lt_of_lt_of_le (Nat.pos_of_ne_zero hne) hm) (Nat.pos_of_ne_zero hne)
  subst hxy
  subst hmm
  have hpre : a = a' := relRepeat_prefix_inj hm a a' b b' hspl
  have hsuf : b = b' := relRepeat_suffix_inj hm a b b' (by rw [hspl, hpre])
  subst hpre
  subst hsuf
  rw [ih (n - m) hlt b us vs hra hra' hltq]

/-- **Full-consumption uniqueness, indexed by list length.** Under `LengthDet`,
`RelAligned` (unambiguity extended across lengths) and productivity, there is at most
one value list **of a given length** that consumes a string. This is the true form of
`decodeFull_spec`'s `huniq`; the un-indexed statement is false — see the section note.
`[propext, Quot.sound]`-only, zero `Classical.choice`. -/
theorem relRepeat_unique_same_length {α : Type} (R : α → {m : Nat} → Bytes m → Prop)
    (hld : LengthDet R) (hal : RelAligned R)
    (hprod : ∀ a {m : Nat} (t : Bytes m), R a t → m ≠ 0) :
    ∀ (n : Nat) (s : Bytes n) (xs ys : List α),
      relRepeat R xs n s → relRepeat R ys n s → xs.length = ys.length → xs = ys := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro s xs ys hx hy hlen
    cases xs with
    | nil =>
        have : n = 0 := hx
        cases ys with
        | nil => rfl
        | cons y ys =>
          simp only [List.length_nil, List.length_cons] at hlen
          omega
    | cons x xs =>
        cases ys with
        | nil =>
          simp only [List.length_nil, List.length_cons] at hlen
          omega
        | cons y ys =>
          rcases hx with ⟨m₁, hm₁, s₁, s₂, hs₁, hR₁, href₁⟩
          rcases hy with ⟨m₂, hm₂, s₁', s₂', hs₂, hR₂, href₂⟩
          have hltq : xs.length = ys.length := by
            simp only [List.length_cons] at hlen
            omega
          have hm0 : m₁ ≠ 0 := hprod x s₁ hR₁
          have hspl : splice hm₁ s₁ s₂ = splice hm₂ s₁' s₂' := by rw [← hs₁, ← hs₂]
          rcases Nat.le_total m₁ m₂ with hle | hle
          · exact relRepeat_cons_eq R hld hal n ih x y xs ys m₁ m₂ hm₁ hm₂ hle
              s₁ s₂ s₁' s₂' hspl hR₁ hR₂ href₁ href₂ hm0 hltq
          · have hm2ne : m₂ ≠ 0 := hprod y s₁' hR₂
            exact (relRepeat_cons_eq R hld hal n ih y x ys xs m₂ m₁ hm₂ hm₁ hle
              s₁' s₂' s₁ s₂ hspl.symm hR₂ hR₁ href₂ href₁ hm2ne hltq.symm).symm

/-! ### Discharging `huniq` for `byte`

The indexed theorem above concludes only when the two consuming lists have equal
length. `decodeFull_spec`'s `huniq` has no such hypothesis, so the missing piece is
a way to _pin_ a consuming list's length from the input length. A step relation
whose every value sits at a fixed length `LengthConst R c` does exactly that: a list
of `xs.length` steps accounts for `xs.length * c` bytes, so `n` determines
`xs.length`.

With `LengthConst` the chain is: `lengths_eq_of_const` supplies the index that
`relRepeat_unique_same_length` demands, which yields `huniq_byte`, which is exactly
`decodeFull_spec`'s premise at `Codec.byte`. `decodeFull_spec_byte` is the result —
the first in-tree supplier of the hypothesis. Note what it is **not**: it is the
*target* of this family, not a hot path. Nothing in the library calls it or
`huniq_byte`; it exists to make the premise demonstrably satisfiable on a real
codec, which is exactly the finding it closes.

Why `LengthConst` and not the weaker `LengthDet`: `LengthDet` pins each value's own
step length, but not how many steps a consuming list has (`huniq_not_derivable`
exhibits exactly that gap), so it is insufficient on its own. All `[propext,
Quot.sound]`-only, zero `Classical.choice`. -/

/-- A step relation is **length-constant** when every value relates only to strings
of one fixed length `c`. This is the hypothesis that pins the _number of steps_ of a
consuming list, and it is what `LengthDet` cannot do. -/
def LengthConst {α : Type} (R : α → {m : Nat} → Bytes m → Prop) (c : Nat) : Prop :=
  ∀ ⦃a : α⦄ {m : Nat} (t : Bytes m), R a t → m = c

/-- `byte` is `LengthConst` at `1`: `Rel byte a s` forces `s` to be the one-byte
string. `[propext]`-only. -/
theorem lengthConst_byte : LengthConst (Rel Codec.byte) 1 := by
  intro a m t h
  rw [Rel_byte] at h
  obtain ⟨hm, -⟩ := h
  exact hm

/-- **A constant-step relation's consuming-list length is determined by the input.**
`k` steps of `c` bytes each account for `k * c` bytes, so `relRepeat R xs n s` forces
`xs.length * c = n`. The bridge from a fixed step length to a fixed step _count_.
`[propext]`-only. -/
theorem relRepeat_length_of_const {α : Type} (R : α → {m : Nat} → Bytes m → Prop)
    (c : Nat) (hc : LengthConst R c) (hc0 : c ≠ 0) :
    ∀ (n : Nat) (s : Bytes n) (xs : List α), relRepeat R xs n s → xs.length * c = n := by
  intro n s xs href
  induction xs generalizing n s with
  | nil =>
      rw [relRepeat_nil] at href
      simp only [List.length_nil, Nat.zero_mul]
      exact href.symm
  | cons x rest ih =>
      rw [relRepeat_cons] at href
      obtain ⟨m, hm, s₁, s₂, hsp, hR, hrest⟩ := href
      have hlen := hc s₁ hR
      subst hlen
      have hlt := ih (n - m) s₂ hrest
      rw [List.length_cons, Nat.succ_mul, hlt]
      exact Nat.sub_add_cancel hm

/-- **Two consuming lists of one string have equal length**, under a constant step
length. This is the length index `relRepeat_unique_same_length` asks for, supplied
rather than assumed. `[propext]`-only. -/
theorem lengths_eq_of_const {α : Type} (R : α → {m : Nat} → Bytes m → Prop)
    (c : Nat) (hc : LengthConst R c) (hc0 : c ≠ 0) :
    ∀ (n : Nat) (s : Bytes n) (xs ys : List α),
      relRepeat R xs n s → relRepeat R ys n s → xs.length = ys.length := by
  intro n s xs ys hx hy
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hc0)
    ((relRepeat_length_of_const R c hc hc0 n s xs hx).trans
      (relRepeat_length_of_const R c hc hc0 n s ys hy).symm)

/-- **`LengthConst` implies `LengthDet`**, but not conversely: the constant form fixes
a single length for _all_ values, the determinate form only that each value has one.
This is the direction that composes — `LengthConst` is what pins a consuming list's
length (`relRepeat_length_of_const`), so it is the hypothesis worth carrying.
**No axioms at all** (measured), which is the strongest footprint in the family. -/
theorem lengthDet_of_lengthConst {α : Type} (R : α → {m : Nat} → Bytes m → Prop)
    (c : Nat) (hc : LengthConst R c) : LengthDet R := by
  intro a m₁ m₂ t₁ t₂ h₁ h₂
  rw [hc t₁ h₁, hc t₂ h₂]

/-- `decodeRepeat` membership at full consumption, spelled as `relRepeat`, **at
`Codec.byte`**. Deliberately specialised rather than general: the general form is
just `decodeRepeat_spec` at `Suffix.empty`, and eliminating its `∃ s₀` needs
`prepend_empty_self` — which is stated at `Codec.byte`'s step relation only because
that is the only step relation whose `∃ s₀` collapses for free. Stating it generally
would be a rename, not a theorem, so this is the useful specialisation and the
docstring says so. `[propext, Quot.sound]`-only. -/
theorem decodeRepeat_mem_iff {n : Nat} (s : Bytes n) (xs : List UInt8) :
    (xs, Suffix.empty n) ∈ decodeRepeat Codec.byte byteConsumesByte n s ↔
      relRepeat (Rel Codec.byte) xs n s := by
  rw [decodeRepeat_spec Codec.byte byteConsumesByte]
  constructor
  · rintro ⟨s₀, hs, hrel⟩
    have hpre : (Suffix.empty n).prepend s₀ = s := hs.symm
    rw [prepend_empty_self] at hpre
    subst hpre
    exact hrel
  · intro hrel
    exact ⟨s, (prepend_empty_self n s).symm, hrel⟩

/-- **`huniq` holds at `Codec.byte`** — the first in-tree supplier of
`decodeFull_spec`'s hypothesis, so that hypothesis is not vacuous.
`[propext, Quot.sound]`-only. -/
theorem huniq_byte : ∀ {x y : List UInt8} {n : Nat} (s : Bytes n),
    (x, Suffix.empty n) ∈ decodeRepeat Codec.byte byteConsumesByte n s →
    (y, Suffix.empty n) ∈ decodeRepeat Codec.byte byteConsumesByte n s → x = y := by
  intro x y n s hx hy
  have hrx := (decodeRepeat_mem_iff s x).1 hx
  have hry := (decodeRepeat_mem_iff s y).1 hy
  exact relRepeat_unique_same_length (Rel Codec.byte)
    (lengthDet_of_lengthConst _ 1 lengthConst_byte) relAligned_byte
    ((productive_iff_consumesByte Codec.byte).2 byteConsumesByte) n s x y hrx hry
    (lengths_eq_of_const (Rel Codec.byte) 1 lengthConst_byte (Nat.one_ne_zero) n s x y hrx hry)

/-- **`decodeFull_spec` at `Codec.byte`, with its premise discharged.** It is the
**only** instantiation in the tree that needs no `huniq`, and its only caller is
itself (`decodeFull_spec_byte` wraps `decodeFull_spec`; nothing else calls either).
So read it as a *witness that the hypothesis is satisfiable on a real codec*, not as
a proof about a wired path -- no library path is `Codec.byte`, and wiring one would
be a different (and larger) piece of work. `[propext, Quot.sound]`-only. -/
theorem decodeFull_spec_byte {n : Nat} (s : Bytes n) (xs : List UInt8) :
    decodeFull Codec.byte byteConsumesByte n s = some xs ↔
      (xs, Suffix.empty n) ∈ decodeRepeat Codec.byte byteConsumesByte n s :=
  decodeFull_spec Codec.byte byteConsumesByte huniq_byte s xs

theorem encodeRepeat_ne_none {α : Type} (p : Codec α) :
    ∀ (xs : List α) {n : Nat} (s : Bytes n), relRepeat (Rel p) xs n s → encodeRepeat p xs ≠ none := by
  intro xs
  induction xs with
  | nil =>
      intro n s hrel
      rw [relRepeat_nil] at hrel
      subst hrel
      simp [encodeRepeat]
  | cons x rest ih =>
      intro n s hrel
      rw [relRepeat_cons] at hrel
      rcases hrel with ⟨m, hm, s₁, s₂, hs, hx, hrest⟩
      rw [encodeRepeat]
      have hne : encode p x ≠ none := encode_ne_none p x s₁ hx
      cases h₁ : encode p x with
      | none => exact False.elim (hne h₁)
      | some e₁ =>
          have hne' : encodeRepeat p rest ≠ none := ih s₂ hrest
          cases h₂ : encodeRepeat p rest with
          | none => exact False.elim (hne' h₂)
          | some e₂ => simp

end Codec
