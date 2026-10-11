/- Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later -/

import Codec.Decode
import Codec.DecodeArray
import Codec.Encode
import Codec.EncodeArray

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
agree by construction, so the old committed-choice `alt` gate — and the
prefix-disjointness machinery it once required — is unnecessary and has been dropped.
-/

namespace Codec

/-- Encoder soundness: any value the encoder prints is in the description's
denotational domain (`Rel d x s`). Inductive on `d`, no hypothesis. -/
theorem encode_rel {α : Type} (d : Codec α) (x : α) :
    ∀ {s : Bytes}, encode d x = some s → Rel d x s := by
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
    (s r : Bytes) :
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
    ∀ {s r : Bytes}, (x, r) ∈ decode d s ↔
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
theorem bidir {α : Type} (d : Codec α) (x : α) (s : Bytes) :
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
    ∀ {s : Bytes}, encode d x = some s → ∀ r, (x, r) ∈ decode d (s ++ r) := by
  intro s he r
  have hrel : Rel d x s := encode_rel d x he
  exact (decode_spec d x (s := s ++ r) (r := r)).2 ⟨s, rfl, hrel⟩

/-- The byte-exact roundtrip: a value encoded to `s` decodes back to `x` with
no remainder. Unconditional. -/
theorem roundtrip {α : Type} (d : Codec α) (x : α) (s : Bytes) :
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
    ∀ (xs : List α) (s r : Bytes), (xs, r) ∈ decodeRepeat p h s ↔
      ∃ s₀, s = s₀ ++ r ∧ relRepeat (Rel p) xs s₀ := by
  have hwf : WellFounded (InvImage (· < ·) (fun s : Bytes => s.length)) :=
    InvImage.wf (fun s : Bytes => s.length) Nat.lt_wfRel.wf
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
          have hlt : InvImage (· < ·) (fun s : Bytes => s.length) s₁ s := h x s₁ s hmem
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
              have hlt : InvImage (· < ·) (fun s : Bytes => s.length) (sb ++ r) s :=
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

/-- Encoder soundness for repetition: any list the repetition-encoder prints is
in the repetition denotation `relRepeat (Rel p)`. The `encode` counterpart to
`decodeRepeat_spec` (which is the decoder's analogue); here no productivity
witness is needed, because `encodeRepeat` recurses on the *value* list rather
than the input bytes. Structural induction on `xs`. -/
theorem encodeRepeat_rel {α : Type} (p : Codec α) :
    ∀ (xs : List α) {s : Bytes}, encodeRepeat p xs = some s → relRepeat (Rel p) xs s := by
  intro xs
  induction xs with
  | nil =>
      intro s he
      have hs : s = [] := by simpa [encodeRepeat] using he
      subst s
      simp [relRepeat]
  | cons x rest ih =>
      intro s he
      rw [encodeRepeat] at he
      cases hx : encode p x with
      | none => simp [hx] at he
      | some sx =>
          rw [hx] at he
          cases hr : encodeRepeat p rest with
          | none => simp [hr] at he
          | some sr =>
              rw [hr] at he
              cases he
              rw [relRepeat_cons]
              refine ⟨sx, sr, rfl, encode_rel p x hx, ih hr⟩

/-! ## The decode→encode direction, and *why* it is only conditional

The laws above (`encode_rel`, `decode_spec`, `bidir`, `decode_encode`,
`roundtrip`) pin down the **encode→decode** direction: anything the encoder
prints decodes back to the same value, byte-for-byte (`roundtrip`). They say
nothing about the **decode→encode** direction — that a value the decoder
accepts re-encodes to exactly the same bytes. And for good reason: it is
**false** in general, and only holds for *functional* descriptions.

The obstruction is the backtracking-union `|`, which can relate **one value to
several byte strings**. Consider `alt (pure 0) byte : Codec UInt8`: it relates
`0` to `[]` (via `pure 0`) *and* to `[0]` (via `byte`). The encoder,
`encode (alt (pure 0) byte) 0 = encode (pure 0) 0 <|> encode byte 0 = some []`,
prefers the left branch, so it prints `[]`. Yet on input `[0]` the decoder
accepts `0` with `[]` remaining via the *byte* branch:

    (0, []) ∈ decode (alt (pure 0) byte) [0]

while `encode (alt (pure 0) byte) 0 = some [] ≠ some [0]`. So the two
directions do **not** commute byte-for-byte without a further hypothesis. Note
this is a **string**-non-uniqueness (`0` ↦ `[]` and `0` ↦ `[0]`), *not* a
value-non-uniqueness: on any *fixed* string `alt (pure 0) byte` relates at most
one value (`Unambiguous` below still holds for it). The precise condition for
the decode→encode half is therefore **functionality in the string direction**:
`Rel d x s ∧ Rel d x s' → s = s'`. This is the *content* of the "lossless
capture" claim (departure #4): it is a property of the **encode→decode**
roundtrip (which holds unconditionally), *not* a claim that every decode result
re-encodes — the latter needs the string-directed functionality that an
ambiguous/overlapping `alt` cannot provide. -/

/-- A description is **unambiguous** when it relates at most one value per byte
string: `Rel d x s` and `Rel d y s` force `x = y`. (This is the *value*-directed
half; the string-directed half — `Rel d x s ∧ Rel d x s' → s = s'` — is needed for
the decode→encode direction, see `Functional`/`encode_of_decode`. Ambiguity here
is *not* a gate on the unconditional laws; it is a precisely-named hypothesis.) -/
def Unambiguous {α : Type} (d : Codec α) : Prop :=
  ∀ ⦃x y⦄ s, Rel d x s → Rel d y s → x = y

/-- A description is **functional** (string-directional) when each value relates
to at most one byte string: `Rel d x s` and `Rel d x s'` force `s = s'`. This is
the exact extra condition under which the decode→encode direction (`encode_of_decode`)
and full bijectivity hold; the backtracking-union `|` does *not* preserve it in
general (cf. `alt (pure 0) byte`, where `0` maps to both `[]` and `[0]`). -/
def Functional {α : Type} (d : Codec α) : Prop :=
  ∀ x ⦃s s'⦄, Rel d x s → Rel d x s' → s = s'

/-- **Encoder completeness**: every value in the denotation encodes successfully
(possibly to a different byte string than the witness — pinning the exact string
requires `Functional`, see `encode_of_decode`). This is the missing `Rel → encode`
soundness half; proved by induction on `d`. -/
theorem encode_ne_none {α : Type} (d : Codec α) (x : α) (s : Bytes) :
    Rel d x s → encode d x ≠ none := by
  induction d generalizing s with
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
      rcases hrel with ⟨s₁, s₂, hs, hr₁, hr₂⟩
      rw [encode]
      have hne₁ : encode d₁ x₁ ≠ none := ih₁ x₁ s₁ hr₁
      cases h₁ : encode d₁ x₁ with
      | none => exact False.elim (hne₁ h₁)
      | some e₁ =>
          have hne₂ : encode d₂ x₂ ≠ none := ih₂ x₂ s₂ hr₂
          cases h₂ : encode d₂ x₂ with
          | none => exact False.elim (hne₂ h₂)
          | some e₂ => simp
  | alt d₁ d₂ ih₁ ih₂ =>
      intro hrel
      rw [encode]
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
      rcases hrel with ⟨hx, hs⟩
      simp [hx]
  | byte =>
      intro hrel
      rw [encode]
      rw [Rel_byte] at hrel
      subst s
      simp

/-- Under functionality, a value the decoder accepts (with no remainder) re-encodes
to exactly the same bytes. Paired with `roundtrip` (encode→decode) this makes
`encode d x = some s ↔ (x, []) ∈ decode d s` a genuine bijection for functional `d`.
This is the missing **decode→encode** half. -/
theorem encode_of_decode {α : Type} (d : Codec α) (hd : Functional d) (x : α)
    {s : Bytes} (hdcd : (x, []) ∈ decode d s) : encode d x = some s := by
  rcases (decode_spec d x).1 hdcd with ⟨s₀, hsplit, hrel⟩
  have hs₀ : s = s₀ := by simpa using hsplit
  subst s₀
  have hne : encode d x ≠ none := encode_ne_none d x s hrel
  cases he : encode d x with
  | none => exact False.elim (hne he)
  | some s' =>
      have hrel' : Rel d x s' := encode_rel d x he
      have hs' : s' = s := hd x hrel' hrel
      rw [hs']

/-- `encode` is injective on the bytes it prints, for **unambiguous**
descriptions: a single byte string cannot encode two distinct values. -/
theorem encode_injective_of_unambiguous {α : Type} (d : Codec α) (hd : Unambiguous d)
    {x y : α} {s : Bytes} (hx : encode d x = some s) (hy : encode d y = some s) :
    x = y := by
  have hrelx : Rel d x s := encode_rel d x hx
  have hrely : Rel d y s := encode_rel d y hy
  exact hd s hrelx hrely

/-! ## Relation-level completeness and functionality

`Functional` and `Unambiguous` are stated over a `Codec` (quantifying over
`Rel d`). The repetition and chain combinators are *relations*
`α → Bytes → Prop` (not `Codec` values), so their decode→encode and
injectivity laws take the same notions over an arbitrary relation. This section
collects the relation-level forms and the `encodeRepeat` completeness mirror of
`encode_ne_none`. -/

/-- A relation is **functional** (string-directional) when each value relates to
at most one byte string. -/
def relFunctional {α : Type} (R : α → Bytes → Prop) : Prop :=
  ∀ a ⦃s s'⦄, R a s → R a s' → s = s'

/-- A relation is **unambiguous** (value-directional) when each byte string
relates to at most one value. -/
def relUnambiguous {α : Type} (R : α → Bytes → Prop) : Prop :=
  ∀ ⦃a b⦄ s, R a s → R b s → a = b

/-- **Encoder completeness for repetition**: every list in the repetition
denotation encodes successfully (possibly to a different byte string than the
witness — pinning the exact string requires functionality of the step). This is
the `relRepeat`-level mirror of `encode_ne_none`; structural induction on `xs`,
with the head step via `encode_ne_none p`. -/
theorem encodeRepeat_ne_none {α : Type} (p : Codec α) :
    ∀ (xs : List α) (s : Bytes), relRepeat (Rel p) xs s → encodeRepeat p xs ≠ none := by
  intro xs
  induction xs with
  | nil =>
      intro s hrel
      rw [relRepeat_nil] at hrel
      subst s
      simp [encodeRepeat]
  | cons x rest ih =>
      intro s hrel
      rw [relRepeat_cons] at hrel
      rcases hrel with ⟨s₁, s₂, hs, hx, hrest⟩
      rw [encodeRepeat]
      have hne : encode p x ≠ none := encode_ne_none p x s₁ hx
      cases h₁ : encode p x with
      | none => exact False.elim (hne h₁)
      | some e₁ =>
          have hne' : encodeRepeat p rest ≠ none := ih s₂ hrest
          cases h₂ : encodeRepeat p rest with
          | none => exact False.elim (hne' h₂)
          | some e₂ => simp

/-! ## The efficient interpreters: transferred laws (Tier A)

`decodeFast` (list-fused) and `decodeFull`/`decodeRepeatFull` (full-consumption,
`Option`-valued repetition) are *proved equal* to the spec interpreters
(`decodeFast_eq`, `decodeFull_spec`), so every law above transfers by a one-line
rewrite — **no new semantics**, no new induction. These lemmas are the API surface
the efficient path exposes; each is a definitional rerouting into the already-proven
law. -/

/-- The bidirectional law for the fused decoder: `decodeFast d s` returns `x` with `r`
remaining iff the input splits as a relating prefix plus `r`. Transferred from
`decode_spec` through `decodeFast_eq`. -/
theorem decodeFast_spec {α : Type} (d : Codec α) (x : α) (s r : Bytes) :
    (x, r) ∈ decodeFast d s ↔ ∃ s₀, s = s₀ ++ r ∧ Rel d x s₀ := by
  rw [decodeFast_eq]
  exact decode_spec d x (s := s) (r := r)

/-- The whole-string bidirectional law for the fused decoder (`decode_spec` at
`r = []`): `Rel d x s` iff `decodeFast d s` accepts `s` fully as `x`. Transferred
from `bidir` through `decodeFast_eq`. -/
theorem bidir_decodeFast {α : Type} (d : Codec α) (x : α) (s : Bytes) :
    Rel d x s ↔ (x, []) ∈ decodeFast d s := by
  rw [decodeFast_eq]
  exact bidir d x s

/-- The byte-exact roundtrip for the fused decoder: a value encoded to `s` decodes
back via `decodeFast` to `x` with no remainder. Transferred from `roundtrip` through
`decodeFast_eq`. -/
theorem roundtrip_decodeFast {α : Type} (d : Codec α) (x : α) (s : Bytes) :
    encode d x = some s → (x, []) ∈ decodeFast d s := by
  intro he
  rw [decodeFast_eq]
  exact roundtrip d x s he

/-- The full-consumption repetition law, restated under the `decodeRepeatFull` name
(the same `↔` as `decodeFull_spec`, already proved in `Codec.Decode`). Under the
full-consumption-uniqueness hypothesis, the fused `Option`-valued "many" decoder returns
`some xs` iff `xs` fully consumes the input. -/
theorem decodeRepeatFull_spec {α : Type} (p : Codec α) (h : ConsumesByte p)
    (huniq : ∀ {x y : List α} {s : Bytes},
      (x, []) ∈ decodeRepeat p h s → (y, []) ∈ decodeRepeat p h s → x = y)
    (xs : List α) (s : Bytes) :
    decodeRepeatFull p h s = some xs ↔ (xs, []) ∈ decodeRepeat p h s :=
  decodeFull_spec p h huniq xs s

/-! ## The array-carrier interpreters: transferred laws (buffer tier)

`decodeArray`/`encodeArray` (`Codec.DecodeArray`/`Codec.EncodeArray`) are the
F\*-style run-models over the `Array UInt8` carrier, *proved equal* to the list
specs (`decodeArray_eq`/`encodeArray_eq`), so every law above transfers by a
one-line rewrite — **no new semantics**, no new induction. Each lemma below is a
definitional rerouting into the already-proven `Bytes`-level law. -/

/-- The bidirectional law for the array-carrier decoder: `(x, j) ∈ decodeArray d a i`
iff the dropped input splits as a `Rel`-prefix `s₀` plus the dropped remainder, with
`j` exactly the position `i + s₀.length` (the canonical index; the explicit arithmetic
pins down `j`, which `drop` alone does not when the remainder is empty). Transferred
from `decode_spec` through `decodeArray_eq` and `List.mem_map`. -/
theorem decodeArray_spec {α : Type} (d : Codec α) (a : Array UInt8) (i : Nat) (x : α) (j : Nat) :
    (x, j) ∈ decodeArray d a i ↔
      ∃ s₀, a.toList.drop i = s₀ ++ a.toList.drop j ∧ Rel d x s₀ ∧ j = i + s₀.length := by
  rw [decodeArray_eq, List.mem_map]
  constructor
  · intro h
    rcases h with ⟨pr, hpr, heq⟩
    rcases pr with ⟨x₀, r⟩
    have hx : x₀ = x := congrArg Prod.fst heq
    have hjidx : i + ((a.toList.drop i).length - r.length) = j := congrArg Prod.snd heq
    subst x₀
    rcases (decode_spec d x (s := a.toList.drop i) (r := r)).1 hpr with ⟨s₀, hs, hrel⟩
    refine ⟨s₀, ?_, hrel, ?_⟩
    · have hlen : (a.toList.drop i).length = s₀.length + r.length := by rw [hs, List.length_append]
      have hj' : j = i + s₀.length := by rw [hjidx.symm, hlen, Nat.add_sub_cancel_right]
      rw [hj']
      rw [drop_add_length_of_append hs.symm]
      exact hs
    · have hlen := congrArg List.length hs
      rw [List.length_append] at hlen
      rw [hjidx.symm, hlen, Nat.add_sub_cancel_right]
  · intro h
    rcases h with ⟨s₀, hs, hrel, hj⟩
    refine ⟨(x, a.toList.drop j), ?_, ?_⟩
    · exact (decode_spec d x (s := a.toList.drop i) (r := a.toList.drop j)).2 ⟨s₀, hs, hrel⟩
    · change (x, i + ((a.toList.drop i).length - (a.toList.drop j).length)) = (x, j)
      congr 1
      have hlen := congrArg List.length hs
      rw [List.length_append] at hlen
      rw [hlen, Nat.add_sub_cancel_right]
      exact hj.symm

/-- Encoder soundness for the array-carrier encoder: any value it prints to an
`Array` is in the description's denotational domain over the array's bytes.
Transferred from `encode_rel` through `encodeArray_eq`. -/
theorem encodeArray_rel {α : Type} (d : Codec α) (x : α) :
    ∀ {a : Array UInt8}, encodeArray d x = some a → Rel d x a.toList := by
  intro a he
  rw [encodeArray_eq] at he
  exact encode_rel d x he

/-- The byte-exact roundtrip for the array carriers: a value encoded to an `Array`
decodes back, over `decodeArray` from index `0`, consuming the whole array. Transferred
from `roundtrip` through `encodeArray_eq` and `decodeArray_eq`. -/
theorem roundtripArray {α : Type} (d : Codec α) (x : α) (a : Array UInt8) :
    encodeArray d x = some a → (x, a.toList.length) ∈ decodeArray d a 0 := by
  intro he
  rw [decodeArray_eq, List.mem_map]
  rw [encodeArray_eq] at he
  have hrt : (x, []) ∈ decode d (a.toList.drop 0) := roundtrip d x a.toList he
  refine ⟨(x, []), ?_, ?_⟩
  · simpa using hrt
  · simp

end Codec
