/- Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later -/

import Codec.Codec

/-!
# The nondeterministic decoder

This file gives `decode`, the paper's list-monad decoder (§4.1):

    decode : Codec α → Bytes → List (α × Bytes)

It returns *all* (value, remaining-bytes) pairs — a relation, not a single
result. Choice (`alt`) is the full backtracking union `decode d₁ s ++ decode d₂ s`,
exactly as in the paper. This is why the bidirectional law (`decode_spec`) holds
**unconditionally** for every description, with no prefix-disjointness or
unambiguity gate *on `decode_spec` itself*: `Rel (alt d₁ d₂) = Rel d₁ ∨ Rel d₂`
and `decode (alt d₁ d₂) = decode d₁ ++ decode d₂` agree by construction. (The
*encode-side* converse laws do need `Functional`/`Unambiguous`, see `Codec.Sound`;
those hypotheses qualify the decode→encode direction, not the decoder's own law.)

The paper notes (§4.4) that this proof-of-concept decoder has exponential
worst-case complexity and a space leak under unlimited backtracking; replacing it
with an efficient implementation of the *same* semantics is the open problem the
paper names, and is future work here (not the semantics of `decode`).
-/

namespace Codec

/-- The nondeterministic decoder: every `(value, remaining)` pair derivable from
the description against the input. This is the paper's `Parser` (§4.1) re-based
onto `Bytes`, with `|` as list concatenation (unlimited backtracking). -/
def decode {α : Type} (d : Codec α) (s : Bytes) : List (α × Bytes) :=
  match d with
  | Codec.iso i d =>
      (decode d s).filterMap fun (a, s') => (i.apply a).map fun x => (x, s')
  | Codec.seq d₁ d₂ =>
      (decode d₁ s).flatMap fun (x, s₁) =>
        (decode d₂ s₁).flatMap fun (y, s₂) => [((x, y), s₂)]
  | Codec.alt d₁ d₂ => decode d₁ s ++ decode d₂ s
  | Codec.empty => []
  | Codec.pure x => [(x, s)]
  | Codec.byte =>
      match s with
      | [] => []
      | b :: rest => [(b, rest)]

/-- The **fused** decoder: a `flatMap`/`map`-fused re-staging of `decode` that does not
re-traverse the singleton result of a `seq` pair (the inner ``flatMap (…) [((x, y), s₂)]``
becomes a single ``map``). This is `decodeFast` (Tier A of
`efficient-backtracking-decoder`): same denotation as `decode`, only the *runtime*
restructuring (list fusion) differs — `decodeFast_eq` proves the two equal. -/
def decodeFast {α : Type} (d : Codec α) (s : Bytes) : List (α × Bytes) :=
  match d with
  | Codec.iso i d =>
      (decodeFast d s).filterMap fun (a, s') => (i.apply a).map fun x => (x, s')
  | Codec.seq d₁ d₂ =>
      (decodeFast d₁ s).flatMap fun (x, s₁) =>
        (decodeFast d₂ s₁).map fun (y, s₂) => ((x, y), s₂)
  | Codec.alt d₁ d₂ => decodeFast d₁ s ++ decodeFast d₂ s
  | Codec.empty => []
  | Codec.pure x => [(x, s)]
  | Codec.byte =>
      match s with
      | [] => []
      | b :: rest => [(b, rest)]

/-- `decodeFast` equals `decode` for every description and input. Proved by induction
on `d`; the only non-trivial case is `seq`, where the fused `map` equals the spec's
`flatMap`-over-singleton via the list-fusion identity ``l.flatMap (fun a => [f a]) =
l.map f``. No `Classical.choice`; `[propext, Quot.sound]` only. -/
theorem decodeFast_eq {α : Type} (d : Codec α) :
    ∀ (s : Bytes), decodeFast d s = decode d s := by
  induction d with
  | iso i d ih =>
      intro s
      simp [decodeFast, decode, ih]
  | seq d₁ d₂ ih₁ ih₂ =>
      intro s
      simp [decodeFast, decode, ih₁, ih₂, List.map_eq_flatMap]
  | alt d₁ d₂ ih₁ ih₂ =>
      intro s
      simp [decodeFast, decode, ih₁, ih₂]
  | empty =>
      intro s
      simp [decodeFast, decode]
  | pure x =>
      intro s
      simp [decodeFast, decode]
  | byte =>
      intro s
      simp [decodeFast, decode]

/-! ## The repetition decoder (productive `many` as well-founded recursion) -/

/-- An executable mirror of `Productive`: every decoding step strictly shortens
the input. Equivalent to `Productive` by `productive_iff_consumesByte` (below);
this is the form the repetition decoder consumes as its well-foundedness witness
(the `p`-consumes-a-byte fact, passed as an argument — not a global predicate). -/
def ConsumesByte {α : Type} (p : Codec α) : Prop :=
  ∀ x s₁ s₀, (x, s₁) ∈ decode p s₀ → s₁.length < s₀.length

/-- The productive repetition decoder: `decodeRepeat p h s` enumerates exactly
the paper's `many p` results — the empty list with `s` unchanged, plus every
one-or-more prefix — by **well-founded recursion on `s.length`**. The recursion
is guarded by `h : ConsumesByte p`, the fact that each `decode p` step strictly
shortens the remaining string, passed as an argument (not recovered from a global
predicate). Total and `#eval`-able for every productive `p`.

This is the *computable* reading of the §3.4 derived `many`; its denotation
is `relRepeat (Rel p)`, and the decoder satisfies `decodeRepeat_spec`. -/
def decodeRepeat {α : Type} (p : Codec α) (h : ConsumesByte p) (s : Bytes) :
    List (List α × Bytes) :=
  WellFounded.fix (InvImage.wf (fun s : Bytes => s.length) Nat.lt_wfRel.wf)
    (fun s ih =>
      ([], s) :: (decode p s).attach.flatMap fun a =>
        match a with
        | ⟨(x, s₁), _hmem⟩ => (ih s₁ (h x s₁ s _hmem)).map fun (xs, r) => (x :: xs, r))
    s

/-- The recursion equation for `decodeRepeat`: the empty result plus every
`cons` step on a strictly-shorter remainder. Derived from `WellFounded.fix_eq`. -/
theorem decodeRepeat_eq {α : Type} (p : Codec α) (h : ConsumesByte p) (s : Bytes) :
    decodeRepeat p h s =
      ([], s) :: (decode p s).attach.flatMap fun a =>
        match a with
        | ⟨(x, s₁), _hmem⟩ => (decodeRepeat p h s₁).map fun (xs, r) => (x :: xs, r) := by
  unfold decodeRepeat
  rw [WellFounded.fix_eq]

/-- The single-byte primitive is productive: decoding one byte always consumes
exactly one byte. This is the `ConsumesByte` witness that makes
`decodeRepeat Codec.byte _` total (and `#eval`-able); the general case is
`Sound.productive_iff_consumesByte`. -/
theorem byte_consumesByte : ConsumesByte Codec.byte := by
  intro x s₁ s₀ hmem
  cases s₀ with
  | nil => simp [decode] at hmem
  | cons b rest =>
      simp [decode] at hmem
      rcases hmem with ⟨rfl, rfl⟩
      simp

/-- `decodeOnce`-free concrete repetition decoder over bytes: the paper's
`many byte` (a *semantic* reading, not a `Codec` node) realized as a *total*
well-founded function. `#eval byteRepeat [1,2,3]` yields the four results
`([], [1,2,3])`, `([1], [2,3])`, `([1,2], [3])`, `([1,2,3], [])`. -/
def byteRepeat (s : Bytes) : List (Bytes × Bytes) :=
  decodeRepeat Codec.byte byte_consumesByte s

/-! ## The full-consumption repetition decoder (Tier A)

The §4.4 / §10.5 blowup is the *all-prefix* enumeration: `decodeRepeat p h s`
materializes every `([], s)`, `([x₁], s₁)`, …, `([x₁…xₙ], [])` prefix, which is
Θ(n²) output when only the single full-consumption list is asked for. `decodeFull`
is the *same* denotation restricted to that one result: it returns `some xs` for the
full consumption (empty remainder), `none` otherwise, without building every
intermediate prefix. It is total and `#eval`-able for every productive `p` via the
*exact same* `ConsumesByte` guard and well-founded measure as `decodeRepeat`, so its
equality law closes by the same `WellFounded.fix_eq` + `List`-lemma machinery. -/

/-- Thread the well-founded recursion over the `attach`-ed candidate `decode p s`
results, picking the first step `(x, s₁)` whose shorter-remainder recursion yields a
full consumption. Each ``⟨(x, s₁), hm⟩`` carries the membership
``hm : (x, s₁) ∈ decode p s`` that the productivity guard ``h`` needs to justify
recursing on the strictly-shorter ``s₁``. Unlike ``decodeRepeat``'s ``flatMap`` (which
builds the whole prefix list), this threads a single ``Option (List α)``: the
``x :: xs`` cons is constant-time and no all-prefix list is ever materialized. -/
def decodeFullStep {α : Type} (p : Codec α) (h : ConsumesByte p)
    (s : Bytes)
    (ih : (s' : Bytes) → InvImage WellFoundedRelation.rel (fun s : Bytes => s.length) s' s → Option (List α)) :
    List { pr : α × Bytes // pr ∈ decode p s } → Option (List α)
  | [] => none
  | ⟨(x, s₁), hm⟩ :: rest =>
      match ih s₁ (h x s₁ s hm) with
      | none => decodeFullStep p h s ih rest
      | some xs => some (x :: xs)

/-- The full-consumption repetition decoder: `decodeFull p h s = some xs` exactly
when `decodeRepeat p h s` contains `(xs, [])`, i.e. `xs` is a list that `many p`
matches against the *whole* input (empty remainder, and the list must be fully
consumed). Defined by an explicit `WellFounded.fix` on `s.length` — the same
measure as `decodeRepeat` — so it is a total, `#eval`-able function (never a
`partial`/opaque value, cf. §9).

Efficiency (Tier A of `efficient-backtracking-decoder`): each step threads a single
`Option` and stops at the first full consumption, so the `[]`/`x :: xs` branches are
constant-time conses — no Θ(n²) all-prefix list is materialized. -/
def decodeFull {α : Type} (p : Codec α) (h : ConsumesByte p) (s : Bytes) : Option (List α) :=
  WellFounded.fix (InvImage.wf (fun s : Bytes => s.length) Nat.lt_wfRel.wf)
    (fun s ih =>
      match s with
      | [] => some []
      | b :: rest => decodeFullStep p h (b :: rest) ih (decode p (b :: rest)).attach)
    s

/-- Forward soundness of `decodeFullStep`: if it returns `some ys`, then `ys = x :: xs`
for some attached candidate `⟨(x, s₁), hm⟩` with a fully-consuming recursion
`ih s₁ … = some xs`. This is the step-level bridge to `decodeRepeat`'s `flatMap` and
holds unconditionally (no uniqueness needed on the forward direction). -/
theorem decodeFullStep_some {α : Type} (p : Codec α) (h : ConsumesByte p)
    (s : Bytes)
    (ih : (s' : Bytes) → InvImage WellFoundedRelation.rel (fun s : Bytes => s.length) s' s → Option (List α)) :
    ∀ (l : List { pr : α × Bytes // pr ∈ decode p s }) (ys : List α),
      decodeFullStep p h s ih l = some ys →
        ∃ (x : α) (xs : List α) (s₁ : Bytes) (hm : (x, s₁) ∈ decode p s),
          ⟨(x, s₁), hm⟩ ∈ l ∧
            ih s₁ (h x s₁ s hm) = some xs ∧ ys = x :: xs := by
  intro l ys
  induction l generalizing ys with
  | nil => simp [decodeFullStep]
  | cons hd tl ihL =>
      rcases hd with ⟨⟨x, s₁⟩, hm⟩
      rw [decodeFullStep]
      cases ho : ih s₁ (h x s₁ s hm) with
      | none =>
          intro h
          rcases ihL _ h with ⟨x', xs', s₁', hm', hmem, hih', hys⟩
          refine ⟨x', xs', s₁', hm', ?_, hih', hys⟩
          rw [List.mem_cons]
          right
          exact hmem
      | some xs₀ =>
          intro h
          simp only at h
          cases h
          refine ⟨x, xs₀, s₁, hm, ?_, ho, rfl⟩
          simp

/-- **Forward soundness** of the full-consumption decoder: if `decodeFull p h s`
returns `some xs`, then `xs` is a full-consumption result of `decodeRepeat` (i.e.
`(xs, [])` is enumerated). Proved by well-founded induction on `s.length`, threading
through `decodeFullStep_some` and the `decodeRepeat` recursion equation. Holds
unconditionally — no uniqueness needed on the forward direction. -/
theorem decodeFull_some {α : Type} (p : Codec α) (h : ConsumesByte p) :
    ∀ (xs : List α) (s : Bytes), decodeFull p h s = some xs → (xs, []) ∈ decodeRepeat p h s := by
  have hwf : WellFounded (InvImage (· < ·) (fun s : Bytes => s.length)) :=
    InvImage.wf (fun s : Bytes => s.length) Nat.lt_wfRel.wf
  intro xs s
  revert xs
  induction s using WellFounded.induction (hwf := hwf) with
  | h s ih =>
      intro xs
      unfold decodeFull
      rw [WellFounded.fix_eq]
      cases s with
      | nil =>
          intro he
          simp at he
          subst xs
          rw [decodeRepeat_eq]
          simp
      | cons b rest =>
          intro he
          rw [decodeRepeat_eq]
          rw [List.mem_cons]
          right
          -- he : decodeFullStep p h (b::rest) (fun s' hlt => ...) (decode p (b::rest)).attach = some xs
          rw [List.mem_flatMap]
          rcases (decodeFullStep_some p h (b :: rest) _ (decode p (b :: rest)).attach xs he) with
            ⟨x, xs', s₁, hm, hmem, hih', hxs⟩
          subst xs
          refine ⟨⟨(x, s₁), hm⟩, hmem, ?_⟩
          rw [List.mem_map]
          refine ⟨(xs', []), ?_, rfl⟩
          have hlt : InvImage WellFoundedRelation.rel (fun s : Bytes => s.length) s₁ (b :: rest) :=
            h x s₁ (b :: rest) hm
          exact (ih s₁ hlt xs' hih')

/-- `decodeFullStep` succeeds (is `≠ none`) whenever *some* candidate in the list
has a fully-consuming recursion. (It returns the *first* such candidate, but for
completeness we only need that it succeeds at all.) -/
theorem decodeFullStep_ne_none {α : Type} (p : Codec α) (h : ConsumesByte p)
    (s : Bytes)
    (ih : (s' : Bytes) → InvImage WellFoundedRelation.rel (fun s : Bytes => s.length) s' s → Option (List α)) :
    ∀ (l : List { pr : α × Bytes // pr ∈ decode p s }),
      (∃ (x : α) (xs : List α) (s₁ : Bytes) (hm : (x, s₁) ∈ decode p s),
        ⟨(x, s₁), hm⟩ ∈ l ∧ ih s₁ (h x s₁ s hm) = some xs) →
      decodeFullStep p h s ih l ≠ none := by
  intro l
  induction l with
  | nil =>
      intro hnone
      rcases hnone with ⟨x, xs, s₁, hm, hmem, _⟩
      cases hmem
  | cons hd tl ihL =>
      rcases hd with ⟨⟨x, s₁⟩, hm⟩
      intro hex
      rw [decodeFullStep]
      cases ho : ih s₁ (h x s₁ s hm) with
      | none =>
          rcases hex with ⟨x', xs', s₁', hm', hmem, hih'⟩
          rw [List.mem_cons] at hmem
          rcases hmem with hmem | hmem
          · -- witness is the head, but head's `ih` returned `none`: contradiction
            cases hmem
            rw [ho] at hih'
            cases hih'
          · -- witness is in the tail
            exact ihL ⟨x', xs', s₁', hm', hmem, hih'⟩
      | some xs =>
          simp

/-- **Completeness** of the full-consumption decoder: if `xs` is a full-consumption
result of `decodeRepeat` (i.e. `(xs, [])` is enumerated), then `decodeFull p h s`
succeeds (`≠ none`). Together with `decodeFull_some` and a uniqueness hypothesis this
makes `decodeFull` the single full-consumption reading. -/
theorem decodeFull_ne_none {α : Type} (p : Codec α) (h : ConsumesByte p) :
    ∀ (xs : List α) (s : Bytes), (xs, []) ∈ decodeRepeat p h s → decodeFull p h s ≠ none := by
  have hwf : WellFounded (InvImage (· < ·) (fun s : Bytes => s.length)) :=
    InvImage.wf (fun s : Bytes => s.length) Nat.lt_wfRel.wf
  intro xs s
  revert xs
  induction s using WellFounded.induction (hwf := hwf) with
  | h s ih =>
      intro xs hmem
      unfold decodeFull
      rw [WellFounded.fix_eq]
      cases s with
      | nil =>
          change some [] ≠ none
          simp
      | cons b rest =>
          rw [decodeRepeat_eq] at hmem
          rw [List.mem_cons] at hmem
          rcases hmem with hmem | hmem
          · cases hmem
          · rw [List.mem_flatMap] at hmem
            rcases hmem with ⟨a, hamem, hres⟩
            rcases a with ⟨⟨x, s₁⟩, hm⟩
            rw [List.mem_map] at hres
            rcases hres with ⟨pr, hpr, hprmap⟩
            rcases pr with ⟨xs', r⟩
            cases hprmap
            -- hm : (x, s₁) ∈ decode p (b::rest); hpr : (xs', []) ∈ decodeRepeat p h s₁
            have hlt : InvImage WellFoundedRelation.rel (fun s : Bytes => s.length) s₁ (b :: rest) :=
              h x s₁ (b :: rest) hm
            have hne_s₁ : decodeFull p h s₁ ≠ none := ih s₁ hlt xs' hpr
            cases ho : decodeFull p h s₁ with
            | none => exact False.elim (hne_s₁ ho)
            | some ys =>
                apply decodeFullStep_ne_none p h (b :: rest)
                  (fun s' _hlt => decodeFull p h s') (decode p (b :: rest)).attach
                refine ⟨x, ys, s₁, hm, ?_, ?_⟩
                · exact List.mem_attach (decode p (b :: rest)) ⟨(x, s₁), hm⟩
                · rw [ho]

/-- The full-consumption law: `decodeFull p h s = some xs` iff `xs` is the
full-consumption result of `decodeRepeat` — **provided full consumption is unique**.
Under that hypothesis (the `decodeFull`-level mirror of the chain laws' `relUnambiguous`),
the ``first-success`` reading of `decodeFull` coincides with the enumeration of
`decodeRepeat`, so the two are equal. The forward direction is unconditional
(`decodeFull_some`); the reverse uses completeness (`decodeFull_ne_none`) plus the
uniqueness hypothesis to pin the returned value to `xs`. -/
theorem decodeFull_spec {α : Type} (p : Codec α) (h : ConsumesByte p)
    (huniq : ∀ {x y : List α} {s : Bytes},
      (x, []) ∈ decodeRepeat p h s → (y, []) ∈ decodeRepeat p h s → x = y)
    (xs : List α) (s : Bytes) :
    decodeFull p h s = some xs ↔ (xs, []) ∈ decodeRepeat p h s := by
  constructor
  · exact decodeFull_some p h xs s
  · intro hmem
    have hne : decodeFull p h s ≠ none := decodeFull_ne_none p h xs s hmem
    cases ho : decodeFull p h s with
    | none => exact False.elim (hne ho)
    | some ys =>
        have hys : (ys, []) ∈ decodeRepeat p h s := decodeFull_some p h ys s ho
        have hxy : ys = xs := huniq hys hmem
        rw [hxy]

/-- `decodeRepeatFull` is the accumulator/fused full-consumption "many" decoder:
the *same* function as `decodeFull` (task 1.1 names it `decodeFull`; task 1.3 names the
same single-pass, `Option`-valued, list-fused reading `decodeRepeatFull`). Kept as a
reducible alias so both names resolve to the one efficient decoder — no duplicate
machinery. -/
abbrev decodeRepeatFull {α : Type} (p : Codec α) (h : ConsumesByte p) (s : Bytes) : Option (List α) :=
  decodeFull p h s

/-- The equality of the fused full-consumption decoder against `decodeRepeat`
restricted to full consumption (task 1.3's `decodeRepeatFull_eq`; the same law as
`decodeFull_spec`). Under the full-consumption-uniqueness hypothesis, `decodeRepeatFull
p h s = some xs` iff `(xs, [])` is a result of `decodeRepeat p h s`. -/
theorem decodeRepeatFull_eq {α : Type} (p : Codec α) (h : ConsumesByte p)
    (huniq : ∀ {x y : List α} {s : Bytes},
      (x, []) ∈ decodeRepeat p h s → (y, []) ∈ decodeRepeat p h s → x = y)
    (xs : List α) (s : Bytes) :
    decodeRepeatFull p h s = some xs ↔ (xs, []) ∈ decodeRepeat p h s :=
  decodeFull_spec p h huniq xs s

end Codec
