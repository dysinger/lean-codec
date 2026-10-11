/- Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later -/

import Codec.Decode
import Codec.Encode
import Codec.Sound

/-!
# Derived combinators

Generic, byte-agnostic combinators built from the primitives (paper §6.1):

  * `p *> q`, `p <* q` — pair variants that ignore a side (the paper's `*>`, `<*`)
  * `between open close p` — `open *> p <* close`
  * `optional`/`maybe`/`choice` — zero-or-one and n-ary alternation (§6.2)
  * `count n p` / `manyUpTo n p` — bounded repetition (total, `#eval`-able)

Unbounded repetition (`many`, and its `some`/`sepBy`/`chainl1` derivations) is
**not** a finite `Codec` value: it is an *infinite* description, which this
strict language cannot represent as an AST node. Its semantics lives in three
already-separate places instead:

  * `relRepeat (Rel p)` (`Codec.Codec`) — the total least-fixpoint denotation.
  * `decodeRepeat p h` (`Codec.Decode`) — the productive decoder, well-founded on
    `s.length`, taking `h : ConsumesByte p` as its argument.
  * `encodeRepeat p` (`Codec.Encode`) — the total encoder, structural on the value
    list (no productivity witness needed).

The `many`-shaped *list* combinators (`sepBy`, `chainl1`, …) are re-derived at the
end of this file **over these three**, not over an opaque `many p` value — a
former `partial def many` was irreducibly opaque at the `Rel` level (a `partial
def` produces no equational lemma), making `Rel (many p) ↔ relRepeat (Rel p)`
unprovable.
-/

namespace Codec

open Iso

/-- `p *> q` parses/prints `p` then `q`, keeping only `q` (ignoring `p`'s `()`).
`p * q : Codec (Unit × α)`, mapped by `commute ≫ inverse unit : Iso (Unit × α) α`. -/
def seqRight {α : Type} (p : Codec Unit) (q : Codec α) : Codec α :=
  Codec.iso (Iso.commute ≫ Iso.inverse (Iso.unit)) (Codec.seq p q)

/-- `p <* q` parses/prints `p` then `q`, keeping only `p` (ignoring `q`'s `()`).
`p * q : Codec (α × Unit)`, mapped by `inverse unit : Iso (α × Unit) α`. -/
def seqLeft {α : Type} (p : Codec α) (q : Codec Unit) : Codec α :=
  Codec.iso (Iso.inverse (Iso.unit)) (Codec.seq p q)

/-- `between open close p` is `open *> p <* close`. -/
def between {α : Type} (l r : Codec Unit) (p : Codec α) : Codec α :=
  seqRight l (seqLeft p r)

/-! ## Sum and optional combinators (paper §6.2) -/

/-- `optional p` is zero-or-one `p`, as `Codec (Option α)`: the `some x` case via
`optionSome`, or `none` via `pure none`. -/
def optional {α : Type} [DecidableEq α] (p : Codec α) : Codec (Option α) :=
  Codec.alt (Codec.iso (Iso.optionSome) p) (Codec.pure none)

/-- `maybe p` is an alias for `optional p`. -/
def maybe {α : Type} [DecidableEq α] (p : Codec α) : Codec (Option α) :=
  optional p

/-- `choice ps` is the n-ary alternation of the descriptions in `ps`,
right-associated (`d₁ | (d₂ | …)`), so `Rel (choice (d::ds)) = Rel d ∨ Rel (choice ds)`
holds *definitionally*. -/
def choice {α : Type} : List (Codec α) → Codec α
  | [] => Codec.empty
  | d :: ds => Codec.alt d (choice ds)

/-! ## Bounded repetition (total and evaluable) -/

/-- `count n p` is exactly `n` repetitions of `p` (a list of length `n`), by
structural induction on `n`. Total and `#eval`-able (unlike unbounded `many`,
which is not a finite description at all). -/
def count {α : Type} (n : Nat) (p : Codec α) : Codec (List α) :=
  match n with
  | 0 => Codec.iso (Iso.nil) (Codec.pure ())
  | n + 1 => Codec.iso (Iso.cons) (Codec.seq p (count n p))

/-- `manyUpTo n p` is at most `n` repetitions of `p`, as the choice of exactly
`k` repetitions for `0 ≤ k ≤ n`. Total and `#eval`-able. -/
def manyUpTo {α : Type} (n : Nat) (p : Codec α) : Codec (List α) :=
  choice ((List.range (n + 1)).map (fun k => count k p))

/-! ## Soundness lemmas: the derived combinators are free theorems

Each derived combinator's `Rel` characterization is a *definitional* consequence
of the primitives' `Rel_*` lemmas — no new induction, no gate. These
representative lemmas pin down that claim; the full laws (`decode_spec`, `bidir`,
`roundtrip`) hold unconditionally via `Codec.Sound`. -/

/-- `optional p` relates `Option.some x` iff `p` relates `x` (the `none` case
is `pure none`). -/
theorem Rel_optional_some {α : Type} [DecidableEq α] (p : Codec α) (x : α)
    (s : List UInt8) :
    Rel (optional p) (Option.some x) s ↔ Rel p x s := by
  unfold optional
  rw [Rel_alt]
  constructor
  · intro h
    rcases h with h | h
    · rw [Rel_iso] at h
      rcases h with ⟨a, hsome, hp⟩
      have : a = x := by
        simpa using (Option.some.inj hsome)
      subst a
      exact hp
    · rw [Rel_pure] at h
      rcases h with ⟨hnone, _⟩
      cases hnone
  · intro hp
    left
    rw [Rel_iso]
    exact ⟨x, rfl, hp⟩

/-- `count 0 p` relates only the empty list to the empty bytes. -/
theorem Rel_count_zero {α : Type} (p : Codec α) (xs : List α) (s : List UInt8) :
    Rel (count 0 p) xs s ↔ xs = [] ∧ s = [] := by
  unfold count
  rw [Rel_iso]
  constructor
  · intro h
    rcases h with ⟨u, hnil, hpure⟩
    rw [Rel_pure] at hpure
    rcases hpure with ⟨_, hs⟩
    have : u = () := by cases u; rfl
    subst u
    rw [Iso.nil] at hnil
    -- hnil : Iso.nil.apply () = some xs, i.e. some [] = some xs
    have : xs = [] := by simpa using hnil.symm
    exact ⟨this, hs⟩
  · intro h
    rcases h with ⟨hxs, hs⟩
    subst xs; subst s
    exact ⟨(), rfl, by simp [Rel_pure]⟩

/-- `choice ps` relates iff some description in `ps` relates. -/
theorem Rel_choice {α : Type} (ps : List (Codec α)) (x : α) (s : List UInt8) :
    Rel (choice ps) x s ↔ ∃ d ∈ ps, Rel d x s := by
  induction ps generalizing x s with
  | nil =>
      constructor
      · intro h
        exact False.elim h
      · intro h
        rcases h with ⟨_, hmem, _⟩
        simp at hmem
  | cons d ds ih =>
      rw [choice, Rel_alt]
      rw [ih]
      constructor
      · intro h
        rcases h with h | h
        · exact ⟨d, by simp, h⟩
        · rcases h with ⟨d', hmem, hd'⟩
          exact ⟨d', by simp [hmem], hd'⟩
      · intro h
        rcases h with ⟨d', hmem, hd'⟩
        rw [List.mem_cons] at hmem
        rcases hmem with hmem | hmem
        · subst d'
          exact Or.inl hd'
        · exact Or.inr ⟨d', hmem, hd'⟩

/-! ## Unbounded repetition: the list combinators re-derived over `relRepeat`

`many p` is `relRepeat (Rel p)` (denotation), `decodeRepeat p h` (decoder),
`encodeRepeat p` (encoder). Its list-shaped derivations are defined the same way
— as a relation, a decoder, and an encoder — rather than as a `Codec` value that
would embed the absent `many` node. See the module docstring for why.
-/

/-- The denotation of `sepBy p sep`, specialized to **non-empty** separated lists:
`p` (the head `x₀`), then arbitrarily many `sep *> p` (the tail, folded by
`relRepeat`). The empty list is **not** a `sepBy` value (the `[]` case is `False`,
and `encodeSepBy [] = none`), so this combinator is semantically the paper's
`sepBy1` (one-or-more), *not* `sepBy` (zero-or-more); zero-or-more separation is
`optional (sepBy p sep)`. This is the `many`-case denotation statement,
specialized to a non-empty head. -/
def relSepBy {α : Type} (p : Codec α) (sep : Codec Unit) :
    List α → List UInt8 → Prop
  | x₀ :: rest, s => ∃ s₀ s', s = s₀ ++ s' ∧ Rel p x₀ s₀ ∧ relRepeat (Rel (seqRight sep p)) rest s'
  | [], _ => False

/-- `decodeRepeat` specialized to the `sepBy` tail step: enumerate the results of
`p` then arbitrarily many `(sep *> p)`, threading the remainder. The empty list is
not produced (separation is one-or-more). Total for a productive `sep`
(`hsep : ConsumesByte (seqRight sep p)`). -/
def decodeSepBy {α : Type} (p : Codec α) (sep : Codec Unit)
    (hsep : ConsumesByte (seqRight sep p)) (s : List UInt8) :
    List (List α × List UInt8) :=
  (decode p s).flatMap fun (x₀, t) =>
    (decodeRepeat (seqRight sep p) hsep t).map fun (rest, r) => (x₀ :: rest, r)

/-- The total encoder for `sepBy p sep`: encode the head with `p` and the tail
with `encodeRepeat (seqRight sep p)`. -/
def encodeSepBy {α : Type} (p : Codec α) (sep : Codec Unit) :
    List α → Option (List UInt8)
  | x₀ :: rest =>
      match encode p x₀ with
      | none => none
      | some s₀ =>
          match encodeRepeat (seqRight sep p) rest with
          | none => none
          | some s' => some (s₀ ++ s')
  | [] => none

/-! ## Left- and right-associative chains on a fold

`chainl1`/`chainr1` parse/print a non-empty, left- or right-associative chain of
`arg` separated by `op`. The paper (§5.3/§6.1) builds them as `foldl`/`foldr`
over an operand list; here that operand list is unbounded repetition, so the
combinators are re-derived over `decodeRepeat`/`encodeRepeat` rather than over a
`Codec` that embeds `many`. The folds themselves (`Iso.foldl`/`Iso.foldr`) are
unchanged.
-/

/-- The denotation of a left-associative chain: a seed `a₀` from `arg`, an operand
list `ops` from the shifted step `seq op arg`, folded by `Iso.foldl f`. -/
def relChainl1 {α β : Type} (f : Iso (α × (β × α)) α) (measure : α → Nat)
    (h : MeasureDecreases measure f) (arg : Codec α) (op : Codec β) :
    α → List UInt8 → Prop :=
  fun a s => ∃ a₀ ops s₀ s', s = s₀ ++ s' ∧ Rel arg a₀ s₀ ∧
    relRepeat (Rel (Codec.seq op arg)) ops s' ∧ (foldl f measure h).apply (a₀, ops) = some a

/-- The denotation of a right-associative chain: a seed `a₀` from `arg`, an operand
list `ops` from the shifted step `seq arg op`, folded by `Iso.foldr f`. -/
def relChainr1 {α β : Type} (f : Iso ((α × β) × α) α) (measure : α → Nat)
    (h : MeasureDecreasesR measure f) (arg : Codec α) (op : Codec β) :
    α → List UInt8 → Prop :=
  fun a s => ∃ a₀ ops s₀ s', s = s₀ ++ s' ∧ Rel arg a₀ s₀ ∧
    relRepeat (Rel (Codec.seq arg op)) ops s' ∧ (foldr f measure h).apply (a₀, ops) = some a

/-- The decoder for a left-associative chain: decode the seed `arg`, decode the
operand list via `decodeRepeat`, then fold. Total for a productive `op`-step
(`hsep : ConsumesByte (seq op arg)`). -/
def decodeChainl1 {α β : Type} (f : Iso (α × (β × α)) α) (measure : α → Nat)
    (h : MeasureDecreases measure f) (arg : Codec α) (op : Codec β)
    (hsep : ConsumesByte (Codec.seq op arg)) (s : List UInt8) :
    List (α × List UInt8) :=
  (decode arg s).flatMap fun (a₀, t) =>
    (decodeRepeat (Codec.seq op arg) hsep t).filterMap fun (ops, r) =>
      ((foldl f measure h).apply (a₀, ops)).map fun a => (a, r)

/-- The decoder for a right-associative chain. -/
def decodeChainr1 {α β : Type} (f : Iso ((α × β) × α) α) (measure : α → Nat)
    (h : MeasureDecreasesR measure f) (arg : Codec α) (op : Codec β)
    (hsep : ConsumesByte (Codec.seq arg op)) (s : List UInt8) :
    List (α × List UInt8) :=
  (decode arg s).flatMap fun (a₀, t) =>
    (decodeRepeat (Codec.seq arg op) hsep t).filterMap fun (ops, r) =>
      ((foldr f measure h).apply (a₀, ops)).map fun a => (a, r)

/-- The encoder for a left-associative chain: maximally unfold `a` via `foldl`,
then encode the seed and the operand list. -/
def encodeChainl1 {α β : Type} (f : Iso (α × (β × α)) α)
    (measure : α → Nat) (h : MeasureDecreases measure f) (arg : Codec α)
    (op : Codec β) (a : α) : Option (List UInt8) :=
  match (foldl f measure h).unapply a with
  | none => none
  | some (a₀, ops) =>
      match encode arg a₀ with
      | none => none
      | some s₀ =>
          match encodeRepeat (Codec.seq op arg) ops with
          | none => none
          | some s' => some (s₀ ++ s')

/-- The encoder for a right-associative chain. -/
def encodeChainr1 {α β : Type} (f : Iso ((α × β) × α) α)
    (measure : α → Nat) (h : MeasureDecreasesR measure f) (arg : Codec α)
    (op : Codec β) (a : α) : Option (List UInt8) :=
  match (foldr f measure h).unapply a with
  | none => none
  | some (a₀, ops) =>
      match encode arg a₀ with
      | none => none
      | some s₀ =>
          match encodeRepeat (Codec.seq arg op) ops with
          | none => none
          | some s' => some (s₀ ++ s')

/-! ## Soundness of the `many`-derived list combinators

The re-derived combinators satisfy the same shape of laws as the primitives
(`decode_spec`/`encode_rel` in `Codec.Sound`): the decoder is complete and sound
against the relation, and the encoder only prints in-relation values. Productivity
appears only as the decoder's `hsep` argument, never as a gate on the laws.
-/

/-- The bidirectional law for `sepBy`: `decodeSepBy` yields `xs` with remainder `r`
iff the input splits as a `relSepBy`-prefix plus `r`. Unconditional; productivity
is carried only as `hsep`. -/
theorem decodeSepBy_spec {α : Type} (p : Codec α) (sep : Codec Unit)
    (hsep : ConsumesByte (seqRight sep p)) :
    ∀ (xs : List α) {s r : List UInt8},
      (xs, r) ∈ decodeSepBy p sep hsep s ↔
        ∃ s₀, s = s₀ ++ r ∧ relSepBy p sep xs s₀ := by
  intro xs s r
  rw [decodeSepBy, List.mem_flatMap]
  cases xs with
  | nil =>
      constructor
      · intro h
        rcases h with ⟨a, _ha, hm⟩
        rcases a with ⟨x₀, t⟩
        rw [List.mem_map] at hm
        rcases hm with ⟨pr, _hpr, heq⟩
        rcases pr with ⟨_rest, _r'⟩
        cases heq
      · intro h
        rcases h with ⟨_s₀, _hs, hrel⟩
        simp [relSepBy] at hrel
  | cons x₀ rest =>
      constructor
      · intro h
        rcases h with ⟨a, ha, hm⟩
        rcases a with ⟨ax, t⟩
        rw [List.mem_map] at hm
        rcases hm with ⟨pr, hpr, heq⟩
        rcases pr with ⟨rest', r'⟩
        have hcons : ax :: rest' = x₀ :: rest := congrArg Prod.fst heq
        have hr : r' = r := congrArg Prod.snd heq
        cases hcons
        cases hr
        rcases (decode_spec p x₀).1 ha with ⟨s₁, hs₁, hrel₁⟩
        rcases (decodeRepeat_spec (seqRight sep p) hsep rest t r).1 hpr with ⟨s₂, hs₂, hrel₂⟩
        refine ⟨s₁ ++ s₂, ?_, ?_⟩
        · rw [hs₁, hs₂]
          simp [List.append_assoc]
        · rw [relSepBy]
          exact ⟨s₁, s₂, rfl, hrel₁, hrel₂⟩
      · intro h
        rcases h with ⟨s₀, hs, hrel⟩
        rw [relSepBy] at hrel
        rcases hrel with ⟨s₁, s₂, hs₀, hrel₁, hrel₂⟩
        have hx : (x₀, s₂ ++ r) ∈ decode p s := by
          refine (decode_spec p x₀).2 ⟨s₁, ?_, hrel₁⟩
          rw [hs, hs₀]
          simp [List.append_assoc]
        refine ⟨(x₀, s₂ ++ r), hx, ?_⟩
        rw [List.mem_map]
        refine ⟨(rest, r), ?_, rfl⟩
        exact (decodeRepeat_spec (seqRight sep p) hsep rest (s₂ ++ r) r).2 ⟨s₂, rfl, hrel₂⟩

/-- Encoder soundness for `sepBy`: any list the `sepBy`-encoder prints is in
`relSepBy`. Structural on the value list; no productivity witness needed. -/
theorem encodeSepBy_rel {α : Type} (p : Codec α) (sep : Codec Unit) :
    ∀ (xs : List α) {s : List UInt8}, encodeSepBy p sep xs = some s → relSepBy p sep xs s := by
  intro xs
  cases xs with
  | nil =>
      intro s he
      simp [encodeSepBy] at he
  | cons x₀ rest =>
      intro s he
      rw [encodeSepBy] at he
      cases hx : encode p x₀ with
      | none => simp [hx] at he
      | some s₀ =>
          rw [hx] at he
          cases hr : encodeRepeat (seqRight sep p) rest with
          | none => simp [hr] at he
          | some s' =>
              rw [hr] at he
              cases he
              rw [relSepBy]
              exact ⟨s₀, s', rfl, encode_rel p x₀ hx, encodeRepeat_rel (seqRight sep p) rest hr⟩

/-- The bidirectional law for `chainl1`: the chain decoder is complete and sound
against `relChainl1`. Unconditional; productivity is the decoder's `hsep` argument.
The fold step `foldl` (and its `MeasureDecreases` witness `h`) is unchanged. -/
theorem decodeChainl1_spec {α β : Type} (f : Iso (α × (β × α)) α) (measure : α → Nat)
    (h : MeasureDecreases measure f) (arg : Codec α) (op : Codec β)
    (hsep : ConsumesByte (Codec.seq op arg)) :
    ∀ (a : α) {s r : List UInt8}, (a, r) ∈ decodeChainl1 f measure h arg op hsep s ↔
      ∃ s₀, s = s₀ ++ r ∧ relChainl1 f measure h arg op a s₀ := by
  intro a s r
  rw [decodeChainl1, List.mem_flatMap]
  constructor
  · intro hm
    rcases hm with ⟨pr, hpr, hm'⟩
    rcases pr with ⟨a₀, t⟩
    rw [List.mem_filterMap] at hm'
    rcases hm' with ⟨opsr, hopsr, hf⟩
    rcases opsr with ⟨ops, r'⟩
    cases haply : (foldl f measure h).apply (a₀, ops) with
    | none => simp [haply] at hf
    | some a' =>
        simp [haply] at hf
        rcases hf with ⟨ha', hr'⟩
        cases ha'
        cases hr'
        rcases (decode_spec arg a₀).1 hpr with ⟨s₁, hs₁, hrel₁⟩
        rcases (decodeRepeat_spec (Codec.seq op arg) hsep ops t r).1 hopsr with ⟨s₂, hs₂, hrel₂⟩
        refine ⟨s₁ ++ s₂, ?_, ?_⟩
        · rw [hs₁, hs₂]
          simp [List.append_assoc]
        · rw [relChainl1]
          exact ⟨a₀, ops, s₁, s₂, rfl, hrel₁, hrel₂, haply⟩
  · intro hm
    rcases hm with ⟨s₀, hs, hrel⟩
    rw [relChainl1] at hrel
    rcases hrel with ⟨a₀, ops, s₁, s₂, hs₀, hrel₁, hrel₂, haply⟩
    have ha : (a₀, s₂ ++ r) ∈ decode arg s := by
      refine (decode_spec arg a₀).2 ⟨s₁, ?_, hrel₁⟩
      rw [hs, hs₀]
      simp [List.append_assoc]
    refine ⟨(a₀, s₂ ++ r), ha, ?_⟩
    rw [List.mem_filterMap]
    refine ⟨(ops, r), ?_, ?_⟩
    · exact (decodeRepeat_spec (Codec.seq op arg) hsep ops (s₂ ++ r) r).2 ⟨s₂, rfl, hrel₂⟩
    · simp [haply]

/-- Encoder soundness for `chainl1`: any value the chain-encoder prints is in
`relChainl1`. The `foldl.unapply` direction is tied to `foldl.apply` by the
`Iso.law` field of `foldl`, so the maximally-unfolded seed/operands re-fold to the
original value. -/
theorem encodeChainl1_rel {α β : Type} (f : Iso (α × (β × α)) α) (measure : α → Nat)
    (h : MeasureDecreases measure f) (arg : Codec α) (op : Codec β) :
    ∀ (a : α) {s : List UInt8}, encodeChainl1 f measure h arg op a = some s →
      relChainl1 f measure h arg op a s := by
  intro a s he
  rw [encodeChainl1] at he
  cases hu : (foldl f measure h).unapply a with
  | none => simp [hu] at he
  | some va =>
      rcases va with ⟨a₀, ops⟩
      simp [hu] at he
      cases ha : encode arg a₀ with
      | none => simp [ha] at he
      | some s₀ =>
          simp [ha] at he
          cases hr : encodeRepeat (Codec.seq op arg) ops with
          | none => simp [hr] at he
          | some s' =>
              simp [hr] at he
              cases he
              have haply : (foldl f measure h).apply (a₀, ops) = some a :=
                ((foldl f measure h).law (a₀, ops) a).2 hu
              rw [relChainl1]
              exact ⟨a₀, ops, s₀, s', rfl, encode_rel arg a₀ ha,
                encodeRepeat_rel (Codec.seq op arg) ops hr, haply⟩

/-- The bidirectional law for `chainr1` (the right-fold dual of `decodeChainl1_spec`). -/
theorem decodeChainr1_spec {α β : Type} (f : Iso ((α × β) × α) α) (measure : α → Nat)
    (h : MeasureDecreasesR measure f) (arg : Codec α) (op : Codec β)
    (hsep : ConsumesByte (Codec.seq arg op)) :
    ∀ (a : α) {s r : List UInt8}, (a, r) ∈ decodeChainr1 f measure h arg op hsep s ↔
      ∃ s₀, s = s₀ ++ r ∧ relChainr1 f measure h arg op a s₀ := by
  intro a s r
  rw [decodeChainr1, List.mem_flatMap]
  constructor
  · intro hm
    rcases hm with ⟨pr, hpr, hm'⟩
    rcases pr with ⟨a₀, t⟩
    rw [List.mem_filterMap] at hm'
    rcases hm' with ⟨opsr, hopsr, hf⟩
    rcases opsr with ⟨ops, r'⟩
    cases haply : (foldr f measure h).apply (a₀, ops) with
    | none => simp [haply] at hf
    | some a' =>
        simp [haply] at hf
        rcases hf with ⟨ha', hr'⟩
        cases ha'
        cases hr'
        rcases (decode_spec arg a₀).1 hpr with ⟨s₁, hs₁, hrel₁⟩
        rcases (decodeRepeat_spec (Codec.seq arg op) hsep ops t r).1 hopsr with ⟨s₂, hs₂, hrel₂⟩
        refine ⟨s₁ ++ s₂, ?_, ?_⟩
        · rw [hs₁, hs₂]
          simp [List.append_assoc]
        · rw [relChainr1]
          exact ⟨a₀, ops, s₁, s₂, rfl, hrel₁, hrel₂, haply⟩
  · intro hm
    rcases hm with ⟨s₀, hs, hrel⟩
    rw [relChainr1] at hrel
    rcases hrel with ⟨a₀, ops, s₁, s₂, hs₀, hrel₁, hrel₂, haply⟩
    have ha : (a₀, s₂ ++ r) ∈ decode arg s := by
      refine (decode_spec arg a₀).2 ⟨s₁, ?_, hrel₁⟩
      rw [hs, hs₀]
      simp [List.append_assoc]
    refine ⟨(a₀, s₂ ++ r), ha, ?_⟩
    rw [List.mem_filterMap]
    refine ⟨(ops, r), ?_, ?_⟩
    · exact (decodeRepeat_spec (Codec.seq arg op) hsep ops (s₂ ++ r) r).2 ⟨s₂, rfl, hrel₂⟩
    · simp [haply]

/-- Encoder soundness for `chainr1` (the right-fold dual of `encodeChainl1_rel`). -/
theorem encodeChainr1_rel {α β : Type} (f : Iso ((α × β) × α) α) (measure : α → Nat)
    (h : MeasureDecreasesR measure f) (arg : Codec α) (op : Codec β) :
    ∀ (a : α) {s : List UInt8}, encodeChainr1 f measure h arg op a = some s →
      relChainr1 f measure h arg op a s := by
  intro a s he
  rw [encodeChainr1] at he
  cases hu : (foldr f measure h).unapply a with
  | none => simp [hu] at he
  | some va =>
      rcases va with ⟨a₀, ops⟩
      simp [hu] at he
      cases ha : encode arg a₀ with
      | none => simp [ha] at he
      | some s₀ =>
          simp [ha] at he
          cases hr : encodeRepeat (Codec.seq arg op) ops with
          | none => simp [hr] at he
          | some s' =>
              simp [hr] at he
              cases he
              have haply : (foldr f measure h).apply (a₀, ops) = some a :=
                ((foldr f measure h).law (a₀, ops) a).2 hu
              rw [relChainr1]
              exact ⟨a₀, ops, s₀, s', rfl, encode_rel arg a₀ ha,
                encodeRepeat_rel (Codec.seq arg op) ops hr, haply⟩

end Codec
