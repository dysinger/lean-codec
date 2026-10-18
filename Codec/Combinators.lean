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

Unbounded repetition (`many`, and its `sepBy`/`chainl1` derivations — realized here
as the `relSepBy`/`decodeSepBy`/`encodeSepBy` and `relChain*`/`decodeChain*`/
`encodeChain*` triples, there being **no** bare `sepBy`/`chainl1`/`some`/`many1`
symbol) is **not** a finite `Codec` value: it is an *infinite* description, which
this strict language cannot represent as an AST node. Its semantics lives in
three already-separate places instead:

  * `relRepeat (Rel p)` (`Codec.Codec`) — the total least-fixpoint denotation.
  * `decodeRepeat p h` (`Codec.Decode`) — the productive decoder, well-founded on
    `n`, taking `h : ConsumesByte p` as its argument.
  * `encodeRepeat p` (`Codec.Encode`) — the total encoder, structural on the value
    list (no productivity witness needed).

The `many`-shaped *list* combinators (`sepBy`, `chainl1`; see the explicit symbol
names above) are re-derived at the end of this file **over these three**, not over
an opaque `many p` value — a former `partial def many` was irreducibly opaque at
the `Rel` level (a `partial def` produces no equational lemma), making
`Rel (many p) ↔ relRepeat (Rel p)` unprovable.
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
    {n : Nat} (s : Bytes n) :
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
theorem Rel_count_zero {α : Type} (p : Codec α) (xs : List α) {n : Nat} (s : Bytes n) :
    Rel (count 0 p) xs s ↔ xs = [] ∧ n = 0 := by
  unfold count
  rw [Rel_iso]
  constructor
  · intro h
    rcases h with ⟨u, hnil, hpure⟩
    rw [Rel_pure] at hpure
    rcases hpure with ⟨_, hn⟩
    have : u = () := by cases u; rfl
    subst u
    rw [Iso.nil] at hnil
    have : xs = [] := by simpa using hnil.symm
    exact ⟨this, hn⟩
  · intro h
    rcases h with ⟨hxs, hn⟩
    subst xs
    subst n
    exact ⟨(), rfl, (Rel_pure () () (s := s)).2 ⟨rfl, rfl⟩⟩

/-- `choice ps` relates iff some description in `ps` relates. -/
theorem Rel_choice {α : Type} (ps : List (Codec α)) (x : α) {n : Nat} (s : Bytes n) :
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
    List α → {n : Nat} → Bytes n → Prop
  | x₀ :: rest, n, s => ∃ (m : Nat) (hm : m ≤ n) (s₁ : Bytes m) (s₂ : Bytes (n - m)),
      s = splice hm s₁ s₂ ∧ Rel p x₀ s₁ ∧ relRepeat (Rel (seqRight sep p)) rest (n - m) s₂
  | [], _, _ => False

/-- `decodeRepeat` specialized to the `sepBy` tail step: enumerate the results of
`p` then arbitrarily many `(sep *> p)`, threading the remainder. The empty list is
not produced (separation is one-or-more). Total for a productive `sep`
(`hsep : ConsumesByte (seqRight sep p)`). -/
def decodeSepBy {α : Type} (p : Codec α) (sep : Codec Unit)
    (hsep : ConsumesByte (seqRight sep p)) {n : Nat} (s : Bytes n) :
    List (List α × Suffix n) :=
  (decode p s).flatMap fun (x₀, t) =>
    (decodeRepeat (seqRight sep p) hsep t.remaining t.bytes).map fun (rest, r) => (x₀ :: rest, Suffix.trans t r)

/-- The total encoder for `sepBy p sep`: encode the head with `p` and the tail
with `encodeRepeat (seqRight sep p)`. -/
def encodeSepBy {α : Type} (p : Codec α) (sep : Codec Unit) :
    List α → Option (Sigma fun n => Bytes n)
  | x₀ :: rest =>
      match encode p x₀ with
      | none => none
      | some s₀ =>
          match encodeRepeat (seqRight sep p) rest with
          | none => none
          | some s' => some ⟨s₀.1 + s'.1, concat s₀.2 s'.2⟩
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
    α → {n : Nat} → Bytes n → Prop :=
  fun a {n : Nat} s => ∃ (a₀ : α) (ops : List (β × α)) (m : Nat) (hm : m ≤ n) (s₁ : Bytes m) (s₂ : Bytes (n - m)),
    s = splice hm s₁ s₂ ∧ Rel arg a₀ s₁ ∧
    relRepeat (Rel (Codec.seq op arg)) ops (n - m) s₂ ∧ (foldl f measure h).apply (a₀, ops) = some a

/-- The denotation of a right-associative chain: a seed `a₀` from `arg`, an operand
list `ops` from the shifted step `seq arg op`, folded by `Iso.foldr f`. -/
def relChainr1 {α β : Type} (f : Iso ((α × β) × α) α) (measure : α → Nat)
    (h : MeasureDecreasesR measure f) (arg : Codec α) (op : Codec β) :
    α → {n : Nat} → Bytes n → Prop :=
  fun a {n : Nat} s => ∃ (a₀ : α) (ops : List (α × β)) (m : Nat) (hm : m ≤ n) (s₁ : Bytes m) (s₂ : Bytes (n - m)),
    s = splice hm s₁ s₂ ∧ Rel arg a₀ s₁ ∧
    relRepeat (Rel (Codec.seq arg op)) ops (n - m) s₂ ∧ (foldr f measure h).apply (a₀, ops) = some a

/-- The decoder for a left-associative chain: decode the seed `arg`, decode the
operand list via `decodeRepeat`, then fold. Total for a productive `op`-step
(`hsep : ConsumesByte (seq op arg)`). -/
def decodeChainl1 {α β : Type} (f : Iso (α × (β × α)) α) (measure : α → Nat)
    (h : MeasureDecreases measure f) (arg : Codec α) (op : Codec β)
    (hsep : ConsumesByte (Codec.seq op arg)) {n : Nat} (s : Bytes n) :
    List (α × Suffix n) :=
  (decode arg s).flatMap fun (a₀, t) =>
    (decodeRepeat (Codec.seq op arg) hsep t.remaining t.bytes).filterMap fun (ops, r) =>
      ((foldl f measure h).apply (a₀, ops)).map fun a => (a, Suffix.trans t r)

/-- The decoder for a right-associative chain. -/
def decodeChainr1 {α β : Type} (f : Iso ((α × β) × α) α) (measure : α → Nat)
    (h : MeasureDecreasesR measure f) (arg : Codec α) (op : Codec β)
    (hsep : ConsumesByte (Codec.seq arg op)) {n : Nat} (s : Bytes n) :
    List (α × Suffix n) :=
  (decode arg s).flatMap fun (a₀, t) =>
    (decodeRepeat (Codec.seq arg op) hsep t.remaining t.bytes).filterMap fun (ops, r) =>
      ((foldr f measure h).apply (a₀, ops)).map fun a => (a, Suffix.trans t r)

/-- The encoder for a left-associative chain: maximally unfold `a` via `foldl`,
then encode the seed and the operand list. -/
def encodeChainl1 {α β : Type} (f : Iso (α × (β × α)) α)
    (measure : α → Nat) (h : MeasureDecreases measure f) (arg : Codec α)
    (op : Codec β) (a : α) : Option (Sigma fun n => Bytes n) :=
  match (foldl f measure h).unapply a with
  | none => none
  | some (a₀, ops) =>
      match encode arg a₀ with
      | none => none
      | some s₀ =>
          match encodeRepeat (Codec.seq op arg) ops with
          | none => none
          | some s' => some ⟨s₀.1 + s'.1, concat s₀.2 s'.2⟩

/-- The encoder for a right-associative chain. -/
def encodeChainr1 {α β : Type} (f : Iso ((α × β) × α) α)
    (measure : α → Nat) (h : MeasureDecreasesR measure f) (arg : Codec α)
    (op : Codec β) (a : α) : Option (Sigma fun n => Bytes n) :=
  match (foldr f measure h).unapply a with
  | none => none
  | some (a₀, ops) =>
      match encode arg a₀ with
      | none => none
      | some s₀ =>
          match encodeRepeat (Codec.seq arg op) ops with
          | none => none
          | some s' => some ⟨s₀.1 + s'.1, concat s₀.2 s'.2⟩

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
    ∀ (xs : List α) {n : Nat} (s : Bytes n) (r : Suffix n),
      (xs, r) ∈ decodeSepBy p sep hsep s ↔
        ∃ s₀ : Bytes (n - r.remaining), s = r.prepend s₀ ∧ relSepBy p sep xs s₀ := by
  intro xs n s r
  rw [decodeSepBy, List.mem_flatMap]
  cases xs with
  | nil =>
      constructor
      · intro h
        rcases h with ⟨ab, _hab, hm⟩
        rcases ab with ⟨x₀, t⟩
        rw [List.mem_map] at hm
        rcases hm with ⟨pr, _hpr, heq⟩
        rcases pr with ⟨rest, r'⟩
        cases heq
      · intro h
        rcases h with ⟨s₀, _hs, hrel⟩
        simp [relSepBy] at hrel
  | cons x₀ rest =>
      constructor
      · intro h
        rcases h with ⟨ab, hab, hm⟩
        rcases ab with ⟨ax, t⟩
        rw [List.mem_map] at hm
        rcases hm with ⟨pr, hpr, heq⟩
        rcases pr with ⟨rest', r'⟩
        have hcons : ax :: rest' = x₀ :: rest := congrArg Prod.fst heq
        have hr : Suffix.trans t r' = r := congrArg Prod.snd heq
        cases hcons
        subst r
        rcases (decode_spec p x₀ (s := s) (r := t)).1 hab with ⟨s₁, hs₁, hrel₁⟩
        rcases (decodeRepeat_spec (seqRight sep p) hsep rest t.remaining t.bytes r').1 hpr with ⟨s₂, hs₂, hrel₂⟩
        refine ⟨cast (congrArg Bytes (sub_sub_add n t.remaining r'.remaining t.hle r'.hle)) (concat s₁ s₂), ?_, ?_⟩
        · rw [hs₁]
          exact (prepend_assoc t r' s₁ s₂ hs₂.symm).symm
        · rw [relSepBy]
          refine ⟨n - t.remaining, Nat.sub_le_sub_left r'.hle n, s₁, cast (congrArg Bytes (sub_sub_sub n t.remaining r'.remaining t.hle r'.hle).symm) s₂, ?_, hrel₁, ?_⟩
          · exact cast_concat_splice_sub t.hle r'.hle s₁ s₂
          · exact (relRepeat_cast (Rel (seqRight sep p)) rest (sub_sub_sub n t.remaining r'.remaining t.hle r'.hle).symm s₂).2 hrel₂
      · intro h
        rcases h with ⟨s₀, hs, hrel⟩
        rw [relSepBy] at hrel
        rcases hrel with ⟨m, hm, s₁, s₂, hs₀, hrel₁, hrel₂⟩
        subst s₀
        have hmem₁ : (x₀, Suffix.drop m s) ∈ decode p s := by
          refine (decode_spec p x₀ (s := s) (r := Suffix.drop m s)).2 ⟨
            cast (congrArg Bytes (Nat.sub_sub_self (Nat.le_trans hm (Nat.sub_le n r.remaining))).symm) s₁,
            ?_, ?_⟩
          · rw [hs]
            exact prepend_drop_of_prepend_splice r m hm s₁ s₂
          · exact (Rel_cast p x₀ (Nat.sub_sub_self (Nat.le_trans hm (Nat.sub_le n r.remaining))).symm s₁).2 hrel₁
        let r' : Suffix (n - m) := Suffix.drop ((n - r.remaining) - m) (bdrop m s)
        have hmem₂ : (rest, r') ∈ decodeRepeat (seqRight sep p) hsep (n - m) (bdrop m s) := by
          refine (decodeRepeat_spec (seqRight sep p) hsep rest (n - m) (bdrop m s) r').2 ⟨
            cast (congrArg Bytes (Nat.sub_sub_self (Nat.sub_le_sub_right (Nat.sub_le n r.remaining) m)).symm) s₂,
            ?_, ?_⟩
          · dsimp [r']
            rw [hs]
            exact prepend_eq_of_eq_splice (bdrop m (r.prepend (splice hm s₁ s₂))) (Nat.sub_le_sub_right (Nat.sub_le n r.remaining) m) s₂ (cast (congrArg Bytes (bdrop_prepend_splice_snd_len r.hle hm).symm) r.bytes) (bdrop_prepend_splice_eq_splice r m hm s₁ s₂)
          · exact (relRepeat_cast (Rel (seqRight sep p)) rest (Nat.sub_sub_self (Nat.sub_le_sub_right (Nat.sub_le n r.remaining) m)).symm s₂).2 hrel₂
        have htrans : (Suffix.drop m s).trans r' = r := by
          refine Suffix.ext (t₁ := (Suffix.drop m s).trans r') (t₂ := r) ?_ ?_
          · dsimp [r', Suffix.trans]
            exact bdrop_prepend_splice_snd_len r.hle hm
          · dsimp [r', Suffix.trans, Suffix.drop]
            rw [hs]
            rw [bdrop_drop_eq_bytes r m hm s₁ s₂]
            change cast (congrArg Bytes (bdrop_prepend_splice_snd_len r.hle hm)) (cast (congrArg Bytes (bdrop_prepend_splice_snd_len r.hle hm).symm) r.bytes) = r.bytes
            simp
        refine ⟨(x₀, Suffix.drop m s), hmem₁, ?_⟩
        rw [List.mem_map]
        refine ⟨(rest, r'), hmem₂, ?_⟩
        exact congrArg (fun y => (x₀ :: rest, y)) htrans

/-- Encoder soundness for `sepBy`: any list the `sepBy`-encoder prints is in
`relSepBy`. Structural on the value list; no productivity witness needed. -/
theorem encodeSepBy_rel {α : Type} (p : Codec α) (sep : Codec Unit) :
    ∀ (xs : List α) {n : Nat} {s : Bytes n}, encodeSepBy p sep xs = some ⟨n, s⟩ → relSepBy p sep xs s := by
  intro xs n s he
  cases xs with
  | nil =>
      simp [encodeSepBy] at he
  | cons x₀ rest =>
      rw [encodeSepBy] at he
      cases hx : encode p x₀ with
      | none => simp [hx] at he
      | some s₀ =>
          rw [hx] at he
          cases hr : encodeRepeat (seqRight sep p) rest with
          | none => simp [hr] at he
          | some s' =>
              rw [hr] at he
              have heq : (⟨s₀.1 + s'.1, concat s₀.2 s'.2⟩ : Sigma fun k => Bytes k) = ⟨n, s⟩ := by
                simpa using he
              cases heq
              rw [relSepBy]
              refine ⟨s₀.1, Nat.le.intro rfl, s₀.2, cast (congrArg Bytes (Nat.add_sub_cancel_left s₀.1 s'.1).symm) s'.2, ?_, encode_rel p x₀ hx, ?_⟩
              · exact concat_eq_splice s₀.2 s'.2
              · exact (relRepeat_cast (Rel (seqRight sep p)) rest (Nat.add_sub_cancel_left s₀.1 s'.1).symm s'.2).2 (encodeRepeat_rel (seqRight sep p) rest hr)

/-- The bidirectional law for `chainl1`: the chain decoder is complete and sound
against `relChainl1`. Unconditional; productivity is the decoder's `hsep` argument.
The fold step `foldl` (and its `MeasureDecreases` witness `h`) is unchanged. -/
theorem decodeChainl1_spec {α β : Type} (f : Iso (α × (β × α)) α) (measure : α → Nat)
    (h : MeasureDecreases measure f) (arg : Codec α) (op : Codec β)
    (hsep : ConsumesByte (Codec.seq op arg)) :
    ∀ (a : α) {n : Nat} (s : Bytes n) (r : Suffix n), (a, r) ∈ decodeChainl1 f measure h arg op hsep s ↔
      ∃ s₀ : Bytes (n - r.remaining), s = r.prepend s₀ ∧ relChainl1 f measure h arg op a s₀ := by
  intro a n s r
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
        subst r
        rcases (decode_spec arg a₀ (s := s) (r := t)).1 hpr with ⟨s₁, hs₁, hrel₁⟩
        rcases (decodeRepeat_spec (Codec.seq op arg) hsep ops t.remaining t.bytes r').1 hopsr with ⟨s₂, hs₂, hrel₂⟩
        refine ⟨cast (congrArg Bytes (sub_sub_add n t.remaining r'.remaining t.hle r'.hle)) (concat s₁ s₂), ?_, ?_⟩
        · rw [hs₁]
          exact (prepend_assoc t r' s₁ s₂ hs₂.symm).symm
        · rw [relChainl1]
          refine ⟨a₀, ops, n - t.remaining, Nat.sub_le_sub_left r'.hle n, s₁, cast (congrArg Bytes (sub_sub_sub n t.remaining r'.remaining t.hle r'.hle).symm) s₂, ?_, hrel₁, ?_, haply⟩
          · exact cast_concat_splice_sub t.hle r'.hle s₁ s₂
          · exact (relRepeat_cast (Rel (Codec.seq op arg)) ops (sub_sub_sub n t.remaining r'.remaining t.hle r'.hle).symm s₂).2 hrel₂
  · intro hm
    rcases hm with ⟨s₀, hs, hrel⟩
    rw [relChainl1] at hrel
    rcases hrel with ⟨a₀, ops, m, hm₀, s₁, s₂, hs₀, hrel₁, hrel₂, haply⟩
    subst s₀
    have hmem₁ : (a₀, Suffix.drop m s) ∈ decode arg s := by
      refine (decode_spec arg a₀ (s := s) (r := Suffix.drop m s)).2 ⟨
        cast (congrArg Bytes (Nat.sub_sub_self (Nat.le_trans hm₀ (Nat.sub_le n r.remaining))).symm) s₁,
        ?_, ?_⟩
      · rw [hs]
        exact prepend_drop_of_prepend_splice r m hm₀ s₁ s₂
      · exact (Rel_cast arg a₀ (Nat.sub_sub_self (Nat.le_trans hm₀ (Nat.sub_le n r.remaining))).symm s₁).2 hrel₁
    let r' : Suffix (n - m) := Suffix.drop ((n - r.remaining) - m) (bdrop m s)
    have hmem₂ : (ops, r') ∈ decodeRepeat (Codec.seq op arg) hsep (n - m) (bdrop m s) := by
      refine (decodeRepeat_spec (Codec.seq op arg) hsep ops (n - m) (bdrop m s) r').2 ⟨
        cast (congrArg Bytes (Nat.sub_sub_self (Nat.sub_le_sub_right (Nat.sub_le n r.remaining) m)).symm) s₂,
        ?_, ?_⟩
      · dsimp [r']
        rw [hs]
        exact prepend_eq_of_eq_splice (bdrop m (r.prepend (splice hm₀ s₁ s₂))) (Nat.sub_le_sub_right (Nat.sub_le n r.remaining) m) s₂ (cast (congrArg Bytes (bdrop_prepend_splice_snd_len r.hle hm₀).symm) r.bytes) (bdrop_prepend_splice_eq_splice r m hm₀ s₁ s₂)
      · exact (relRepeat_cast (Rel (Codec.seq op arg)) ops (Nat.sub_sub_self (Nat.sub_le_sub_right (Nat.sub_le n r.remaining) m)).symm s₂).2 hrel₂
    have htrans : (Suffix.drop m s).trans r' = r := by
      refine Suffix.ext (t₁ := (Suffix.drop m s).trans r') (t₂ := r) ?_ ?_
      · dsimp [r', Suffix.trans]
        exact bdrop_prepend_splice_snd_len r.hle hm₀
      · dsimp [r', Suffix.trans, Suffix.drop]
        rw [hs]
        rw [bdrop_drop_eq_bytes r m hm₀ s₁ s₂]
        change cast (congrArg Bytes (bdrop_prepend_splice_snd_len r.hle hm₀)) (cast (congrArg Bytes (bdrop_prepend_splice_snd_len r.hle hm₀).symm) r.bytes) = r.bytes
        simp
    refine ⟨(a₀, Suffix.drop m s), hmem₁, ?_⟩
    rw [List.mem_filterMap]
    refine ⟨(ops, r'), ?_, ?_⟩
    · exact hmem₂
    · simp [haply, congrArg (fun y => (a, y)) htrans]

/-- Encoder soundness for `chainl1`: any value the chain-encoder prints is in
`relChainl1`. The `foldl.unapply` direction is tied to `foldl.apply` by the
`Iso.law` field of `foldl`, so the maximally-unfolded seed/operands re-fold to the
original value. -/
theorem encodeChainl1_rel {α β : Type} (f : Iso (α × (β × α)) α) (measure : α → Nat)
    (h : MeasureDecreases measure f) (arg : Codec α) (op : Codec β) :
    ∀ (a : α) {n : Nat} {s : Bytes n}, encodeChainl1 f measure h arg op a = some ⟨n, s⟩ →
      relChainl1 f measure h arg op a s := by
  intro a n s he
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
              have heq : (⟨s₀.1 + s'.1, concat s₀.2 s'.2⟩ : Sigma fun k => Bytes k) = ⟨n, s⟩ := by
                simpa using he
              cases heq
              have haply : (foldl f measure h).apply (a₀, ops) = some a :=
                ((foldl f measure h).law (a₀, ops) a).2 hu
              rw [relChainl1]
              refine ⟨a₀, ops, s₀.1, Nat.le.intro rfl, s₀.2, cast (congrArg Bytes (Nat.add_sub_cancel_left s₀.1 s'.1).symm) s'.2, ?_, encode_rel arg a₀ ha, ?_, haply⟩
              · exact concat_eq_splice s₀.2 s'.2
              · exact (relRepeat_cast (Rel (Codec.seq op arg)) ops (Nat.add_sub_cancel_left s₀.1 s'.1).symm s'.2).2 (encodeRepeat_rel (Codec.seq op arg) ops hr)

/-- The bidirectional law for `chainr1` (the right-fold dual of `decodeChainl1_spec`). -/
theorem decodeChainr1_spec {α β : Type} (f : Iso ((α × β) × α) α) (measure : α → Nat)
    (h : MeasureDecreasesR measure f) (arg : Codec α) (op : Codec β)
    (hsep : ConsumesByte (Codec.seq arg op)) :
    ∀ (a : α) {n : Nat} (s : Bytes n) (r : Suffix n), (a, r) ∈ decodeChainr1 f measure h arg op hsep s ↔
      ∃ s₀ : Bytes (n - r.remaining), s = r.prepend s₀ ∧ relChainr1 f measure h arg op a s₀ := by
  intro a n s r
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
        subst r
        rcases (decode_spec arg a₀ (s := s) (r := t)).1 hpr with ⟨s₁, hs₁, hrel₁⟩
        rcases (decodeRepeat_spec (Codec.seq arg op) hsep ops t.remaining t.bytes r').1 hopsr with ⟨s₂, hs₂, hrel₂⟩
        refine ⟨cast (congrArg Bytes (sub_sub_add n t.remaining r'.remaining t.hle r'.hle)) (concat s₁ s₂), ?_, ?_⟩
        · rw [hs₁]
          exact (prepend_assoc t r' s₁ s₂ hs₂.symm).symm
        · rw [relChainr1]
          refine ⟨a₀, ops, n - t.remaining, Nat.sub_le_sub_left r'.hle n, s₁, cast (congrArg Bytes (sub_sub_sub n t.remaining r'.remaining t.hle r'.hle).symm) s₂, ?_, hrel₁, ?_, haply⟩
          · exact cast_concat_splice_sub t.hle r'.hle s₁ s₂
          · exact (relRepeat_cast (Rel (Codec.seq arg op)) ops (sub_sub_sub n t.remaining r'.remaining t.hle r'.hle).symm s₂).2 hrel₂
  · intro hm
    rcases hm with ⟨s₀, hs, hrel⟩
    rw [relChainr1] at hrel
    rcases hrel with ⟨a₀, ops, m, hm₀, s₁, s₂, hs₀, hrel₁, hrel₂, haply⟩
    subst s₀
    have hmem₁ : (a₀, Suffix.drop m s) ∈ decode arg s := by
      refine (decode_spec arg a₀ (s := s) (r := Suffix.drop m s)).2 ⟨
        cast (congrArg Bytes (Nat.sub_sub_self (Nat.le_trans hm₀ (Nat.sub_le n r.remaining))).symm) s₁,
        ?_, ?_⟩
      · rw [hs]
        exact prepend_drop_of_prepend_splice r m hm₀ s₁ s₂
      · exact (Rel_cast arg a₀ (Nat.sub_sub_self (Nat.le_trans hm₀ (Nat.sub_le n r.remaining))).symm s₁).2 hrel₁
    let r' : Suffix (n - m) := Suffix.drop ((n - r.remaining) - m) (bdrop m s)
    have hmem₂ : (ops, r') ∈ decodeRepeat (Codec.seq arg op) hsep (n - m) (bdrop m s) := by
      refine (decodeRepeat_spec (Codec.seq arg op) hsep ops (n - m) (bdrop m s) r').2 ⟨
        cast (congrArg Bytes (Nat.sub_sub_self (Nat.sub_le_sub_right (Nat.sub_le n r.remaining) m)).symm) s₂,
        ?_, ?_⟩
      · dsimp [r']
        rw [hs]
        exact prepend_eq_of_eq_splice (bdrop m (r.prepend (splice hm₀ s₁ s₂))) (Nat.sub_le_sub_right (Nat.sub_le n r.remaining) m) s₂ (cast (congrArg Bytes (bdrop_prepend_splice_snd_len r.hle hm₀).symm) r.bytes) (bdrop_prepend_splice_eq_splice r m hm₀ s₁ s₂)
      · exact (relRepeat_cast (Rel (Codec.seq arg op)) ops (Nat.sub_sub_self (Nat.sub_le_sub_right (Nat.sub_le n r.remaining) m)).symm s₂).2 hrel₂
    have htrans : (Suffix.drop m s).trans r' = r := by
      refine Suffix.ext (t₁ := (Suffix.drop m s).trans r') (t₂ := r) ?_ ?_
      · dsimp [r', Suffix.trans]
        exact bdrop_prepend_splice_snd_len r.hle hm₀
      · dsimp [r', Suffix.trans, Suffix.drop]
        rw [hs]
        rw [bdrop_drop_eq_bytes r m hm₀ s₁ s₂]
        change cast (congrArg Bytes (bdrop_prepend_splice_snd_len r.hle hm₀)) (cast (congrArg Bytes (bdrop_prepend_splice_snd_len r.hle hm₀).symm) r.bytes) = r.bytes
        simp
    refine ⟨(a₀, Suffix.drop m s), hmem₁, ?_⟩
    rw [List.mem_filterMap]
    refine ⟨(ops, r'), ?_, ?_⟩
    · exact hmem₂
    · simp [haply, congrArg (fun y => (a, y)) htrans]

/-- Encoder soundness for `chainr1` (the right-fold dual of `encodeChainl1_rel`). -/
theorem encodeChainr1_rel {α β : Type} (f : Iso ((α × β) × α) α) (measure : α → Nat)
    (h : MeasureDecreasesR measure f) (arg : Codec α) (op : Codec β) :
    ∀ (a : α) {n : Nat} {s : Bytes n}, encodeChainr1 f measure h arg op a = some ⟨n, s⟩ →
      relChainr1 f measure h arg op a s := by
  intro a n s he
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
              have heq : (⟨s₀.1 + s'.1, concat s₀.2 s'.2⟩ : Sigma fun k => Bytes k) = ⟨n, s⟩ := by
                simpa using he
              cases heq
              have haply : (foldr f measure h).apply (a₀, ops) = some a :=
                ((foldr f measure h).law (a₀, ops) a).2 hu
              rw [relChainr1]
              refine ⟨a₀, ops, s₀.1, Nat.le.intro rfl, s₀.2, cast (congrArg Bytes (Nat.add_sub_cancel_left s₀.1 s'.1).symm) s'.2, ?_, encode_rel arg a₀ ha, ?_, haply⟩
              · exact concat_eq_splice s₀.2 s'.2
              · exact (relRepeat_cast (Rel (Codec.seq arg op)) ops (Nat.add_sub_cancel_left s₀.1 s'.1).symm s'.2).2 (encodeRepeat_rel (Codec.seq arg op) ops hr)

/-! ## The chain decode→encode direction, and chain injectivity

The primitives carry `encode_ne_none`/`encode_of_decode`/`encode_injective_of_unambiguous`
(see `Codec.Sound`), each conditional on value- and string-directionality. The chain
combinators are *relations*, not `Codec` values, so their mirror laws take the
relation-level predicates `relFunctional`/`relUnambiguous` over `relChainl1`/
`relChainr1` (the same notions stated over the chain denotation rather than a
`Rel d`). Together they extend the unconditional encode→decode half
(`encodeChainl1_rel`) and the decoder law (`decodeChainl1_spec`) to a full
decode→encode bijection and injectivity under those hypotheses. -/

/-- `relChainl1` is insensitive to a length-cast of its byte string (the
`relFunctional`/`relFunctional`-carrying transport the `_of_decode` laws need to
conclude at the *input* length `n` rather than the decoder's `n - 0`).

`cases e` is sound (not hiding a mismatch) because every conjunct of `relChainl1`
— the ``s = splice …`` equality, and the `Rel arg` / `relRepeat (Rel op)` /
`foldl.apply` sub-relations — is definitionally transported through
`cast (congrArg Bytes e)` (each reduces pointwise; cf. `Rel_cast`/`relRepeat_cast`
in `Codec.Codec`). So the two sides are literally `rfl`. -/
theorem relChainl1_cast {α β : Type} (f : Iso (α × (β × α)) α) (measure : α → Nat)
    (h : MeasureDecreases measure f) (arg : Codec α) (op : Codec β) (a : α)
    {n m : Nat} (e : n = m) (s : Bytes n) :
    relChainl1 f measure h arg op a (cast (congrArg Bytes e) s) ↔ relChainl1 f measure h arg op a s := by
  cases e
  rfl

/-- `relChainr1` is insensitive to a length-cast of its byte string (the
right-fold dual of `relChainl1_cast`); `cases e` is sound by the same
cast-invariance argument as `relChainl1_cast`. -/
theorem relChainr1_cast {α β : Type} (f : Iso ((α × β) × α) α) (measure : α → Nat)
    (h : MeasureDecreasesR measure f) (arg : Codec α) (op : Codec β) (a : α)
    {n m : Nat} (e : n = m) (s : Bytes n) :
    relChainr1 f measure h arg op a (cast (congrArg Bytes e) s) ↔ relChainr1 f measure h arg op a s := by
  cases e
  rfl

/-- **Encoder completeness for a left chain**: every value in `relChainl1` encodes
successfully. The maximal unfold of `a` via `foldl` is tied to the fold's apply by
the `Iso.law` field, so the relation's seed/operands are recovered and each part
encodes (seed via `encode_ne_none`, operands via `encodeRepeat_ne_none`). -/
theorem encodeChainl1_ne_none {α β : Type} (f : Iso (α × (β × α)) α) (measure : α → Nat)
    (h : MeasureDecreases measure f) (arg : Codec α) (op : Codec β) :
    ∀ (a : α) {n : Nat} (s : Bytes n), relChainl1 f measure h arg op a s →
      encodeChainl1 f measure h arg op a ≠ none := by
  intro a n s hrel
  rw [relChainl1] at hrel
  rcases hrel with ⟨a₀, ops, m, _hm, s₁, s₂, _hs, hrel₀, hrelops, haply⟩
  rw [encodeChainl1]
  have hu : (foldl f measure h).unapply a = some (a₀, ops) :=
    ((foldl f measure h).law (a₀, ops) a).1 haply
  rw [hu]
  have hne₀ : encode arg a₀ ≠ none := encode_ne_none arg a₀ s₁ hrel₀
  cases h₁ : encode arg a₀ with
  | none => exact False.elim (hne₀ h₁)
  | some e₀ =>
      have hneops : encodeRepeat (Codec.seq op arg) ops ≠ none :=
        encodeRepeat_ne_none (Codec.seq op arg) ops s₂ hrelops
      cases h₂ : encodeRepeat (Codec.seq op arg) ops with
      | none => exact False.elim (hneops h₂)
      | some eops => simp [h₁, h₂]

/-- **Encoder completeness for a right chain** (the dual of `encodeChainl1_ne_none`). -/
theorem encodeChainr1_ne_none {α β : Type} (f : Iso ((α × β) × α) α) (measure : α → Nat)
    (h : MeasureDecreasesR measure f) (arg : Codec α) (op : Codec β) :
    ∀ (a : α) {n : Nat} (s : Bytes n), relChainr1 f measure h arg op a s →
      encodeChainr1 f measure h arg op a ≠ none := by
  intro a n s hrel
  rw [relChainr1] at hrel
  rcases hrel with ⟨a₀, ops, m, _hm, s₁, s₂, _hs, hrel₀, hrelops, haply⟩
  rw [encodeChainr1]
  have hu : (foldr f measure h).unapply a = some (a₀, ops) :=
    ((foldr f measure h).law (a₀, ops) a).1 haply
  rw [hu]
  have hne₀ : encode arg a₀ ≠ none := encode_ne_none arg a₀ s₁ hrel₀
  cases h₁ : encode arg a₀ with
  | none => exact False.elim (hne₀ h₁)
  | some e₀ =>
      have hneops : encodeRepeat (Codec.seq arg op) ops ≠ none :=
        encodeRepeat_ne_none (Codec.seq arg op) ops s₂ hrelops
      cases h₂ : encodeRepeat (Codec.seq arg op) ops with
      | none => exact False.elim (hneops h₂)
      | some eops => simp [h₁, h₂]

/-- Under chain functionality, a value the left-chain decoder accepts (with no
remainder) re-encodes to exactly the same bytes — the chain mirror of
`encode_of_decode`, making `encodeChainl1 … = some s ↔ (a, Suffix.empty n) ∈ decodeChainl1 … s`
a bijection for functional chains. -/
theorem encodeChainl1_of_decode {α β : Type} (f : Iso (α × (β × α)) α)
    (measure : α → Nat) (h : MeasureDecreases measure f) (arg : Codec α) (op : Codec β)
    (hsep : ConsumesByte (Codec.seq op arg))
    (hd : relFunctional (relChainl1 f measure h arg op)) (a : α)
    {n : Nat} {s : Bytes n} (hdcd : (a, Suffix.empty n) ∈ decodeChainl1 f measure h arg op hsep s) :
    encodeChainl1 f measure h arg op a = some ⟨n, s⟩ := by
  rcases (decodeChainl1_spec f measure h arg op hsep a (s := s) (r := Suffix.empty n)).1 hdcd with
    ⟨s₀, hsplit, hrel⟩
  have hcast : s = cast (congrArg Bytes (Nat.sub_zero n)) s₀ := by
    rw [hsplit]
    exact prepend_empty s₀
  have hrels : relChainl1 f measure h arg op a s := by
    rw [hcast]
    exact (relChainl1_cast f measure h arg op a (Nat.sub_zero n) s₀).1 hrel
  have hne : encodeChainl1 f measure h arg op a ≠ none :=
    encodeChainl1_ne_none f measure h arg op a s hrels
  cases he : encodeChainl1 f measure h arg op a with
  | none => exact False.elim (hne he)
  | some e =>
      rcases e with ⟨n', s'⟩
      have hrel' : relChainl1 f measure h arg op a s' :=
        encodeChainl1_rel f measure h arg op a he
      have hs' : (⟨n', s'⟩ : Sigma fun k => Bytes k) = ⟨n, s⟩ := hd a s' s hrel' hrels
      cases hs'
      rfl

/-- Under chain functionality, a value the right-chain decoder accepts re-encodes
to exactly the same bytes (the dual of `encodeChainl1_of_decode`). -/
theorem encodeChainr1_of_decode {α β : Type} (f : Iso ((α × β) × α) α)
    (measure : α → Nat) (h : MeasureDecreasesR measure f) (arg : Codec α) (op : Codec β)
    (hsep : ConsumesByte (Codec.seq arg op))
    (hd : relFunctional (relChainr1 f measure h arg op)) (a : α)
    {n : Nat} {s : Bytes n} (hdcd : (a, Suffix.empty n) ∈ decodeChainr1 f measure h arg op hsep s) :
    encodeChainr1 f measure h arg op a = some ⟨n, s⟩ := by
  rcases (decodeChainr1_spec f measure h arg op hsep a (s := s) (r := Suffix.empty n)).1 hdcd with
    ⟨s₀, hsplit, hrel⟩
  have hcast : s = cast (congrArg Bytes (Nat.sub_zero n)) s₀ := by
    rw [hsplit]
    exact prepend_empty s₀
  have hrels : relChainr1 f measure h arg op a s := by
    rw [hcast]
    exact (relChainr1_cast f measure h arg op a (Nat.sub_zero n) s₀).1 hrel
  have hne : encodeChainr1 f measure h arg op a ≠ none :=
    encodeChainr1_ne_none f measure h arg op a s hrels
  cases he : encodeChainr1 f measure h arg op a with
  | none => exact False.elim (hne he)
  | some e =>
      rcases e with ⟨n', s'⟩
      have hrel' : relChainr1 f measure h arg op a s' :=
        encodeChainr1_rel f measure h arg op a he
      have hs' : (⟨n', s'⟩ : Sigma fun k => Bytes k) = ⟨n, s⟩ := hd a s' s hrel' hrels
      cases hs'
      rfl

/-- `encodeChainl1` is injective on the bytes it prints, for chain-unambiguous
descriptions (the chain mirror of `encode_injective_of_unambiguous`). -/
theorem encodeChainl1_injective_of_unambiguous {α β : Type} (f : Iso (α × (β × α)) α)
    (measure : α → Nat) (h : MeasureDecreases measure f) (arg : Codec α) (op : Codec β)
    (hd : relUnambiguous (relChainl1 f measure h arg op)) {x y : α} {n : Nat} {s : Bytes n}
    (hx : encodeChainl1 f measure h arg op x = some ⟨n, s⟩)
    (hy : encodeChainl1 f measure h arg op y = some ⟨n, s⟩) : x = y := by
  have hrelx : relChainl1 f measure h arg op x s := encodeChainl1_rel f measure h arg op x hx
  have hrely : relChainl1 f measure h arg op y s := encodeChainl1_rel f measure h arg op y hy
  exact hd s hrelx hrely

/-- `encodeChainr1` is injective on the bytes it prints, for chain-unambiguous
descriptions (the dual of `encodeChainl1_injective_of_unambiguous`). -/
theorem encodeChainr1_injective_of_unambiguous {α β : Type} (f : Iso ((α × β) × α) α)
    (measure : α → Nat) (h : MeasureDecreasesR measure f) (arg : Codec α) (op : Codec β)
    (hd : relUnambiguous (relChainr1 f measure h arg op)) {x y : α} {n : Nat} {s : Bytes n}
    (hx : encodeChainr1 f measure h arg op x = some ⟨n, s⟩)
    (hy : encodeChainr1 f measure h arg op y = some ⟨n, s⟩) : x = y := by
  have hrelx : relChainr1 f measure h arg op x s := encodeChainr1_rel f measure h arg op x hx
  have hrely : relChainr1 f measure h arg op y s := encodeChainr1_rel f measure h arg op y hy
  exact hd s hrelx hrely

/-! ## The derived run combinator `takeWhile`

`takeWhile p` is `many (satisfy p)` — a maximal run of bytes each satisfying `p` —
realized over the existing repetition layer, **not** a new `Codec` constructor.
It is the variable-length-token primitive: an alphabet run (`takeWhile isHexDigit`),
a varint (`takeWhile highBitSet` + a fold `iso`), a UTF-8 code-unit run. Like
`sepBy`/`chainl1`, it is a *relation, a decoder, an encoder* triple (there is no
finite `many` node to embed), and its laws are inherited (`decodeRepeat_spec` /
`encodeRepeat_rel`) with zero new induction. -/

/-- The denotation of `takeWhile p`: `relRepeat` over the step `Rel (satisfy p)`. -/
def relTakeWhile (p : UInt8 → Bool) : List UInt8 → (n : Nat) → Bytes n → Prop :=
  relRepeat (Rel (Codec.satisfy p))

/-- The decoder for `takeWhile p`: the productive repetition decoder over the
`satisfy p` step. Total (the `satisfyConsumesByte` witness is its productivity
proof), and enumerates every run of `p`-satisfying bytes (all prefixes, the full
backtracking union of `many (satisfy p)`). -/
def decodeTakeWhile (p : UInt8 → Bool) {n : Nat} (s : Bytes n) : List (List UInt8 × Suffix n) :=
  decodeRepeat (Codec.satisfy p) (satisfyConsumesByte p) n s

/-- The encoder for `takeWhile p`: encode each byte via `satisfy p`, structural on
the value list (no productivity witness needed, as with every `encodeRepeat`). -/
def encodeTakeWhile (p : UInt8 → Bool) (bs : List UInt8) : Option (Sigma fun n => Bytes n) :=
  encodeRepeat (Codec.satisfy p) bs

/-- The bidirectional law for `takeWhile`, inherited from `decodeRepeat_spec`: a
`takeWhile p` result is exactly a `relTakeWhile p` prefix plus the remainder. -/
theorem decodeTakeWhile_spec (p : UInt8 → Bool) :
    ∀ (bs : List UInt8) (n : Nat) (s : Bytes n) (r : Suffix n),
      (bs, r) ∈ decodeTakeWhile p s ↔
        ∃ s₀ : Bytes (n - r.remaining), s = r.prepend s₀ ∧ relTakeWhile p bs (n - r.remaining) s₀ :=
  decodeRepeat_spec (Codec.satisfy p) (satisfyConsumesByte p)

/-- Encoder soundness for `takeWhile`, inherited from `encodeRepeat_rel`: any run
the `takeWhile` encoder prints is in `relTakeWhile p`. -/
theorem encodeTakeWhile_rel (p : UInt8 → Bool) :
    ∀ (bs : List UInt8) {n : Nat} {s : Bytes n},
      encodeTakeWhile p bs = some ⟨n, s⟩ → relTakeWhile p bs n s :=
  encodeRepeat_rel (Codec.satisfy p)

end Codec
