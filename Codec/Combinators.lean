/- Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later -/

import Codec.Codec

/-!
# Derived combinators

Generic, byte-agnostic combinators built from the primitives (the paper §6.1):

  * `many p` — zero or more, the paper's `many` (§3.4)
  * `p *> q`, `p <* q` — pair variants that ignore a side (the paper's `*>`, `<*`)
  * `between open close p` — `open *> p <* close`

`many` is recursive and hence `partial`. Under the nondeterministic (backtracking)
decoder it is sound *unconditionally* — exactly the paper's `many` (§3.4): `decode
(many p) s` returns the empty-list result *and* every one-or-more result, so the
bidirectional law holds without any prefix-disjointness gate. `chainl1` (below) is
built on the proved `Iso.foldl` (paper §5.2/§5.3); its `law` is part of
`Iso.foldl`'s law field, not a separate proof.
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

/-- `many p` describes a list: either empty, or one `p` followed by `many p`
(the paper's `many`, §3.4). Recursive, hence `partial`. -/
partial def many {α : Type} (p : Codec α) : Codec (List α) :=
  Codec.alt (Codec.iso (Iso.nil) (Codec.pure ()))
    (Codec.iso (Iso.cons) (Codec.seq p (many p)))

/-- `chainl1 arg op f` parses/prints a *non-empty* left-associative chain of
`arg` separated by `op`, folding left via the step iso `f : Iso (α × (β × α)) α`
(the paper's `chainl1`, §6.1). Built on `Iso.foldl`; `measure`/`h` are the
well-foundedness witness (see `Iso.MeasureDecreases`). -/
noncomputable def chainl1 {α β : Type} (arg : Codec α) (op : Codec β)
    (f : Iso (α × (β × α)) α) (measure : α → Nat)
    (h : Iso.MeasureDecreases measure f) : Codec α :=
  Codec.iso (Iso.foldl f measure h) (Codec.seq arg (many (Codec.seq op arg)))

/-! ## Repetition and sum combinators (paper §6.1/§6.2) -/

/-- `some p` is one-or-more `p` (`cons $ (p * many p)`): a non-empty list. -/
def some {α : Type} (p : Codec α) : Codec (List α) :=
  Codec.iso (Iso.cons) (Codec.seq p (many p))

/-- `many1 p` is an alias for `some p` (one-or-more). -/
def many1 {α : Type} (p : Codec α) : Codec (List α) :=
  some p

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

/-- `sepBy p sep` is a leading `p` followed by zero or more `(sep *> p)`, folded
to `List α`. -/
def sepBy {α : Type} (p : Codec α) (sep : Codec Unit) : Codec (List α) :=
  Codec.iso (Iso.cons) (Codec.seq p (many (seqRight sep p)))

/-- `sepBy1 p sep` is a leading `p` followed by one or more `(sep *> p)`, folded
to `List α`. -/
def sepBy1 {α : Type} (p : Codec α) (sep : Codec Unit) : Codec (List α) :=
  Codec.iso (Iso.cons) (Codec.seq p (some (seqRight sep p)))

/-- `chainr1 arg op f` parses/prints a *non-empty* right-associative chain of
`arg` separated by `op`, folding right via the step iso
`f : Iso ((α × β) × α) α` (the dual of `chainl1`; the combined element `(α × β)`
sits on the left, the accumulator `α` on the right). Built on `Iso.foldr`;
`measure`/`h` are the well-foundedness witness (see `Iso.MeasureDecreasesR`). -/
noncomputable def chainr1 {α β : Type} (arg : Codec α) (op : Codec β)
    (f : Iso ((α × β) × α) α) (measure : α → Nat)
    (h : Iso.MeasureDecreasesR measure f) : Codec α :=
  Codec.iso (Iso.foldr f measure h) (Codec.seq arg (many (Codec.seq arg op)))

/-! ## Bounded repetition (total and evaluable) -/

/-- `count n p` is exactly `n` repetitions of `p` (a list of length `n`), by
structural induction on `n`. Total and `#eval`-able (unlike `many`, which is
`partial`). -/
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

/-- `some p` relates a non-empty list iff its head relates via `p` and its tail
via `many p`. -/
theorem Rel_some {α : Type} (p : Codec α) (xs : List α) (s : List UInt8) :
    Rel (some p) xs s ↔
      ∃ x rest s₁ s₂, xs = x :: rest ∧ s = s₁ ++ s₂ ∧ Rel p x s₁ ∧ Rel (many p) rest s₂ := by
  unfold some
  rw [Rel_iso]
  constructor
  · intro h
    rcases h with ⟨xy, hcons, hseq⟩
    rcases xy with ⟨xh, rest⟩
    have hxs : xs = xh :: rest := by
      exact (Option.some.inj hcons).symm
    subst xs
    rw [Rel_seq] at hseq
    rcases hseq with ⟨s₁, s₂, hsplit, hp, hm⟩
    exact ⟨xh, rest, s₁, s₂, rfl, hsplit, hp, hm⟩
  · intro h
    rcases h with ⟨x, rest, s₁, s₂, hxs, hsplit, hp, hm⟩
    subst xs
    exact ⟨(x, rest), rfl, (Rel_seq p (many p) x rest s).2 ⟨s₁, s₂, hsplit, hp, hm⟩⟩

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

end Codec
