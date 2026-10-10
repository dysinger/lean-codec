/- Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later -/

/-!
# Partial isomorphisms

This file defines `Iso`, the category of partial isomorphisms, following
Rendel & Ostermann's *Invertible Syntax Descriptions* (§3.1, §5.1). A partial
isomorphism between types `α` and `β` is a pair of partial functions

    apply   : α → Option β
    unapply : β → Option α

together with a *proof* that they are inverses:

    law : ∀ a b, apply a = some b ↔ unapply b = some a

Unlike the paper, where the inverse invariant is prose, the law is a **field**,
so an `Iso` without its proof cannot be constructed. This is the requirement
"invertibility by construction".
-/

universe u v w

/-- A partial isomorphism between `α` and `β`, carrying its inverse law as a
field. `apply a = some b` holds exactly when `unapply b = some a`. -/
structure Iso (α : Type u) (β : Type v) where
  /-- The forward direction, partial. -/
  apply : α → Option β
  /-- The backward direction, partial. -/
  unapply : β → Option α
  /-- The inverse law: the two directions agree on their domains. -/
  law : ∀ a b, apply a = some b ↔ unapply b = some a

namespace Iso

/-- `Option.bind` evaluates to `some z` exactly when the outer option is `some x`
and the continuation maps `x` to `some z`. -/
theorem bind_eq_some {α : Type u} {β : Type v} (o : Option α) (f : α → Option β)
    (z : β) : o.bind f = some z ↔ ∃ x, o = some x ∧ f x = some z := by
  constructor
  · intro h
    cases o with
    | none => simp at h
    | some x =>
        refine ⟨x, rfl, ?_⟩
        simpa using h
  · intro h
    rcases h with ⟨x, rfl, hx⟩
    simpa using hx

/-- `(if p then some x else none) = some y` iff `p` holds and `x = y`. -/
theorem ite_some_eq_some {α : Type u} {p : Prop} [Decidable p] (x y : α) :
    (if p then some x else none) = some y ↔ p ∧ x = y := by
  by_cases h : p <;> simp [h]

/-- The forward direction. -/
def app (i : Iso α β) (a : α) : Option β := i.apply a

/-- The backward direction. -/
def unapp (i : Iso α β) (b : β) : Option α := i.unapply b

/-- Apply the inverse law left-to-right. -/
theorem apply_eq_some_of_unapply (i : Iso α β) {a : α} {b : β}
    (h : i.unapply b = some a) : i.apply a = some b :=
  (i.law a b).2 h

/-- Apply the inverse law right-to-left. -/
theorem unapply_eq_some_of_apply (i : Iso α β) {a : α} {b : β}
    (h : i.apply a = some b) : i.unapply b = some a :=
  (i.law a b).1 h

/-! ## Category structure -/

/-- `Iso` is a category: identity is the total isomorphism `some`. -/
def id (α : Type u) : Iso α α where
  apply a := some a
  unapply b := some b
  law := by
    intro a b
    constructor <;> intro h <;> simpa using h.symm

/-- Kleisli composition of partial isomorphisms. -/
def comp {α : Type u} {β : Type v} {γ : Type w} (g : Iso β γ) (f : Iso α β) :
    Iso α γ where
  apply a := Option.bind (f.apply a) g.apply
  unapply c := Option.bind (g.unapply c) f.unapply
  law := by
    intro a c
    constructor
    · intro h
      rcases (bind_eq_some (f.apply a) g.apply c).1 h with ⟨b, hf, hg⟩
      have hgu : g.unapply c = some b := g.unapply_eq_some_of_apply hg
      have hfu : f.unapply b = some a := f.unapply_eq_some_of_apply hf
      exact (bind_eq_some (g.unapply c) f.unapply a).2 ⟨b, hgu, hfu⟩
    · intro h
      rcases (bind_eq_some (g.unapply c) f.unapply a).1 h with ⟨b, hg, hf⟩
      have hga : g.apply b = some c := g.apply_eq_some_of_unapply hg
      have hfa : f.apply a = some b := f.apply_eq_some_of_unapply hf
      exact (bind_eq_some (f.apply a) g.apply c).2 ⟨b, hfa, hga⟩

/-- Composition as a notation-friendly function. -/
def trans {α : Type u} {β : Type v} {γ : Type w} (f : Iso α β) (g : Iso β γ) :
    Iso α γ :=
  comp g f

@[inherit_doc Iso.trans]
infixr:80 " ≫ " => Iso.trans

/-! ## Product bifunctor -/

/-- The product bifunctor `×`: maps two isos onto the components of a tuple. -/
def prod {α : Type u} {β : Type v} {γ : Type u} {δ : Type v}
    (i : Iso α β) (j : Iso γ δ) : Iso (α × γ) (β × δ) where
  apply p := Option.bind (i.apply p.1) fun b => Option.bind (j.apply p.2) fun d => some (b, d)
  unapply q := Option.bind (i.unapply q.1) fun a => Option.bind (j.unapply q.2) fun c => some (a, c)
  law := by
    intro p q
    constructor
    · intro h
      rcases (bind_eq_some (i.apply p.1) (fun b => Option.bind (j.apply p.2) (fun d => some (b, d))) q).1 h with
        ⟨b, hib, hb⟩
      rcases (bind_eq_some (j.apply p.2) (fun d => some (b, d)) q).1 hb with ⟨d, hjd, hbd⟩
      have hq : (b, d) = q := by simpa using hbd
      subst q
      have hi : i.unapply b = some p.1 := i.unapply_eq_some_of_apply hib
      have hj : j.unapply d = some p.2 := j.unapply_eq_some_of_apply hjd
      exact (bind_eq_some (i.unapply b) (fun a => Option.bind (j.unapply d) (fun c => some (a, c))) p).2
        ⟨p.1, hi, (bind_eq_some (j.unapply d) (fun c => some (p.1, c)) p).2 ⟨p.2, hj, rfl⟩⟩
    · intro h
      rcases (bind_eq_some (i.unapply q.1) (fun a => Option.bind (j.unapply q.2) (fun c => some (a, c))) p).1 h with
        ⟨a, hia, ha⟩
      rcases (bind_eq_some (j.unapply q.2) (fun c => some (a, c)) p).1 ha with ⟨c, hjc, hac⟩
      have hp : (a, c) = p := by simpa using hac
      subst p
      have hi : i.apply a = some q.1 := (i.law a q.1).2 hia
      have hj : j.apply c = some q.2 := (j.law c q.2).2 hjc
      exact (bind_eq_some (i.apply a) (fun b => Option.bind (j.apply c) (fun d => some (b, d))) q).2
        ⟨q.1, hi, (bind_eq_some (j.apply c) (fun d => some (q.1, d)) q).2 ⟨q.2, hj, rfl⟩⟩

/-! ## Structural isomorphisms -/

/-- Products associate: `α × (β × γ) ↔ (α × β) × γ`. -/
def associate {α : Type u} {β : Type u} {γ : Type u} :
    Iso (α × β × γ) ((α × β) × γ) where
  apply a := some ((a.1, a.2.1), a.2.2)
  unapply a := some (a.1.1, (a.1.2, a.2))
  law := by
    intro a b
    rcases a with ⟨a, b2, c⟩
    rcases b with ⟨⟨a', b'⟩, c'⟩
    constructor
    · intro h
      simp at h
      rcases h with ⟨⟨h1, h2⟩, h3⟩
      subst a
      subst b2
      subst c
      rfl
    · intro h
      simp at h
      rcases h with ⟨h1, ⟨h2, h3⟩⟩
      subst a
      subst b2
      subst c
      rfl

/-- Products commute: `α × β ↔ β × α`. -/
def commute {α : Type u} {β : Type u} : Iso (α × β) (β × α) where
  apply a := some (a.2, a.1)
  unapply b := some (b.2, b.1)
  law := by
    intro a b
    rcases a with ⟨a1, a2⟩
    rcases b with ⟨b2, b1⟩
    constructor
    · intro h
      simp at h
      rcases h with ⟨h1, h2⟩
      subst a1
      subst a2
      rfl
    · intro h
      simp at h
      rcases h with ⟨h1, h2⟩
      subst a1
      subst a2
      rfl

/-- `()` is the right unit: `α ↔ α × ()`. -/
def unit {α : Type u} : Iso α (α × Unit) where
  apply a := some (a, ())
  unapply b := some b.1
  law := by
    intro a b
    rcases b with ⟨b, u⟩
    cases u
    constructor
    · intro h
      simp at h
      subst a
      rfl
    · intro h
      simp at h
      subst b
      rfl

/-- `element x` is the partial iso between `Unit` and the singleton `{x}`. -/
def element {α : Type u} [DecidableEq α] (x : α) : Iso Unit α where
  apply _ := some x
  unapply b := if b = x then some () else none
  law := by
    intro a b
    constructor
    · intro h
      -- some x = some b, so b = x
      have hbx : b = x := by simpa using h.symm
      simp [hbx]
    · intro h
      -- (if b = x then some () else none) = some a
      by_cases hbx : b = x
      · subst b
        simp at h
        rfl
      · simp [hbx] at h

/-- `subset p` is the identity iso restricted to elements satisfying `p`. -/
def subset {α : Type u} {p : α → Prop} [DecidablePred p] : Iso α α where
  apply x := if p x then some x else none
  unapply x := if p x then some x else none
  law := by
    intro a b
    constructor
    · intro h
      by_cases hpa : p a
      · have hab : a = b := by simpa [hpa] using h
        subst b
        simp [hpa]
      · simp [hpa] at h
    · intro h
      by_cases hpa : p a
      · have h' : p b ∧ b = a := (ite_some_eq_some b a).1 h
        have hba : b = a := h'.2
        subst a
        simp [hpa]
      · rcases (ite_some_eq_some b a).1 h with ⟨hpb, hba⟩
        subst a
        contradiction

/-- `inverse` swaps the two directions. -/
def inverse {α : Type u} {β : Type v} (i : Iso α β) : Iso β α where
  apply := i.unapply
  unapply := i.apply
  law := by
    intro a b
    exact (i.law b a).symm

/-- `optionSome` is the partial iso `α ↔ Option α` mapping `x ↦ some x`; the
inverse maps `some x ↦ x` and is undefined on `none`. Used to lift a `Codec α`
to `Codec (Option α)` before the `| pure none` branch of `optional`. -/
def optionSome {α : Type u} : Iso α (Option α) where
  apply x := some (some x)
  unapply o := match o with
    | none => none
    | some x => some x
  law := by
    intro a b
    cases b with
    | none =>
        constructor <;> intro h <;> simp at h
    | some x =>
        constructor
        · intro h
          simp at h
          subst a
          rfl
        · intro h
          simp at h
          subst x
          rfl

/-! ## Lists -/

/-- `nil` is the partial iso between `Unit` and the empty list. -/
def nil {α : Type u} : Iso Unit (List α) where
  apply _ := some []
  unapply l := match l with
    | [] => some ()
    | _ => none
  law := by
    intro a b
    cases b with
    | nil =>
        cases a
        simp
    | cons b bs =>
        cases a
        constructor <;> intro h <;> simp at h

/-- `cons` is the partial iso between `α × List α` and a non-empty `List α`. -/
def cons {α : Type u} : Iso (α × List α) (List α) where
  apply p := some (p.1 :: p.2)
  unapply l := match l with
    | [] => none
    | x :: xs => some (x, xs)
  law := by
    intro a b
    rcases a with ⟨a, as⟩
    cases b with
    | nil =>
        constructor <;> intro h <;> simp at h
    | cons b bs =>
        constructor
        · intro h
          simp at h ⊢
          rcases h with ⟨hab, has⟩
          rw [hab, has]
          exact ⟨rfl, rfl⟩
        · intro h
          simp at h ⊢
          rcases h with ⟨hab, has⟩
          rw [hab, has]
          exact ⟨rfl, rfl⟩

-- `iterate`/`foldl` (paper §5.2/§5.3) need a well-foundedness gating on the step
-- iso; `foldl` is provable via a `measure : α → Nat` (see below). The bare
-- `iterate` primitive would additionally need a user-supplied well-founded relation
-- and has no current consumer, so it is omitted; `foldl` is defined directly.

/-! ## Left-associative folding as an isomorphism (paper §5.2/§5.3) -/

/-- Unfolding via `i.unapply` strictly decreases the measure. This is the
well-foundedness precondition that makes the maximal unfold terminating and
unique, hence makes `foldl` a true partial isomorphism. -/
structure MeasureDecreases {α β : Type} (measure : α → Nat) (i : Iso (α × β) α) : Prop where
  /-- Each unfold step reduces the measure. -/
  dec : ∀ a a' b, i.unapply a = some (a', b) → measure a' < measure a

/-- Left fold of the step iso over a list (the `apply` direction of `foldl`). -/
def foldApply {α β : Type} (i : Iso (α × β) α) (a0 : α) (bs : List β) : Option α :=
  match bs with
  | [] => some a0
  | b :: bs' =>
      match i.apply (a0, b) with
      | none => none
      | some a1 => foldApply i a1 bs'

/-- Maximal unfold (the `unapply` direction of `foldl`), by well-founded recursion
on `measure a`. Peels `i.unapply` until it returns `none`, collecting operands and
backing them out to fold order. -/
noncomputable def foldUnapply {α β : Type} (measure : α → Nat) (i : Iso (α × β) α)
    (h : MeasureDecreases measure i) (a : α) : Option (α × List β) :=
  WellFounded.fix (InvImage.wf measure Nat.lt_wfRel.wf) (fun a ih =>
    match hua : i.unapply a with
    | none => some (a, [])
    | some (a', b) =>
        have hlt : measure a' < measure a := h.dec a a' b hua
        match ih a' hlt with
        | none => none
        | some (seed, bs) => some (seed, bs ++ [b])
  ) a

set_option linter.unusedVariables false in
/- The recursion equation for `foldUnapply` (derived from `WellFounded.fix_eq`). -/
theorem foldUnapply_eq {α β : Type} (measure : α → Nat) (i : Iso (α × β) α)
    (h : MeasureDecreases measure i) (a : α) :
    foldUnapply measure i h a =
      match hua : i.unapply a with
      | none => some (a, [])
      | some (a', b) =>
          match foldUnapply measure i h a' with
          | none => none
          | some (seed, bs) => some (seed, bs ++ [b]) := by
  unfold foldUnapply
  rw [WellFounded.fix_eq]

/-- `foldApply` is associative over list append. -/
theorem foldApply_append {α β : Type} (i : Iso (α × β) α) (a : α) (bs cs : List β) :
    foldApply i a (bs ++ cs) =
      Option.bind (foldApply i a bs) fun x => foldApply i x cs := by
  induction bs generalizing a with
  | nil => simp [foldApply]
  | cons b bs' ih =>
      simp [foldApply]
      cases h : i.apply (a, b) with
      | none => simp
      | some a1 => simp [ih a1]

/-- Soundness of the maximal unfold: `foldUnapply a = (seed, ops)` gives a fold
that reproduces `a` from a terminal `seed`. -/
theorem foldUnapply_sound {α β : Type} (i : Iso (α × β) α) (measure : α → Nat)
    (h : MeasureDecreases measure i) :
    ∀ a seed ops, foldUnapply measure i h a = some (seed, ops) →
      i.unapply seed = none ∧ foldApply i seed ops = some a := by
  intro a
  have hwf : WellFounded (InvImage (· < ·) measure) := InvImage.wf measure Nat.lt_wfRel.wf
  induction a using WellFounded.induction (hwf := hwf) with
  | h a ih =>
      intro seed ops hf
      rw [foldUnapply_eq] at hf
      cases hua : i.unapply a with
      | none =>
          rw [hua] at hf
          rcases hf with ⟨rfl, rfl⟩
          exact ⟨hua, rfl⟩
      | some va =>
          rcases va with ⟨a', b⟩
          rw [hua] at hf
          cases hrec : foldUnapply measure i h a' with
          | none => simp [hrec] at hf
          | some v =>
              rcases v with ⟨seed', ops'⟩
              simp [hrec] at hf
              rcases hf with ⟨rfl, hops⟩
              have hlt : InvImage (· < ·) measure a' a := h.dec a a' b hua
              have hrec' := ih a' hlt seed' ops' hrec
              rcases hrec' with ⟨hterm, hfold⟩
              refine ⟨hterm, ?_⟩
              rw [← hops]
              have hia : i.apply (a', b) = some a := (i.law (a', b) a).2 hua
              rw [foldApply_append]
              rw [hfold]
              simp [foldApply, hia]

/-- A nonempty list is its `dropLast` concatenated with a singleton of its last element. -/
theorem dropLast_append_getLast {α : Type} (bs : List α) (h : bs ≠ []) :
    bs = bs.dropLast ++ [bs.getLast h] := by
  obtain ⟨b, hgl⟩ : ∃ b, bs.getLast? = some b :=
    ⟨bs.getLast h, List.getLast?_eq_some_getLast h⟩
  have hsplit := List.getLast?_eq_some_iff.mp hgl
  rcases hsplit with ⟨ys, rfl⟩
  simp

/-- Completeness of the maximal unfold: folding a terminal seed over a list and
unfolding the result returns the seed and the list. Proved by well-founded
induction on the measure of the final state, peeling one element from the tail. -/
theorem foldUnapply_of_foldApply {α β : Type} (i : Iso (α × β) α) (measure : α → Nat)
    (h : MeasureDecreases measure i) :
    ∀ a bs a', i.unapply a = none → foldApply i a bs = some a' →
      foldUnapply measure i h a' = some (a, bs) := by
  intro a bs a' ht hap
  revert a bs ht hap
  have hwf : WellFounded (InvImage (· < ·) measure) := InvImage.wf measure Nat.lt_wfRel.wf
  induction a' using WellFounded.induction (hwf := hwf) with
  | h a' ih =>
      intro a bs ht hap
      rw [foldUnapply_eq]
      by_cases hbs : bs = []
      · subst bs
        simp [foldApply] at hap
        subst a'
        rw [ht]
      · have hsplit := dropLast_append_getLast bs hbs
        rw [hsplit] at hap
        -- foldApply a (bs.dropLast ++ [getLast]) = some a'
        rw [foldApply_append] at hap
        -- Option.bind (foldApply a bs.dropLast) (fun a0 => foldApply a0 [getLast]) = some a'
        cases hpre : foldApply i a bs.dropLast with
        | none =>
            rw [hpre] at hap
            simp at hap
        | some a0 =>
            rw [hpre] at hap
            simp [foldApply] at hap
            -- hap : (match i.apply (a0, bs.getLast hbs) with ...) = some a'
            cases hlast : i.apply (a0, bs.getLast hbs) with
            | none => simp [hlast] at hap
            | some a'' =>
                simp [hlast] at hap
                subst a''
                -- now hap says a' = a';
                -- i.unapply a' = some (a0, getLast) by i.law
                have hua' : i.unapply a' = some (a0, bs.getLast hbs) := (i.law (a0, bs.getLast hbs) a').1 hlast
                rw [hua']
                simp
                -- goal: foldUnapply measure i h (some...) = some (a, bs); reduce further
                -- need foldUnapply a0 = some (a, bs.dropLast), by IH
                have hlt : InvImage (· < ·) measure a0 a' := h.dec a' a0 (bs.getLast hbs) hua'
                have hrec := ih a0 hlt a bs.dropLast ht hpre
                rw [hrec]
                simp
                -- foldUnapply a' = some (a, bs.dropLast ++ [getLast]) = some (a, bs)
                rw [← hsplit]

/-- The `apply` direction of `foldl`: folds the step over the list, restricted to
terminal seeds. -/
def foldlApply {α β : Type} (i : Iso (α × β) α) (a : α) (bs : List β) : Option α :=
  match i.unapply a with
  | none => foldApply i a bs
  | some _ => none

/-- Left-associative folding as a partial isomorphism (paper §5.3 `foldl`).

`foldl i` maps a seed `a : α` and a list `bs : List β` to the left fold of the step
iso `i : Iso (α × β) α` over `bs`; inversely, it maximally unfolds a result back
into `(seed, operands)`. The `measure : α → Nat` parameter is the well-foundedness
witness: unfolding via `i.unapply` must strictly decrease `measure` (see
`MeasureDecreases`), which makes the maximal unfold terminating and unique, so the
inverse law holds *unconditionally* (no "modulo equivalence classes").

`apply` is restricted to *terminal* seeds (those with `i.unapply a = none`): this is
the honest domain on which the fold/unfold is a genuine bijection. -/
noncomputable def foldl {α β : Type} (i : Iso (α × β) α) (measure : α → Nat)
    (h : MeasureDecreases measure i) : Iso (α × List β) α where
  apply x := match x with | (a, bs) => foldlApply i a bs
  unapply a := foldUnapply measure i h a
  law := by
    intro x y
    rcases x with ⟨a, bs⟩
    constructor
    · intro hap
      cases hua : i.unapply a with
      | none =>
          simp [foldlApply, hua] at hap
          exact foldUnapply_of_foldApply i measure h a bs y hua hap
      | some va =>
          simp [foldlApply, hua] at hap
    · intro hun
      have hsnd := foldUnapply_sound i measure h y a bs hun
      rcases hsnd with ⟨ht, hfoo⟩
      simp [foldlApply, ht, hfoo]

/-! ## Right-associative folding as an isomorphism (the dual of `foldl`) -/

/-- Unfolding via the *right* step `i.unapply` (element on the left) strictly
decreases the measure. This is the well-foundedness precondition for `foldr`,
the right-fold dual of `foldl`. The step type `Iso (β × α) α` is distinct from
`foldl`'s `Iso (α × β) α`: the element is on the left, the accumulator on the
right, so `unapply a = some (b, a')`. -/
structure MeasureDecreasesR {α β : Type} (measure : α → Nat) (i : Iso (β × α) α) : Prop where
  /-- Each unfold step reduces the measure. -/
  dec : ∀ a b a', i.unapply a = some (b, a') → measure a' < measure a

/-- Right fold of the step iso over a list (the `apply` direction of `foldr`).
`foldrApply i a0 [b1, …, bn]` = `i (b1, i (b2, … i (bn, a0)))` — the rightmost
element is folded first (innermost). -/
def foldrApply {α β : Type} (i : Iso (β × α) α) (a0 : α) (bs : List β) : Option α :=
  match bs with
  | [] => some a0
  | b :: bs' =>
      match foldrApply i a0 bs' with
      | none => none
      | some acc => i.apply (b, acc)

/-- Maximal unfold (the `unapply` direction of `foldr`), by well-founded recursion
on `measure a`. Peels `i.unapply a = some (b, a')` (element first), recursing on
`a'` and *prepending* `b` — the dual of `foldl`'s `foldUnapply` (which appends). -/
noncomputable def foldrUnapply {α β : Type} (measure : α → Nat) (i : Iso (β × α) α)
    (h : MeasureDecreasesR measure i) (a : α) : Option (α × List β) :=
  WellFounded.fix (InvImage.wf measure Nat.lt_wfRel.wf) (fun a ih =>
    match hua : i.unapply a with
    | none => some (a, [])
    | some (b, a') =>
        have hlt : measure a' < measure a := h.dec a b a' hua
        match ih a' hlt with
        | none => none
        | some (seed, bs) => some (seed, b :: bs)
  ) a

set_option linter.unusedVariables false in
/- The recursion equation for `foldrUnapply` (derived from `WellFounded.fix_eq`). -/
theorem foldrUnapply_eq {α β : Type} (measure : α → Nat) (i : Iso (β × α) α)
    (h : MeasureDecreasesR measure i) (a : α) :
    foldrUnapply measure i h a =
      match hua : i.unapply a with
      | none => some (a, [])
      | some (b, a') =>
          match foldrUnapply measure i h a' with
          | none => none
          | some (seed, bs) => some (seed, b :: bs) := by
  unfold foldrUnapply
  rw [WellFounded.fix_eq]

/-- `foldrApply` is associative over list append (in the right-fold sense:
folding over `bs ++ cs` folds `cs` first (innermost), then folds `bs` over the
result). This is exactly the monad associativity of `Option.bind`. -/
theorem foldrApply_append {α β : Type} (i : Iso (β × α) α) (a : α) (bs cs : List β) :
    foldrApply i a (bs ++ cs) =
      Option.bind (foldrApply i a cs) fun x => foldrApply i x bs := by
  induction bs generalizing a with
  | nil => simp [foldrApply]
  | cons b bs' ih =>
      simp [foldrApply, ih]
      -- goal: (Option.bind (foldrApply i a cs) fun x => foldrApply i x bs').bind
      --        (fun acc => i.apply (b, acc))
      --     = Option.bind (foldrApply i a cs) fun x =>
      --        (foldrApply i x bs').bind (fun acc => i.apply (b, acc))
      cases h : foldrApply i a cs with
      | none => simp
      | some acc => simp
/-- A nonempty list is its head and tail. -/
theorem cons_head_tail {α : Type} {b : α} {bs : List α} : b :: bs = [b] ++ bs := rfl

/-- Soundness of the maximal unfold: `foldrUnapply a = (seed, ops)` gives a right
fold that reproduces `a` from a terminal `seed`. -/
theorem foldrUnapply_sound {α β : Type} (i : Iso (β × α) α) (measure : α → Nat)
    (h : MeasureDecreasesR measure i) :
    ∀ a seed ops, foldrUnapply measure i h a = some (seed, ops) →
      i.unapply seed = none ∧ foldrApply i seed ops = some a := by
  intro a
  have hwf : WellFounded (InvImage (· < ·) measure) := InvImage.wf measure Nat.lt_wfRel.wf
  induction a using WellFounded.induction (hwf := hwf) with
  | h a ih =>
      intro seed ops hf
      rw [foldrUnapply_eq] at hf
      cases hua : i.unapply a with
      | none =>
          rw [hua] at hf
          rcases hf with ⟨rfl, rfl⟩
          exact ⟨hua, rfl⟩
      | some va =>
          rcases va with ⟨b, a'⟩
          rw [hua] at hf
          cases hrec : foldrUnapply measure i h a' with
          | none => simp [hrec] at hf
          | some v =>
              rcases v with ⟨seed', ops'⟩
              simp [hrec] at hf
              rcases hf with ⟨rfl, hops⟩
              have hlt : InvImage (· < ·) measure a' a := h.dec a b a' hua
              have hrec' := ih a' hlt seed' ops' hrec
              rcases hrec' with ⟨hterm, hfold⟩
              refine ⟨hterm, ?_⟩
              rw [← hops]
              have hia : i.apply (b, a') = some a := (i.law (b, a') a).2 hua
              rw [foldrApply]
              rw [hfold]
              simp [hia]

/-- Completeness of the maximal unfold: right-folding a terminal seed over a list
and unfolding the result returns the seed and the list. Proved by well-founded
induction on the measure of the final state, peeling one element from the *head*. -/
theorem foldrUnapply_of_foldrApply {α β : Type} (i : Iso (β × α) α) (measure : α → Nat)
    (h : MeasureDecreasesR measure i) :
    ∀ a bs a', i.unapply a = none → foldrApply i a bs = some a' →
      foldrUnapply measure i h a' = some (a, bs) := by
  intro a bs a' ht hap
  revert a bs ht hap
  have hwf : WellFounded (InvImage (· < ·) measure) := InvImage.wf measure Nat.lt_wfRel.wf
  induction a' using WellFounded.induction (hwf := hwf) with
  | h a' ih =>
      intro a bs ht hap
      rw [foldrUnapply_eq]
      cases bs with
      | nil =>
          simp [foldrApply] at hap
          subst a'
          rw [ht]
      | cons b bs' =>
          -- foldrApply a (b :: bs') = some a'
          simp [foldrApply] at hap
          cases htail : foldrApply i a bs' with
          | none => simp [htail] at hap
          | some acc =>
              simp [htail] at hap
              cases hlast : i.apply (b, acc) with
              | none => simp [hlast] at hap
              | some a'' =>
                  simp [hlast] at hap
                  subst a''
                  -- now: i.unapply a' = some (b, acc) by i.law
                  have hua' : i.unapply a' = some (b, acc) := (i.law (b, acc) a').1 hlast
                  rw [hua']
                  simp
                  -- need foldrUnapply acc = some (a, bs'), by IH
                  have hlt : InvImage (· < ·) measure acc a' := h.dec a' b acc hua'
                  have hrec := ih acc hlt a bs' ht htail
                  rw [hrec]

/-- The `apply` direction of `foldr`: right-folds the step over the list,
restricted to terminal seeds. -/
def foldrApply' {α β : Type} (i : Iso (β × α) α) (a : α) (bs : List β) : Option α :=
  match i.unapply a with
  | none => foldrApply i a bs
  | some _ => none

/-- Right-associative folding as a partial isomorphism (the dual of §5.3 `foldl`).

`foldr i` maps a seed `a : α` and a list `bs : List β` to the right fold of the
step iso `i : Iso (β × α) α` over `bs`; inversely, it maximally unfolds a result
back into `(seed, operands)`. The `measure : α → Nat` parameter is the
well-foundedness witness: unfolding via `i.unapply` must strictly decrease
`measure` (see `MeasureDecreasesR`).

`apply` is restricted to *terminal* seeds, exactly as `foldl`. The right-fold step
has the element on the left (`Iso (β × α) α`), so `foldr` is a *fresh* derivation
— not `inverse ∘ foldl ∘ inverse`, which is type-incoherent. -/
noncomputable def foldr {α β : Type} (i : Iso (β × α) α) (measure : α → Nat)
    (h : MeasureDecreasesR measure i) : Iso (α × List β) α where
  apply x := match x with | (a, bs) => foldrApply' i a bs
  unapply a := foldrUnapply measure i h a
  law := by
    intro x y
    rcases x with ⟨a, bs⟩
    constructor
    · intro hap
      cases hua : i.unapply a with
      | none =>
          simp [foldrApply', hua] at hap
          exact foldrUnapply_of_foldrApply i measure h a bs y hua hap
      | some va =>
          simp [foldrApply', hua] at hap
    · intro hun
      have hsnd := foldrUnapply_sound i measure h y a bs hun
      rcases hsnd with ⟨ht, hfoo⟩
      simp [foldrApply', ht, hfoo]

/- `iterate` (paper §5.3) is *not* provided as an `Iso`: the paper's definition
(`apply` iterated via a `driver` until failure, and dually `unapply`) carries its
inverse law only "modulo equivalence classes" — the forward-iteration fixpoint
`b` (where `apply b = none`) and the backward-iteration fixpoint `a` (where
`unapply a = none`) need not coincide, because `apply a = some b ↔ unapply b =
some a` does not force `apply a = none ↔ unapply a = none`. Encoding the law as a
field would require a per-element "chain-isolated in both directions"
precondition, which is precisely the gloss this library rejects. `foldl` (proved
directly, above) is the combinator `chainl1` actually needs; `iterate` is omitted
rather than shipped with a subtly-unsound law. -/

end Iso
