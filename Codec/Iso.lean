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

-- NB: `iterate`/`foldl` (paper §5.2/§5.3) are coinductive at the `Iso` level
-- (their `law` field would need coinduction). They are deferred to a follow-up;
-- `chainl1` in `Codec.Combinators` needs them and is likewise deferred.

end Iso
