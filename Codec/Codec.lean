/- Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later -/

import Codec.Iso

/-!
# Codec: the description interface over bytes

This file defines `Codec`, the *description* language re-based onto bytes from
Rendel & Ostermann's `Syntax` (§3.4). A `Codec α` is a syntax description
producing values of type `α`; one description gives both a decoder and an
encoder (the two interpreters live in `Codec.Decode` and `Codec.Encode`).

The combinators are:

  * `iso i $ d`   — apply a partial isomorphism (§3.1 `IsoFunctor`)
  * `d₁ * d₂`     — sequential/product composition (§3.2 `ProductFunctor`)
  * `d₁ | d₂`     — committed choice (§3.3 `Alternative`), `empty` its unit
  * `pure x`      — the description relating `x` to the empty byte string
  * `byte`        — the description relating each byte to itself (`token`)

Note: `Codec` is an inductive *description* (an AST), not the paper's
polymorphically-embedded typeclass. The typeclass reading would prevent the
two interpreters from having types `decode : Codec α → ByteArray → …` and
`encode : Codec α → α → …` (which require `Codec` to be a `Type → Type`
constructor applied to a value type). This is the free-alternative / free-applicative
encoding of syntax descriptions, and it is what makes `Rel`, `decode`, and
`encode` into interpreters over a single description value.
-/

universe u v

/-- A byte codec description: an AST producing values of type `α`. -/
inductive Codec : Type → Type 1
  | /-- Apply a partial isomorphism: `iso i $ d`. -/
    iso {α β : Type} : Iso α β → Codec α → Codec β
  | /-- Sequential/product: `d₁ * d₂` pairs results. -/
    seq {α β : Type} : Codec α → Codec β → Codec (α × β)
  | /-- Committed choice: `d₁ | d₂` tries the left, then the right. -/
    alt {α : Type} : Codec α → Codec α → Codec α
  | /-- The always-failing description (`Alternative.empty`). -/
    empty {α : Type} : Codec α
  | /-- The description of a fixed value `x` against the empty bytes. Carries a
    `DecidableEq α` instance so the encoder can test equality (the paper's `Eq α`). -/
    pure {α : Type} [DecidableEq α] : α → Codec α
  | /-- The primitive byte description (`token`, re-based onto `UInt8`). -/
    byte : Codec UInt8

/-- Apply a partial isomorphism to a description. -/
def isoMap {α β : Type} (i : Iso α β) (d : Codec α) : Codec β :=
  Codec.iso i d

/-- Sequential/product composition. -/
def seq {α β : Type} (d₁ : Codec α) (d₂ : Codec β) : Codec (α × β) :=
  Codec.seq d₁ d₂

/-- Committed choice. -/
def alt {α : Type} (d₁ d₂ : Codec α) : Codec α :=
  Codec.alt d₁ d₂

/-- The always-failing description. -/
def fail {α : Type} : Codec α :=
  Codec.empty

/-! ## Denotational semantics: `Rel` -/

/-- A single-byte sequence containing exactly `b`. -/
def single (b : UInt8) : List UInt8 := [b]

/-- `Codec α` is inhabited by the always-failing description. -/
instance {α : Type} : Inhabited (Codec α) := ⟨Codec.empty⟩

/-- The denotational relation `Rel d x s`: the description `d` relates the value `x` to
the *whole* byte string `s`. Defined by structural recursion on `d`; this is the
paper's §4.3 graph semantics re-based onto `List UInt8` (there is no "remaining
bytes" here — that is internal to the decoder). -/
def Rel {α : Type} (d : Codec α) (x : α) (s : List UInt8) : Prop :=
  match d with
  | Codec.iso i d => ∃ a, i.apply a = some x ∧ Rel d a s
  | Codec.seq d₁ d₂ =>
      match x with
      | (x₁, x₂) => ∃ s₁ s₂, s = s₁ ++ s₂ ∧ Rel d₁ x₁ s₁ ∧ Rel d₂ x₂ s₂
  | Codec.alt d₁ d₂ => Rel d₁ x s ∨ Rel d₂ x s
  | Codec.empty => False
  | Codec.pure x₀ => x = x₀ ∧ s = []
  | Codec.byte => s = single x

/-- An `iso`-description is a relation only when the iso applies without loss. -/
theorem Rel_iso {α β : Type} (i : Iso α β) (d : Codec α) (x : β) (s : List UInt8) :
    Rel (Codec.iso i d) x s ↔ ∃ a, i.apply a = some x ∧ Rel d a s :=
  Iff.rfl

/-- `seq` relates a pair iff the components relate with a compatible split. -/
theorem Rel_seq {α β : Type} (d₁ : Codec α) (d₂ : Codec β) (x : α) (y : β)
    (s : List UInt8) :
    Rel (Codec.seq d₁ d₂) (x, y) s ↔
      ∃ s₁ s₂, s = s₁ ++ s₂ ∧ Rel d₁ x s₁ ∧ Rel d₂ y s₂ :=
  Iff.rfl

/-- `alt` is the union of the two relations. -/
theorem Rel_alt {α : Type} (d₁ d₂ : Codec α) (x : α) (s : List UInt8) :
    Rel (Codec.alt d₁ d₂) x s ↔ Rel d₁ x s ∨ Rel d₂ x s :=
  Iff.rfl

/-- `pure x₀` relates exactly `x₀` to the empty string. -/
theorem Rel_pure {α : Type} [DecidableEq α] (x₀ x : α) (s : List UInt8) :
    Rel (Codec.pure x₀) x s ↔ x = x₀ ∧ s = [] :=
  Iff.rfl

/-- `byte` relates `b` to `[b]` exactly. -/
theorem Rel_byte (b : UInt8) (s : List UInt8) :
    Rel Codec.byte b s ↔ s = single b :=
  Iff.rfl

/-- `empty` never relates. -/
theorem Rel_empty {α : Type} (x : α) (s : List UInt8) :
    Rel (Codec.empty : Codec α) x s ↔ False :=
  Iff.rfl

/-! ## Repetition: the least fixpoint relation -/

/-- The least `nil`/`cons` fixpoint relation for repetition, given a *step*
relation `R : α → List UInt8 → Prop`. This is the well-founded (structural-on-
the-list) reading of `Rel (many p)` — total for *every* `R`, independent of
whether the step itself matches the empty string. It is the constructive
denotation of the derived `many` combinator; the decoder law is
`Codec.Decode.decodeRepeat_spec`. -/
def relRepeat {α : Type} (R : α → List UInt8 → Prop) :
    List α → List UInt8 → Prop
  | [], s => s = []
  | x :: xs, s => ∃ s₁ s₂, s = s₁ ++ s₂ ∧ R x s₁ ∧ relRepeat R xs s₂

/-- A description `p` is *productive* (consumes at least one byte per step) when
every value it relates sits on a non-empty string. This is the paper's
guard under which unbounded `many` decoding terminates: each `cons` step recurses
on a strictly shorter remaining string. -/
def Productive {α : Type} (p : Codec α) : Prop :=
  ∀ x s, Rel p x s → s ≠ []

/-- `relRepeat`'s empty case: the empty list relates only to the empty string. -/
theorem relRepeat_nil {α : Type} (R : α → List UInt8 → Prop) (s : List UInt8) :
    relRepeat R [] s ↔ s = [] :=
  Iff.rfl

/-- `relRepeat`'s `cons` case: a non-empty list relates to a string iff its head
relates via the step `R` and its tail relates via `relRepeat`, with a compatible
split. -/
theorem relRepeat_cons {α : Type} (R : α → List UInt8 → Prop) (x : α)
    (xs : List α) (s : List UInt8) :
    relRepeat R (x :: xs) s ↔
      ∃ s₁ s₂, s = s₁ ++ s₂ ∧ R x s₁ ∧ relRepeat R xs s₂ :=
  Iff.rfl
