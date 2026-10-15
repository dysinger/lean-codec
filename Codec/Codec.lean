/- Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later -/

import Codec.Iso

/-!
# Codec: the description interface over bytes

This file defines `Codec`, the *description* language re-based onto bytes from
Rendel & Ostermann's `Syntax` (§3.4). A `Codec α` is a syntax description
producing values of type `α`; one description gives both a decoder and an
encoder (the two interpreters are `Codec.decode` and `Codec.encode`).

The combinators are:

  * `iso i $ d`   — apply a partial isomorphism (§3.1 `IsoFunctor`)
  * `d₁ * d₂`     — sequential/product composition (§3.2 `ProductFunctor`)
  * `d₁ | d₂`     — backtracking union (§3.3 `Alternative`), `empty` its unit
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
  | /-- Backtracking union: `d₁ | d₂` returns both alternatives
    (`decode (d₁ | d₂) s = decode d₁ s ++ decode d₂ s`, `Rel (d₁ | d₂) =
    Rel d₁ ∨ Rel d₂`). -/
    alt {α : Type} : Codec α → Codec α → Codec α
  | /-- The always-failing description (`Alternative.empty`). -/
    empty {α : Type} : Codec α
  | /-- The description of a fixed value `x` against the empty bytes. Carries a
    `DecidableEq α` instance so the encoder can test equality (the paper's `Eq α`). -/
    pure {α : Type} [DecidableEq α] : α → Codec α
  | /-- The primitive byte description (`token`, re-based onto `UInt8`). -/
    byte : Codec UInt8

namespace Codec

/-! ## The length-indexed byte string substrate -/

/-- The byte-string substrate: a length-indexed byte string `Bytes n` is a
total function `Fin n → UInt8`. The length `n` is part of the *type*, so every
consumer knows the byte count without an auxiliary length field or an O(n)
traversal, and the read `s i` is a structural indexed load (reducible under
`simp`/`rfl`/`induction` for proofs, and a scalar indexed load in the emitted
IR). There is **one** byte-string type serving as both the proof substrate and
the run-model; there is no second `List`/`Array`/`ByteArray`/`Buffer` carrier. -/
abbrev Bytes (n : Nat) : Type := Fin n → UInt8

/-- The empty byte string. -/
def emptyBytes : Bytes 0 := fun i => Fin.elim0 i

/-- A single-byte string containing exactly `b`. -/
def single (b : UInt8) : Bytes 1 := fun _ => b

/-- Concatenate two byte strings of lengths `m` and `n` into one of length
`m + n`: index `i < m` reads from the left, `i ≥ m` reads from the right. -/
def concat {m n : Nat} (s₁ : Bytes m) (s₂ : Bytes n) : Bytes (m + n) :=
  fun i =>
    if h : i.val < m then s₁ ⟨i.val, h⟩
    else s₂ ⟨i.val - m, by
      have hge : m ≤ i.val := Nat.le_of_not_gt h
      have hlt : i.val < m + n := i.isLt
      exact Nat.sub_lt_left_of_lt_add hge hlt⟩

/-- Reassemble `s₁ : Bytes m` and `s₂ : Bytes (n - m)` into a `Bytes n`, given
a proof `m ≤ n` (so `m + (n - m) = n`). This is the "splice" used by `Rel`'s
`seq` case and by `relRepeat`'s `cons` case — the length-indexed spelling of the
old `List` append split. Defined as the `m ≤ n` cast of `concat s₁ s₂`, so the
split and the concat are definitionally the same function (up to the length cast). -/
def splice {n m : Nat} (hm : m ≤ n) (s₁ : Bytes m) (s₂ : Bytes (n - m)) : Bytes n :=
  cast (congrArg Bytes (show m + (n - m) = n by
    rw [Nat.add_comm]
    exact Nat.sub_add_cancel hm)) (concat s₁ s₂)

/-- Drop the first `m` bytes of a byte string: `bdrop m s i = s (i + m)`.
The result has length `n - m`. -/
def bdrop (m : Nat) {n : Nat} (s : Bytes n) : Bytes (n - m) :=
  fun i => s ⟨i.val + m, by
    have hlt : i.val < n - m := i.isLt
    omega⟩

/-- Take the first `m` bytes of a byte string: `btake m s i = s i` for `i < m`.
The result has length `min m n`. -/
def btake (m : Nat) {n : Nat} (s : Bytes n) : Bytes (min m n) :=
  fun i => s ⟨i.val, by
    have hlt : i.val < min m n := i.isLt
    omega⟩

/-- A decode's remaining buffer: the length `remaining` of the leftover bytes
(with a proof `remaining ≤ n`), together with the leftover bytes themselves.
The consumed length is the named quantity `n - remaining` (recoverable, never a
recomputed `List.length`). This is the spec's `({m : Nat} × Bytes m)` with the
`m ≤ n` witness carried as a field — chosen over the design's `{consumed,
remainder : Bytes (n - consumed)}` spelling because `seq` composes two suffixes
by threading the nested remainder length `m₂ ≤ m₁ ≤ n` directly (no `Nat.sub`
re-computation of `(n - c₁) - c₂`). -/
structure Suffix (n : Nat) where
  /-- The length of the remaining (unconsumed) bytes. -/
  remaining : Nat
  /-- The witness that at most `n` bytes were consumed. -/
  hle : remaining ≤ n
  /-- The remaining bytes, of length `remaining`. -/
  bytes : Bytes remaining

/-- The number of bytes consumed: `n` minus the remaining length. -/
def Suffix.consumed {n : Nat} (t : Suffix n) : Nat := n - t.remaining

/-- The identity suffix: `n` bytes remain (nothing consumed). -/
def Suffix.id (n : Nat) (s : Bytes n) : Suffix n :=
  { remaining := n, hle := Nat.le_refl n, bytes := s }

/-- Drop the first `m` bytes: `n - m` bytes remain. -/
def Suffix.drop {n : Nat} (m : Nat) (s : Bytes n) : Suffix n :=
  { remaining := n - m, hle := Nat.sub_le n m, bytes := bdrop m s }

/-- Compose two successive suffixes: the remaining buffer of `r` (a suffix of `t`)
is a suffix of `n`. Threads the `≤` witness transitively. -/
def Suffix.trans {n : Nat} (t : Suffix n) (r : Suffix t.remaining) : Suffix n :=
  { remaining := r.remaining, hle := Nat.le_trans r.hle t.hle, bytes := r.bytes }

/-- The fully-consumed suffix: zero bytes remain. This is the "empty remaining
buffer" a roundtrip names (`Bytes 0`, the length-indexed spelling of `[]`). -/
def Suffix.empty (n : Nat) : Suffix n :=
  { remaining := 0, hle := Nat.zero_le n, bytes := emptyBytes }

/-- A suffix with zero remaining bytes is exactly the empty suffix. -/
theorem Suffix.eq_empty_of_remaining_zero {n : Nat} (t : Suffix n) (h : t.remaining = 0) :
    t = Suffix.empty n := by
  cases t with
  | mk remaining hle bytes =>
      simp only at h
      cases h
      have hb : bytes = emptyBytes := by
        funext i
        exact Fin.elim0 i
      cases hb
      rfl

/-- `Bytes n` equality is pointwise on `Fin n`, decidable without `Classical.choice`. -/
theorem Bytes.ext {n : Nat} {s₁ s₂ : Bytes n} :
    (∀ i : Fin n, s₁ i = s₂ i) → s₁ = s₂ := by
  intro h
  funext i
  exact h i

/-- `s₁ = s₂` is equivalent to pointwise equality on `Fin n` — provable by
`funext` (left) and `congrFun` (right), both `[propext, Quot.sound]`-only. -/
theorem Bytes.ext_iff {n : Nat} (s₁ s₂ : Bytes n) :
    s₁ = s₂ ↔ ∀ i : Fin n, s₁ i = s₂ i :=
  ⟨fun h i => congrFun h i, Bytes.ext⟩

/-- Decidability of `Bytes n` equality: decided pointwise over the finite `Fin n`,
transported across `Bytes.ext_iff` (no `Classical.choice`). -/
instance {n : Nat} : DecidableEq (Bytes n) :=
  fun s₁ s₂ =>
    decidable_of_iff (∀ i : Fin n, s₁ i = s₂ i) (Bytes.ext_iff s₁ s₂).symm

/-- `Codec α` is inhabited by the always-failing description. -/
instance {α : Type} : Inhabited (Codec α) := ⟨Codec.empty⟩

/-! ## Denotational semantics: `Rel` -/

/-- The denotational relation `Rel d x (s : Bytes n)`: the description `d` relates
the value `x` to the *whole* byte string `s` of length `n`. Defined by structural
recursion on `d`; the `seq` case splits `s` at a Fin index `m` (with `m ≤ n`) into
a relating prefix `Bytes m` and suffix `Bytes (n - m)`. This is the paper's §4.3
graph semantics re-based onto the length-indexed `Bytes` (there is no "remaining
bytes" here — that is internal to the decoder). -/
def Rel {α : Type} (d : Codec α) (x : α) {n : Nat} (s : Bytes n) : Prop :=
  match d with
  | Codec.iso i d => ∃ a, i.apply a = some x ∧ Rel d a s
  | Codec.seq d₁ d₂ =>
      match x with
      | (x₁, x₂) => ∃ (m : Nat) (hm : m ≤ n) (s₁ : Bytes m) (s₂ : Bytes (n - m)),
          s = splice hm s₁ s₂ ∧ Rel d₁ x₁ s₁ ∧ Rel d₂ x₂ s₂
  | Codec.alt d₁ d₂ => Rel d₁ x s ∨ Rel d₂ x s
  | Codec.empty => False
  | Codec.pure x₀ => x = x₀ ∧ n = 0
  | Codec.byte => ∃ h : n = 1, h ▸ s = single x

/-- The unique byte string of length `0` is `emptyBytes`. -/
theorem emptyBytes_unique {n : Nat} (s : Bytes n) (hn : n = 0) : hn ▸ s = emptyBytes := by
  subst hn
  funext i
  exact Fin.elim0 i

/-- An `iso`-description is a relation only when the iso applies without loss. -/
theorem Rel_iso {α β : Type} (i : Iso α β) (d : Codec α) (x : β) {n : Nat} (s : Bytes n) :
    Rel (Codec.iso i d) x s ↔ ∃ a, i.apply a = some x ∧ Rel d a s :=
  Iff.rfl

/-- A `seq`-description relates a pair to a string that splits compatibly between
the two components. -/
theorem Rel_seq {α β : Type} (d₁ : Codec α) (d₂ : Codec β) (x₁ : α) (x₂ : β)
    {n : Nat} (s : Bytes n) :
    Rel (Codec.seq d₁ d₂) (x₁, x₂) s ↔
      ∃ (m : Nat) (hm : m ≤ n) (s₁ : Bytes m) (s₂ : Bytes (n - m)),
        s = splice hm s₁ s₂ ∧ Rel d₁ x₁ s₁ ∧ Rel d₂ x₂ s₂ :=
  Iff.rfl

/-- `alt` is the union of the two relations. -/
theorem Rel_alt {α : Type} (d₁ d₂ : Codec α) (x : α) {n : Nat} (s : Bytes n) :
    Rel (Codec.alt d₁ d₂) x s ↔ Rel d₁ x s ∨ Rel d₂ x s :=
  Iff.rfl

/-- `empty` relates nothing. -/
theorem Rel_empty {α : Type} (x : α) {n : Nat} (s : Bytes n) :
    Rel (Codec.empty : Codec α) x s ↔ False :=
  Iff.rfl

/-- `pure x₀` relates exactly `x₀` to the empty string. -/
theorem Rel_pure {α : Type} [DecidableEq α] (x₀ x : α) {n : Nat} (s : Bytes n) :
    Rel (Codec.pure x₀) x s ↔ x = x₀ ∧ n = 0 :=
  Iff.rfl

/-- `byte` relates `b` to `single b` exactly. -/
theorem Rel_byte (b : UInt8) {n : Nat} (s : Bytes n) :
    Rel Codec.byte b s ↔ ∃ h : n = 1, h ▸ s = single b :=
  Iff.rfl

/-! ## Repetition: the least fixpoint relation -/

/-- The least `nil`/`cons` fixpoint relation for repetition, given a *step*
relation `R : α → {m} → Bytes m → Prop` (the step relates a value to a byte
string of *some* length). The `cons` case splits `s : Bytes n` at a Fin index
`m` (with `m ≤ n`) into a step prefix and a recursive suffix. This is the
well-founded reading of `Rel (many p)` — total for *every* `R`, independent of
whether the step itself matches the empty string. It is the constructive
denotation of the derived `many` combinator; the decoder law is
`Codec.decodeRepeat_spec`. -/
def relRepeat {α : Type} (R : α → {m : Nat} → Bytes m → Prop) :
    List α → (n : Nat) → Bytes n → Prop
  | [], n, _ => n = 0
  | x :: xs, n, s => ∃ (m : Nat) (hm : m ≤ n) (s₁ : Bytes m) (s₂ : Bytes (n - m)),
      s = splice hm s₁ s₂ ∧ R x s₁ ∧ relRepeat R xs (n - m) s₂

/-- A description `p` is *productive* (consumes at least one byte per step) when
every value it relates sits on a non-empty string. This is the paper's
guard under which unbounded `many` decoding terminates: each `cons` step recurses
on a strictly shorter remaining string. -/
def Productive {α : Type} (p : Codec α) : Prop :=
  ∀ x {n : Nat} (s : Bytes n), Rel p x s → n ≠ 0

/-- `relRepeat`'s empty case: the empty list relates only to the empty string. -/
theorem relRepeat_nil {α : Type} (R : α → {m : Nat} → Bytes m → Prop) {n : Nat} (s : Bytes n) :
    relRepeat R [] n s ↔ n = 0 :=
  Iff.rfl

/-! ## Substrate lemmas: casts, splice, and concat arithmetic

The length-indexed `Bytes n := Fin n → UInt8` substrates make the `seq`/`byte`
cases of the laws turn on two proof-shaped facts: (a) `splice` is `concat` cast
along `m + (n - m) = n` (so the two are equal up to that transport), and (b) the
transport itself reduces pointwise. Everything here is `[propext, Quot.sound]`
-only — no `Classical.choice`. -/

/-- Pushing `cast` over a curried function type through an application: casting
`f : α → γ` along `congrArg (fun X => X → γ) h` and applying to `x : β` equals
`f (cast h.symm x)`. This is the single reduction that makes `splice`'s cast
(which lives at the `Bytes = Fin _ → UInt8` function level) reduce pointwise. -/
theorem cast_fun_apply {α β : Sort u} {γ : Sort v} (h : α = β) (f : α → γ) (x : β) :
    cast (congrArg (fun X => X → γ) h) f x = f (cast h.symm x) := by
  subst h
  simp

/-- Casting a `Fin n` along `congrArg Fin e` is `Fin.cast e`. -/
theorem cast_fin {n m : Nat} (e : n = m) (i : Fin n) :
    cast (congrArg Fin e) i = Fin.cast e i := by
  subst e
  rfl

/-- `Fin.cast` preserves the underlying `Nat` value. -/
@[simp] theorem Fin.cast_val {n m : Nat} (e : n = m) (i : Fin n) :
    (Fin.cast e i).val = i.val := rfl

/-- Casting a byte string along `congrArg Bytes e` and reading at a `Nat`-valued
index commutes with re-casting the index: the byte at `⟨k, hk⟩` is unchanged. This
is the one reduction that makes `splice`/`concat` casts disappear pointwise. -/
@[simp] theorem cast_bytes_val {n m : Nat} (e : n = m) (f : Bytes n) (k : Nat) (hk : k < m) :
    (cast (congrArg Bytes e) f) ⟨k, hk⟩ = f ⟨k, by simpa [e] using hk⟩ := by
  subst e
  rfl

/-- The *bare-`Fin`-variable* form of `cast_bytes_val`: casting a byte string along
`congrArg Bytes e` and reading at an index `i : Fin m` equals reading at
`⟨i.val, ·⟩`. Unlike the `⟨k, hk⟩` form, this LHS is a variable projection, so
`rw`/`simp` can fire it on nested casts whose *index* is a compound
`omega`-generated term (`⟨↑(cast … i) - m, ·⟩`) — the `⟨k, hk⟩` form's `k`/`hk`
cannot be unified there. This is the lemma that closes the `prepend_assoc` /
`decode_spec` `seq` reassociation (see tasks 2.3). -/
@[simp] theorem cast_bytes_val' {n m : Nat} (e : n = m) (f : Bytes n) (i : Fin m) :
    (cast (congrArg Bytes e) f) i = f ⟨i.val, by simp [e, i.isLt]⟩ := by
  subst e
  rfl

/-- Proof irrelevance for `Nat` equalities: any two proofs of `n = m` are equal,
so a `cast`/`congrArg` at a length is insensitive to *which* arithmetic proof is
used. This is what lets the laws close without `Classical.choice`. -/
theorem Nat.eq_irrel {n m : Nat} (e₁ e₂ : n = m) : e₁ = e₂ :=
  Subsingleton.elim e₁ e₂

/-- `splice` reduces pointwise: `splice hm s₁ s₂ i` is `concat s₁ s₂` at the
`Fin`-cast of `i` from `Fin n` back to `Fin (m + (n - m))`. This is the one
pointwise lemma every `seq`/`byte` law rewrites through. -/
theorem splice_apply {n m : Nat} (hm : m ≤ n) (s₁ : Bytes m) (s₂ : Bytes (n - m))
    (i : Fin n) :
    splice hm s₁ s₂ i = concat s₁ s₂ (cast (congrArg Fin (show m + (n - m) = n by
      rw [Nat.add_comm]; exact Nat.sub_add_cancel hm)).symm i) := by
  let hfin : Fin (m + (n - m)) = Fin n :=
    congrArg Fin (show m + (n - m) = n by rw [Nat.add_comm]; exact Nat.sub_add_cancel hm)
  unfold splice
  rw [cast_fun_apply (h := hfin)]

/-- `concat` distributes into `splice`: for `s₁ : Bytes n₁`, `s₂ : Bytes n₂`, the
plain concatenation equals `splice` with prefix `s₁` and the length-cast of `s₂`
(to `Bytes ((n₁ + n₂) - n₁)`). This is the ``encode_rel`` `seq`-case lemma (the
`splice_eq_concat` the design notes): `concat` and `splice` agree via a single
transport of the suffix length. -/
theorem concat_eq_splice {n₁ n₂ : Nat} (s₁ : Bytes n₁) (s₂ : Bytes n₂) :
    concat s₁ s₂ = splice (Nat.le.intro rfl : n₁ ≤ n₁ + n₂)
      s₁ (cast (congrArg Bytes (Nat.add_sub_cancel_left n₁ n₂).symm) s₂) := by
  apply Bytes.ext
  intro i
  rw [splice_apply]
  unfold concat
  simp [cast_fin, Fin.cast]

/-- The `Nat`-sub arithmetic for the `seq`-case reassociation:
`(n - m₁) + (m₁ - m₂) = n - m₂` under `m₂ ≤ m₁ ≤ n`. -/
theorem sub_sub_add (n m₁ m₂ : Nat) (hm₁ : m₁ ≤ n) (hm₂ : m₂ ≤ m₁) :
    (n - m₁) + (m₁ - m₂) = n - m₂ := by
  omega

/-- Reconstruct a `Bytes n` from a consumed prefix and a suffix: `t.prepend s₀`
is `s₀` followed by the remaining bytes of `t`. The length cast
`n - (n - t.remaining) = t.remaining` is discharged by `t.hle`. The `decode_spec`
law is stated as ``(x, t) ∈ decode d s ↔ ∃ s₀, t.prepend s₀ = s ∧ Rel d x s₀``. -/
def Suffix.prepend {n : Nat} (t : Suffix n) (s₀ : Bytes (n - t.remaining)) : Bytes n :=
  splice (Nat.sub_le n t.remaining) s₀
    (cast (congrArg Bytes (Nat.sub_sub_self t.hle).symm) t.bytes)

/-- `relRepeat`'s `cons` case: a non-empty list relates to a string iff its head
relates via the step `R` and its tail relates via `relRepeat`, with a compatible
split. -/
theorem relRepeat_cons {α : Type} (R : α → {m : Nat} → Bytes m → Prop) (x : α)
    (xs : List α) {n : Nat} (s : Bytes n) :
    relRepeat R (x :: xs) n s ↔
      ∃ (m : Nat) (hm : m ≤ n) (s₁ : Bytes m) (s₂ : Bytes (n - m)),
        s = splice hm s₁ s₂ ∧ R x s₁ ∧ relRepeat R xs (n - m) s₂ :=
  Iff.rfl

/-- **Least-fixpoint induction** for `relRepeat`: any predicate `P` closed under
the `nil`/`cons` rules holds for every `(xs, s)` related by `relRepeat R`. This is
what makes `relRepeat R` the *least* relation closed under those rules (the title
"least fixpoint" is proved here, not just asserted in the docstring). -/
theorem relRepeat_induction {α : Type} (R : α → {m : Nat} → Bytes m → Prop)
    (P : List α → {m : Nat} → Bytes m → Prop)
    (hnil : P [] emptyBytes)
    (hcons : ∀ (x : α) (xs : List α) {m n : Nat} (hm : m ≤ n) (s₁ : Bytes m) (s₂ : Bytes (n - m)),
        R x s₁ → relRepeat R xs (n - m) s₂ → P xs s₂ → P (x :: xs) (splice hm s₁ s₂)) :
    ∀ (xs : List α) {n : Nat} (s : Bytes n), relRepeat R xs n s → P xs s := by
  intro xs n s h
  induction xs generalizing n s with
  | nil =>
      rw [relRepeat_nil] at h
      subst h
      have hs : s = emptyBytes := by
        funext i
        exact Fin.elim0 i
      rw [hs]
      exact hnil
  | cons x xs ih =>
      rw [relRepeat_cons] at h
      rcases h with ⟨m, hm, s₁, s₂, hs, hx, hxs⟩
      subst s
      exact hcons x xs hm s₁ s₂ hx hxs (ih s₂ hxs)

end Codec
