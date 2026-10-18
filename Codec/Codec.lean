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
two interpreters from having types `decode : Codec α → {n : Nat} → Bytes n → …` and
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
  | /-- The byte-token-with-guard: `satisfy p` relates a byte `b` to `single b`
    exactly when `p b = true`. `decode` consumes one byte iff `p b`, else `[]`;
    `encode` emits one byte iff `p b`, else `none`. The single substrate-touching
    leaf beyond `byte`; no BE/LE/fixed-width/`varint`/text/tagged-sum constructor
    exists or will be added. -/
    satisfy : (UInt8 → Bool) → Codec UInt8

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

/-- The cast proof of `splice`: `m + (n - m) = n` under `m ≤ n`. Named so the
cast argument of `splice`/`prepend` is a clean constant (not an inline
`show … by rw …` proof), which `rw`/`simp` can structurally match when closing
the `seq`/`byte` laws (an inline `omega`/`Nat.add_comm` proof would be opaque to
the `cast`-reduction lemmas). -/
theorem splice_add {n m : Nat} (hm : m ≤ n) : m + (n - m) = n := by
  rw [Nat.add_comm]
  exact Nat.sub_add_cancel hm

/-- Reassemble `s₁ : Bytes m` and `s₂ : Bytes (n - m)` into a `Bytes n`, given
a proof `m ≤ n` (so `m + (n - m) = n`). This is the "splice" used by `Rel`'s
`seq` case and by `relRepeat`'s `cons` case — the length-indexed spelling of the
old `List` append split. Defined as the `m ≤ n` cast of `concat s₁ s₂`, so the
split and the concat are definitionally the same function (up to the length cast). -/
def splice {n m : Nat} (hm : m ≤ n) (s₁ : Bytes m) (s₂ : Bytes (n - m)) : Bytes n :=
  cast (congrArg Bytes (splice_add hm)) (concat s₁ s₂)

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

/-- Extensionality for `Suffix n`: two suffixes are equal when their `remaining`
lengths agree (up to the transport `hrem`) and their `bytes` fields agree under
that same transport. The `hle` field is proof-irrelevant. Used by `decode_spec`'s
`seq` backward third goal to close `r = Suffix.trans t₁ t₂` from the
`bdrop_drop_eq_bytes` field equality. `[propext, Quot.sound]`-only. -/
theorem Suffix.ext {n : Nat} {t₁ t₂ : Suffix n}
    (hrem : t₁.remaining = t₂.remaining)
    (hbytes : cast (congrArg Bytes hrem) t₁.bytes = t₂.bytes) : t₁ = t₂ := by
  cases t₁ with
  | mk rem₁ hle₁ bytes₁ =>
      cases t₂ with
      | mk rem₂ hle₂ bytes₂ =>
          simp only at hrem
          subst rem₁
          have hbytes' : bytes₁ = bytes₂ := by
            simpa using hbytes
          subst bytes₁
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
  | Codec.satisfy p => p x = true ∧ ∃ h : n = 1, h ▸ s = single x

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

/-- `satisfy p` relates `b` to `single b` exactly when `p b` holds. -/
theorem Rel_satisfy (p : UInt8 → Bool) (b : UInt8) {n : Nat} (s : Bytes n) :
    Rel (Codec.satisfy p) b s ↔ p b = true ∧ ∃ h : n = 1, h ▸ s = single b :=
  Iff.rfl

/-- `Rel` is insensitive to a length-cast of its byte string (`cast (congrArg Bytes e)`,
for `e : n = m`, is the same string transported across the Fin re-indexing). Needed to
re-state `encode_rel`'s `seq` case, where the `splice` decomposition gives the suffix a
`Bytes (n₁ + n₂ - n₁)` type instead of the encoder's `Bytes n₂`. `[propext, Quot.sound]`-only. -/
theorem Rel_cast {α : Type} (d : Codec α) (x : α) {n m : Nat} (e : n = m) (s : Bytes n) :
    Rel d x (cast (congrArg Bytes e) s) ↔ Rel d x s := by
  subst m
  rfl

/-- The reverse-length form of `Rel_cast` (`e : m = n`, casting `s : Bytes m`). -/
theorem Rel_cast_symm {α : Type} (d : Codec α) (x : α) {n m : Nat} (e : m = n) (s : Bytes m) :
    Rel d x (cast (congrArg Bytes e) s) ↔ Rel d x s := by
  subst m
  rfl

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

/-- `relRepeat` is insensitive to a length-cast of its byte string: `relRepeat R xs m
(cast (congrArg Bytes e) s)` iff `relRepeat R xs n s` for `e : n = m`. The
`relRepeat`-level analogue of `Rel_cast`, needed by `encodeRepeat_rel`'s `cons` case
(where the recursive suffix length `n₂` is cast to `(n₁ + n₂) - n₁`). Proved by
`subst`, no `Classical.choice`. -/
theorem relRepeat_cast {α : Type} (R : α → {m : Nat} → Bytes m → Prop) (xs : List α)
    {n m : Nat} (e : n = m) (s : Bytes n) :
    relRepeat R xs m (cast (congrArg Bytes e) s) ↔ relRepeat R xs n s := by
  subst m
  rfl

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

/-- The `.symm`-aware form of `cast_bytes_val'`: casting a byte string along
`Eq.symm (congrArg Bytes e)` (the spelling `Suffix.prepend`/`concat_eq_splice`'s
suffix length produces — `Nat.sub_sub_self …` and friends are `.symm`-wrapped)
and reading at `i : Fin m` equals reading at `⟨i.val, ·⟩`. `Suffix.prepend` casts
its `bytes` field along `(Nat.sub_sub_self t.hle).symm`, which is this `.symm` form;
without it the `decode_spec` `seq` case cannot reduce the `t₁.bytes` read. -/
@[simp] theorem cast_bytes_val_symm {n m : Nat} (e : n = m) (f : Bytes m) (i : Fin n) :
    (cast (Eq.symm (congrArg Bytes e)) f) i = f ⟨i.val, by simpa [e] using i.isLt⟩ := by
  subst e
  rfl

/-- Proof irrelevance for `Nat` equalities: any two proofs of `n = m` are equal,
so a `cast`/`congrArg` at a length is insensitive to *which* arithmetic proof is
used. This is what lets the laws close without `Classical.choice`. -/
theorem Nat.eq_irrel {n m : Nat} (e₁ e₂ : n = m) : e₁ = e₂ :=
  Subsingleton.elim e₁ e₂

/-- Casting a `Fin m` along the *symmetric* form `Eq.symm (congrArg Fin e)` (the
spelling `splice`/`prepend` produce — `.symm` of a `congrArg Fin`, not a bare
`congrArg Fin`) preserves the index's `Nat` value. This is the `.symm`-aware form of
`cast_fin`/`Fin.cast_val` that `rw`/`simp` need to close the `seq`-law reassociation;
without it the length-index cast (`splice … i`, with `i : Fin n`) does not reduce
to a bare `⟨·.val, ·⟩`. -/
theorem cast_fin_symm_val {n m : Nat} (e : m = n) (i : Fin n) :
    (cast (Eq.symm (congrArg Fin e)) i).val = i.val := by
  cases e
  rfl

/-- Casting a `Fin n` along `congrArg Fin e` (the positive direction) preserves the
index's `Nat` value — the bare-`Fin` companion to `cast_fin_symm_val`, for casts that
appear without the `.symm` (e.g. the index of a `concat`-result read back at `Fin n`). -/
theorem cast_fin_val {n m : Nat} (e : n = m) (i : Fin n) :
    (cast (congrArg Fin e) i).val = i.val := by
  cases e
  rfl

/-- The full-index form of `cast_fin_symm_val`: casting a `Fin n` along
`Eq.symm (congrArg Fin e)` (for `e : m = n`) yields the *same index* re-wrapped with
a re-proved bound. This is what `rw`/`simp` need to reduce an `if h : ↑(cast … i) < …`
scrutinee to `↑i < …`; the `.val`-only form is insufficient because the scrutinee is a
full `Fin`, not a projection. -/
theorem cast_fin_symm {n m : Nat} (e : m = n) (i : Fin n) :
    cast (Eq.symm (congrArg Fin e)) i = ⟨i.val, by
      have h : i.val < m := by omega
      exact h⟩ := by
  cases e
  rfl

/-- Associativity of `concat` over `+`-indexed byte strings, transported by the
`+` reassociation `Nat.add_assoc`. This is the clean, `Nat.sub`-free content of the
`seq`-law reassociation (`prepend_assoc`); every subsequent lemma closes by
`cast`-transporting through it. -/
theorem concat_assoc {a b c : Nat} (s₁ : Bytes a) (s₂ : Bytes b) (s₃ : Bytes c) :
    concat s₁ (concat s₂ s₃) = cast (congrArg Bytes (Nat.add_assoc a b c)) (concat (concat s₁ s₂) s₃) := by
  apply Bytes.ext
  intro i
  unfold concat
  rw [cast_bytes_val' (e := Nat.add_assoc a b c)]
  simp
  by_cases h1 : i.val < a
  · have h4 : i.val < a + b := by omega
    simp [h1, h4]
  · by_cases h3 : i.val - a < b
    · have h4 : i.val < a + b := by omega
      simp [h1, h3, h4]
    · have h5 : ¬ i.val < a + b := by omega
      simp [h1, h3, h5]
      apply congrArg s₃
      apply Fin.ext
      exact Nat.sub_sub i.val a b

/-- `splice` reduces pointwise: `splice hm s₁ s₂ i` is `concat s₁ s₂` at the
`Fin`-cast of `i` from `Fin n` back to `Fin (m + (n - m))`. This is the one
pointwise lemma every `seq`/`byte` law rewrites through. -/
theorem splice_apply {n m : Nat} (hm : m ≤ n) (s₁ : Bytes m) (s₂ : Bytes (n - m))
    (i : Fin n) :
    splice hm s₁ s₂ i = concat s₁ s₂ (cast (congrArg Fin (splice_add hm)).symm i) := by
  let hfin : Fin (m + (n - m)) = Fin n :=
    congrArg Fin (splice_add hm)
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

/-- The `Nat`-sub arithmetic for the `decodeRepeat_spec` cons-case reassociation:
`(n - m₂) - (n - m₁) = m₁ - m₂` under `m₂ ≤ m₁ ≤ n`. Named so the suffix length cast
of the `relRepeat_cons` witness is a clean constant. `[propext, Quot.sound]`-only. -/
theorem sub_sub_sub (n m₁ m₂ : Nat) (hm₁ : m₁ ≤ n) (hm₂ : m₂ ≤ m₁) :
    (n - m₂) - (n - m₁) = m₁ - m₂ := by
  omega

/-- Casting a whole `splice` commutes past its prefix: `cast (congrArg Bytes e) (splice hm s₁ s₂)`
(for `e : n = n'`) equals `splice (m ≤ n') s₁ (cast (n' - m = n - m) s₂)` — the prefix `s₁` is
unchanged and the suffix `s₂` is length-transported along `n' - m = n - m`. This is the
`concat_eq_splice`-companion that closes the `decode_spec` `seq`-case forwarding, where the
`Rel_seq` witness's suffix length `n - t₂.remaining` differs from the encoder's `(n - t₁) + (t₁ - t₂)`
by the `sub_sub_add` cast. `[propext, Quot.sound]`-only. -/
theorem splice_cast_commute {n n' m : Nat} (e : n = n') (hm : m ≤ n)
    (s₁ : Bytes m) (s₂ : Bytes (n - m)) :
    cast (congrArg Bytes e) (splice hm s₁ s₂) =
      splice (by omega : m ≤ n') s₁ (cast (congrArg Bytes (by omega : n - m = n' - m)) s₂) := by
  subst e
  simp

/-- The length cast of `splice_splice_assoc`: under `k ≤ m ≤ n`,
`(m - k) + (n - m) = n - k`. Named so the cast argument of
`splice_splice_assoc` is a clean constant (not an inline `omega` proof) that
`rw`/`simp` can match when closing the `decode_spec` `seq` backward / `decodeRepeat_spec`
re-parenthesization. `[propext, Quot.sound]`-only. -/
theorem splice_splice_len {n m k : Nat} (hm : m ≤ n) (hk : k ≤ m) :
    (m - k) + (n - m) = n - k := by
  omega

/-- Three-way associativity of `splice`: `splice hm (splice hk s₁ s₂) s₃` re-parenthesizes
into `splice (Nat.le_trans hk hm) s₁ (cast … (splice (Nat.sub_le_sub_right hm k) s₂ s₃))` —
the split at `m` then at `k ≤ m` becomes the split at `k` then at `m - k`. This is the
`n - m`-indexed sub analogue of `concat_assoc`, and is what `decode_spec`'s `seq`
completeness and `decodeRepeat_spec`'s cons case use to re-parenthesize a
`r.prepend (splice hm s₁ s₂)` decomposition into a first-step `s₁` prefix plus the
recursive `(s₂ ++ r)` remainder. `[propext, Quot.sound]`-only. -/
theorem splice_splice_assoc {n m k : Nat} (hm : m ≤ n) (hk : k ≤ m)
    (s₁ : Bytes k) (s₂ : Bytes (m - k)) (s₃ : Bytes (n - m)) :
    splice hm (splice hk s₁ s₂) s₃ =
      splice (Nat.le_trans hk hm)
        s₁ (cast (congrArg Bytes (splice_splice_len hm hk))
          (concat s₂ s₃)) := by
  apply Bytes.ext
  intro i
  rw [splice_apply]
  rw [splice_apply]
  rw [cast_fin_symm]
  · rw [cast_fin_symm]
    · unfold concat
      dsimp
      by_cases h1 : i.val < k
      · have h1m : i.val < m := Nat.lt_of_lt_of_le h1 hk
        simp [h1, h1m]
        rw [splice_apply]
        unfold concat
        rw [cast_fin_symm (e := splice_add hk) (i := ⟨i.val, h1m⟩)]
        simp [h1]
      · have hgek : k ≤ i.val := Nat.le_of_not_gt h1
        by_cases h2 : i.val < m
        · have h2' : i.val - k < m - k := by omega
          simp [h1, h2]
          rw [splice_apply]
          rw [cast_fin_symm (e := splice_add hk) (i := ⟨i.val, h2⟩)]
          rw [cast_bytes_val' (e := splice_splice_len hm hk)]
          unfold concat
          simp [h1, h2']
        · have hgenm : m ≤ i.val := Nat.le_of_not_gt h2
          have hnot : ¬ i.val - k < m - k := by omega
          simp [h1, h2]
          rw [cast_bytes_val' (e := splice_splice_len hm hk)]
          dsimp
          simp [hnot]
          congr 1
          apply Fin.ext
          calc
            i.val - m = i.val - (k + (m - k)) := by omega
            _ = i.val - k - (m - k) := by rw [Nat.sub_sub]

    · omega
  · omega


/-- Reconstruct a `Bytes n` from a consumed prefix and a suffix: `t.prepend s₀`
is `s₀` followed by the remaining bytes of `t`. The length cast
`n - (n - t.remaining) = t.remaining` is discharged by `t.hle`. The `decode_spec`
law is stated as ``(x, t) ∈ decode d s ↔ ∃ s₀, t.prepend s₀ = s ∧ Rel d x s₀``. -/
def Suffix.prepend {n : Nat} (t : Suffix n) (s₀ : Bytes (n - t.remaining)) : Bytes n :=
  splice (Nat.sub_le n t.remaining) s₀
    (cast (congrArg Bytes (Nat.sub_sub_self t.hle).symm) t.bytes)

/-- `Suffix.prepend` reduces pointwise: `t.prepend s₀ i` is `concat s₀ t.bytes` at
a `Fin`-cast of `i` (with `t.bytes` transported across
`n - (n - t.remaining) = t.remaining`). This is the single lemma that makes
`decode_spec`'s `seq`/`byte` cases close: both sides of `t.prepend s₀ = s` become
`concat` reads, so the laws reduce to `concat` arithmetic. -/
@[simp] theorem prepend_apply {n : Nat} (t : Suffix n) (s₀ : Bytes (n - t.remaining))
    (i : Fin n) :
    t.prepend s₀ i = concat s₀ (cast (congrArg Bytes (Nat.sub_sub_self t.hle).symm) t.bytes)
      (cast (congrArg Fin (splice_add (Nat.sub_le n t.remaining))).symm i) := by
  unfold Suffix.prepend
  rw [splice_apply]

/-- Cast at a byte-string length is insensitive to *which* proof of the length
equality is used (`Nat` equalities are subsingletons). This is what lets every
`seq`/`byte` law transport between `concat`/`splice`/`prepend` trees whose casts
use different (but propositionally equal) `Nat`-sub/`Nat`-add proofs. -/
theorem cast_bytes_irrel {n m : Nat} (e₁ e₂ : n = m) (s : Bytes n) :
    cast (congrArg Bytes e₁) s = cast (congrArg Bytes e₂) s := by
  rw [Nat.eq_irrel e₁ e₂]

/-- Dropping the first `m` bytes of a `splice hm s₁ s₂` recovers the suffix `s₂`. This
is the ``concat``/``splice`` counterpart of the old ``drop_append`` fact, used by
`decode_spec`'s `seq` completeness (the ``s₂ ++ r`` intermediary). `[propext, Quot.sound]`-only. -/
theorem bdrop_splice {n m : Nat} (hm : m ≤ n) (s₁ : Bytes m) (s₂ : Bytes (n - m)) :
    bdrop m (splice hm s₁ s₂) = s₂ := by
  apply Bytes.ext
  intro i
  unfold bdrop
  rw [splice_apply]
  unfold concat
  rw [cast_fin_symm]
  · dsimp
    by_cases hlt : i.val + m < m
    · omega
    · simp [hlt]
  · omega

/-- Reading the *prefix* region of a `splice hm s₁ s₂` recovers the prefix `s₁`:
for any `i : Fin n` with `i.val < m`, `splice hm s₁ s₂ i = s₁ ⟨i.val, ·⟩`. This is
`bdrop_splice`'s dual (the ``drop``-of-``splice`` recovers the suffix; this recovers
the *prefix*) — the length-indexed spelling of the old `take (m) (s₁ ++ s₂) = s₁`.
It is the transport `decodeArray_unambiguous_value` needs to show two same-length
decoded prefixes of one input agree. `[propext, Quot.sound]`-only. -/
theorem splice_prefix_read {n m : Nat} (hm : m ≤ n) (s₁ : Bytes m) (s₂ : Bytes (n - m))
    (i : Fin n) (hi : i.val < m) :
    splice hm s₁ s₂ i = s₁ ⟨i.val, hi⟩ := by
  rw [splice_apply]
  unfold concat
  rw [cast_fin_symm]
  · dsimp
    simp [hi]
  · exact splice_add hm

/-- Reading the *prefix* region of a `t.prepend s₀` recovers the prefix `s₀`: for
`i : Fin n` with `i.val < n - t.remaining`, `(t.prepend s₀) i = s₀ ⟨i.val, ·⟩`. This
re-states `splice_prefix_read` at the `Suffix.prepend` level (`prepend` is the `splice`
with prefix `s₀` and suffix `cast … t.bytes`). `[propext, Quot.sound]`-only. -/
theorem prepend_prefix_read {n : Nat} (t : Suffix n) (s₀ : Bytes (n - t.remaining))
    (i : Fin n) (hi : i.val < n - t.remaining) :
    t.prepend s₀ i = s₀ ⟨i.val, hi⟩ := by
  unfold Suffix.prepend
  exact splice_prefix_read (Nat.sub_le n t.remaining) s₀ (cast (congrArg Bytes (Nat.sub_sub_self t.hle).symm) t.bytes) i hi

/-- `Suffix.prepend` is injective in its prefix argument: two prefixes that
`prepend` (onto the *same* suffix `t`) to equal whole strings are themselves equal.
This is the "take the consumed prefix" step that, once `t₁ = t₂` is known, turns
`t.prepend s₀₁ = t.prepend s₀₂` into `s₀₁ = s₀₂` — the same-type, cast-free half of
`decodeArray_unambiguous_value`. `[propext, Quot.sound]`-only. -/
theorem prepend_prefix_eq {n : Nat} (t : Suffix n) (s₀₁ s₀₂ : Bytes (n - t.remaining)) :
    t.prepend s₀₁ = t.prepend s₀₂ → s₀₁ = s₀₂ := by
  intro h
  apply Bytes.ext
  intro i
  have hr := congrFun h ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.sub_le n t.remaining)⟩
  rw [prepend_prefix_read t s₀₁ ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.sub_le n t.remaining)⟩ i.isLt] at hr
  rw [prepend_prefix_read t s₀₂ ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.sub_le n t.remaining)⟩ i.isLt] at hr
  exact hr

/-- Reconstructing a `Bytes n` from a `splice hm s₁ s₂` split by dropping the prefix and
re-prepending it gives back the originals: `s = (Suffix.drop m s).prepend s₁` (with `s₁`
transported to the `n - (n - m)` length `Suffix.prepend` expects). Used by `decode_spec`'s
`seq` completeness. `[propext, Quot.sound]`-only. -/
theorem prepend_eq_of_eq_splice {n m : Nat} (s : Bytes n) (hm : m ≤ n)
    (s₁ : Bytes m) (s₂ : Bytes (n - m)) (h : s = splice hm s₁ s₂) :
    s = (Suffix.drop m s).prepend (cast (congrArg Bytes (Nat.sub_sub_self hm).symm) s₁) := by
  rw [h]
  unfold Suffix.drop
  dsimp
  apply Bytes.ext
  intro i
  rw [splice_apply]
  rw [prepend_apply]
  unfold concat
  rw [cast_fin_symm]
  · rw [cast_fin_symm]
    · dsimp
      simp [Nat.sub_sub_self hm, bdrop_splice hm s₁ s₂, cast_bytes_val']
    · omega
  · omega

/-- Reconstruction for `decode_spec`'s `seq` backward direction: given a
`r.prepend (splice hm s₁ s₂)` reassembly (a `r`-suffix over a `splice` of `s₁` then
`s₂`), dropping the first `m` bytes (the `s₁` part) and re-prepending `s₁` recovers
the whole: `r.prepend (splice hm s₁ s₂) = (Suffix.drop m (r.prepend (splice hm s₁ s₂))).prepend
(cast … s₁)`. This is the `s₁`-prefix factorization the backward case of `decode_spec`
`seq` needs to obtain `(x.1, Suffix.drop m s) ∈ decode d₁ s` from `Rel d₁ x.1 s₁`;
it chains `splice_splice_assoc` (to re-parenthesize into `s₁ ++ (s₂ ++ r.bytes)`) with
`prepend_eq_of_eq_splice` (to reconstruct from the drop). `[propext, Quot.sound]`-only. -/
theorem prepend_drop_of_prepend_splice {n : Nat} (r : Suffix n) (m : Nat)
    (hm : m ≤ n - r.remaining) (s₁ : Bytes m) (s₂ : Bytes ((n - r.remaining) - m)) :
    r.prepend (splice hm s₁ s₂) =
      (Suffix.drop m (r.prepend (splice hm s₁ s₂))).prepend
        (cast (congrArg Bytes (Nat.sub_sub_self (Nat.le_trans hm (Nat.sub_le n r.remaining))).symm) s₁) := by
  have hrle : r.remaining ≤ n := r.hle
  unfold Suffix.prepend
  exact prepend_eq_of_eq_splice (splice (Nat.sub_le n r.remaining) (splice hm s₁ s₂) (cast (congrArg Bytes (Nat.sub_sub_self hrle).symm) r.bytes)) (Nat.le_trans hm (Nat.sub_le n r.remaining)) s₁ _ (by rw [splice_splice_assoc (Nat.sub_le n r.remaining) hm s₁ s₂ (cast (congrArg Bytes (Nat.sub_sub_self hrle).symm) r.bytes)])

/-- The length cast of `bdrop_prepend_splice`: under `rem ≤ n` and `m ≤ n - rem`,
`(n - rem) - m + rem = n - m`. Named so the cast argument of
`bdrop_prepend_splice` is a clean constant (not an inline `omega` proof) that
`rw`/`simp` can match when closing the `decode_spec` `seq` backward / `decodeRepeat_spec`
re-parenthesization. `[propext, Quot.sound]`-only. -/
theorem bdrop_prepend_splice_len {n rem m : Nat} (hrem : rem ≤ n) (hm : m ≤ n - rem) :
    (n - rem) - m + rem = n - m := by
  omega

/-- Dropping the first `m` bytes of `r.prepend (splice hm s₁ s₂)` (a `r`-suffixed
re-assembly whose consumed region is itself a `splice` of `s₁` then `s₂`) recovers
`s₂ ++ r.bytes` — the ``concat`` of the inner suffix `s₂` with the outer suffix
`r.bytes`, up to the length cast `(n - r.remaining) - m + r.remaining = n - m`. This
is the `decode_spec` `seq`-backward / `decodeRepeat_spec` helper: it re-parenthesizes
a `r.prepend (splice hm s₁ s₂)` into `s₁` followed by `s₂ ++ r.bytes`, giving the
first-step `s₁` prefix and the recursive `s₂ ++ r.bytes` remainder. `[propext, Quot.sound]`-only. -/
theorem bdrop_prepend_splice {n : Nat} (r : Suffix n) (m : Nat)
    (hm : m ≤ n - r.remaining) (s₁ : Bytes m) (s₂ : Bytes ((n - r.remaining) - m)) :
    bdrop m (r.prepend (splice hm s₁ s₂)) =
      cast (congrArg Bytes (bdrop_prepend_splice_len r.hle hm))
        (concat s₂ r.bytes) := by
  have hrle : r.remaining ≤ n := r.hle
  apply Bytes.ext
  intro i
  unfold bdrop
  rw [prepend_apply]
  unfold concat
  rw [cast_fin_symm]
  · dsimp
    rw [cast_bytes_val' (e := bdrop_prepend_splice_len hrle hm)]
    unfold concat at *
    by_cases h1 : i.val < (n - r.remaining) - m
    · have hlt : i.val + m < n - r.remaining := by omega
      simp [h1, hlt]
      rw [splice_apply]
      unfold concat
      rw [cast_fin_symm]
      · dsimp
        have hnot : ¬ i.val + m < m := by omega
        simp [hnot]
      · omega
    · have hnot_outer : ¬ i.val + m < n - r.remaining := by omega
      simp [h1, hnot_outer]
      rw [cast_bytes_val_symm (e := Nat.sub_sub_self hrle)]
      congr 1
      apply Fin.ext
      change (↑i + m - (n - r.remaining)) = (↑i - (n - r.remaining - m))
      omega
  · omega

/-- The suffix length cast of `bdrop_prepend_splice_eq_splice`: under `rem ≤ n` and
`m ≤ n - rem`, `n - m - ((n - rem) - m) = rem`. Named so the suffix cast of
`bdrop_prepend_splice_eq_splice` is a clean constant. `[propext, Quot.sound]`-only. -/
theorem bdrop_prepend_splice_snd_len {n rem m : Nat} (hrem : rem ≤ n) (hm : m ≤ n - rem) :
    n - m - ((n - rem) - m) = rem := by
  omega

/-- The `concat`-to-`splice` re-parenthesization of `bdrop_prepend_splice`: casting
`concat s₂ r.bytes` along `(n - rem) - m + rem = n - m` equals the `splice` of `s₂`
with the length-transported `r.bytes` suffix. This is the `concat_eq_splice` fact
specialized to the `bdrop_prepend_splice` length, with both casts named so `rw`/`simp`
can match them when closing the `decode_spec` `seq` backward / `decodeRepeat_spec`
second-step reconstruction. `[propext, Quot.sound]`-only. -/
theorem cast_concat_eq_splice {n rem m : Nat} (hrem : rem ≤ n) (hm : m ≤ n - rem)
    (s₂ : Bytes ((n - rem) - m)) (rbytes : Bytes rem) :
    cast (congrArg Bytes (bdrop_prepend_splice_len hrem hm)) (concat s₂ rbytes) =
      splice (Nat.sub_le_sub_right (Nat.sub_le n rem) m) s₂
        (cast (congrArg Bytes (bdrop_prepend_splice_snd_len hrem hm).symm) rbytes) := by
  apply Bytes.ext
  intro i
  rw [cast_bytes_val' (e := bdrop_prepend_splice_len hrem hm)]
  rw [splice_apply]
  unfold concat
  rw [cast_fin_symm]
  · dsimp
    by_cases hlt : i.val < (n - rem) - m
    · simp [hlt]
    · have hge : (n - rem) - m ≤ i.val := Nat.le_of_not_gt hlt
      simp [hlt]
      rw [cast_bytes_val_symm (e := bdrop_prepend_splice_snd_len hrem hm)]
  · omega

/-- Dropping the first `m` bytes of `r.prepend (splice hm s₁ s₂)` recovers the inner
suffix `s₂` followed by the outer suffix `r.bytes`, re-parenthesized as a `splice` (the
`concat_eq_splice` reading of `bdrop_prepend_splice`):
`bdrop m (r.prepend (splice hm s₁ s₂)) = splice (… : (n - r.remaining) - m ≤ n - m) s₂
(cast … r.bytes)`. This is the second-step reconstruction the `decode_spec` `seq`
backward / `decodeRepeat_spec` need to obtain `(x.2, Suffix.drop L (bdrop m s)) ∈
decode d₂ (bdrop m s)` from `Rel d₂ x.2 s₂`. `[propext, Quot.sound]`-only. -/
theorem bdrop_prepend_splice_eq_splice {n : Nat} (r : Suffix n) (m : Nat)
    (hm : m ≤ n - r.remaining) (s₁ : Bytes m) (s₂ : Bytes ((n - r.remaining) - m)) :
    bdrop m (r.prepend (splice hm s₁ s₂)) =
      splice (Nat.sub_le_sub_right (Nat.sub_le n r.remaining) m) s₂
        (cast (congrArg Bytes (bdrop_prepend_splice_snd_len r.hle hm).symm) r.bytes) := by
  rw [bdrop_prepend_splice r m hm s₁ s₂]
  exact cast_concat_eq_splice r.hle hm s₂ r.bytes

/-- Casting `concat s₁ s₂` (length `(n - t) + (t - r)`) along `sub_sub_add n t r`
equals the `splice` of `s₁` with the length-transported `s₂` suffix (length
`t - r = (n - r) - (n - t)` via `sub_sub_sub`). This is the `relRepeat_cons`
witness re-parenthesization for `decodeRepeat_spec`'s cons case: it turns the
`concat s₁ s₂` decoded prefix into the first-step `s₁` and recursive `s₂` split. `[propext, Quot.sound]`-only. -/
theorem cast_concat_splice_sub {n t r : Nat} (ht : t ≤ n) (hr : r ≤ t)
    (s₁ : Bytes (n - t)) (s₂ : Bytes (t - r)) :
    cast (congrArg Bytes (sub_sub_add n t r ht hr)) (concat s₁ s₂) =
      splice (Nat.sub_le_sub_left hr n) s₁
        (cast (congrArg Bytes (sub_sub_sub n t r ht hr).symm) s₂) := by
  apply Bytes.ext
  intro i
  rw [cast_bytes_val' (e := sub_sub_add n t r ht hr)]
  rw [splice_apply]
  unfold concat
  rw [cast_fin_symm]
  · dsimp
    by_cases h1 : i.val < n - t
    · simp [h1]
    · have hge : n - t ≤ i.val := Nat.le_of_not_gt h1
      simp [h1]
      rw [cast_bytes_val' (e := (sub_sub_sub n t r ht hr).symm)]
  · omega

/-- Dropping the whole consumed prefix `n - r.remaining` of `r.prepend s₀` recovers
`r.bytes` (transported across `n - (n - r.remaining) = r.remaining`). This is the
`bdrop`-of-`prepend` reconstruction (the `s₂ ++ r.bytes` tail read), used by
`bdrop_drop_eq_bytes` to close the `decode_spec` `seq` backward third goal. `[propext, Quot.sound]`-only. -/
theorem bdrop_prepend {n : Nat} (r : Suffix n) (s₀ : Bytes (n - r.remaining)) :
    bdrop (n - r.remaining) (r.prepend s₀) =
      cast (congrArg Bytes (Nat.sub_sub_self r.hle).symm) r.bytes := by
  apply Bytes.ext
  intro i
  unfold bdrop
  rw [prepend_apply]
  unfold concat
  rw [cast_fin_symm]
  · dsimp
    have hnot : ¬ ↑i + (n - r.remaining) < n - r.remaining := by omega
    simp [hnot]
  · omega

/-- The inverse of `bdrop_prepend`: dropping the whole consumed prefix
`n - r.remaining` of `r.prepend s₀` recovers the suffix `r` itself (up to the
`Suffix.ext` re-indexing). Used by `decode_spec`'s `byte` backward case to close
`r = Suffix.drop 1 s` from `s = r.prepend s₀`. `[propext, Quot.sound]`-only. -/
theorem drop_prepend {n : Nat} (r : Suffix n) (s₀ : Bytes (n - r.remaining)) :
    Suffix.drop (n - r.remaining) (r.prepend s₀) = r := by
  refine Suffix.ext (t₁ := Suffix.drop (n - r.remaining) (r.prepend s₀)) (t₂ := r) ?_ ?_
  · dsimp [Suffix.drop]
    exact Nat.sub_sub_self r.hle
  · dsimp [Suffix.drop]
    rw [bdrop_prepend r s₀]
    change cast (congrArg Bytes (Nat.sub_sub_self r.hle)) (cast (congrArg Bytes (Nat.sub_sub_self r.hle).symm) r.bytes) = r.bytes
    simp

/-- Dropping zero bytes is the identity on byte strings (`bdrop 0 s = s`). `[propext, Quot.sound]`-only. -/
theorem bdrop_zero {n : Nat} (s : Bytes n) : bdrop 0 s = s := by
  apply Bytes.ext
  intro i
  dsimp [bdrop]

/-- A suffix with all `n` bytes remaining is the identity suffix (`Suffix.drop 0 s =
Suffix.id n s`). Used by `decodeRepeat_spec`'s nil case to close `r = Suffix.id n s`
from `n - r.remaining = 0`. `[propext, Quot.sound]`-only. -/
theorem drop_zero_eq_id {n : Nat} (s : Bytes n) : Suffix.drop 0 s = Suffix.id n s := by
  refine Suffix.ext (t₁ := Suffix.drop 0 s) (t₂ := Suffix.id n s) ?_ ?_
  · dsimp [Suffix.drop, Suffix.id]
  · dsimp [Suffix.drop, Suffix.id]
    rw [bdrop_zero s]
    change cast (congrArg Bytes (Nat.sub_zero n)) s = s
    simp

/-- Dropping the inner suffix `s₂` (of length `(n - r.remaining) - m`) and then the
outer consumed prefix `m` of `r.prepend (splice hm s₁ s₂)` recovers `r.bytes`,
transported across `n - m - ((n - r.remaining) - m) = r.remaining`. This is the
`t₂.bytes = r.bytes` field equality the `decode_spec` `seq` backward third goal
(`r = Suffix.trans t₁ t₂`) needs. `[propext, Quot.sound]`-only. -/
theorem bdrop_drop_eq_bytes {n : Nat} (r : Suffix n) (m : Nat)
    (hm : m ≤ n - r.remaining) (s₁ : Bytes m) (s₂ : Bytes ((n - r.remaining) - m)) :
    bdrop ((n - r.remaining) - m) (bdrop m (r.prepend (splice hm s₁ s₂))) =
      cast (congrArg Bytes (bdrop_prepend_splice_snd_len r.hle hm).symm) r.bytes := by
  have hrle : r.remaining ≤ n := r.hle
  apply Bytes.ext
  intro i
  unfold bdrop
  rw [prepend_apply]
  unfold concat
  rw [cast_fin_symm]
  · dsimp
    have hsum : m + ((n - r.remaining) - m) = n - r.remaining := by omega
    have hnot : ¬ (↑i + ((n - r.remaining) - m) + m) < n - r.remaining := by omega
    simp [hnot]
    rw [cast_bytes_val_symm (e := Nat.sub_sub_self hrle)]
    dsimp
    rw [cast_bytes_val' (e := (bdrop_prepend_splice_snd_len hrle hm).symm)]
    congr 1
    apply Fin.ext
    dsimp
    omega
  · omega

/-- Associativity of `Suffix.prepend` over two successive suffixes: prepending
`s₁` then `s₂` to `t₂.bytes` (and threading the `≤` witnesses to a suffix of `n`)
is the same as prepending the concatenation `s₁ ++ s₂` to `t₁`, provided the
middle region reconstructs `t₁.bytes` (`t₂.prepend s₂ = t₁.bytes`). This is the
`seq`-case reassociation the `decode_spec` law needs (see `Sound.decode_spec`);
it is the `splice`/`prepend` analogue of `List.append_assoc` transported through
the length-index casts. Without the `h` hypothesis it is false (the two sides
read `t₂.bytes` and `t₁.bytes` respectively in the deep-suffix region).

`[propext, Quot.sound]`-only. -/
theorem prepend_assoc {n : Nat} (t₁ : Suffix n) (t₂ : Suffix t₁.remaining)
    (s₁ : Bytes (n - t₁.remaining)) (s₂ : Bytes (t₁.remaining - t₂.remaining))
    (h : t₂.prepend s₂ = t₁.bytes) :
    (Suffix.trans t₁ t₂).prepend
      (cast (congrArg Bytes (sub_sub_add n t₁.remaining t₂.remaining t₁.hle t₂.hle))
        (concat s₁ s₂))
      = t₁.prepend s₁ := by
  apply Bytes.ext
  intro i
  unfold Suffix.trans Suffix.prepend
  dsimp
  rw [splice_apply]
  rw [splice_apply]
  unfold concat
  rw [cast_fin_symm]
  · rw [cast_fin_symm]
    · by_cases hlt : i.val < n - t₁.remaining
      · simp [hlt, cast_bytes_val', sub_sub_add n t₁.remaining t₂.remaining t₁.hle t₂.hle]
        have hlt2 : i.val < n - t₂.remaining :=
          Nat.lt_of_lt_of_le hlt (Nat.sub_le_sub_left t₂.hle n)
        simp [hlt2]
      · rw [← h]
        simp [hlt]
        rw [cast_bytes_val_symm]
        · rw [prepend_apply]
          unfold concat
          rw [cast_fin_symm]
          · dsimp
            by_cases hlt2 : i.val - (n - t₁.remaining) < t₁.remaining - t₂.remaining
            · have hlt2a : i.val < (t₁.remaining - t₂.remaining) + (n - t₁.remaining) := by
                omega
              have hlt2' : i.val < n - t₂.remaining := by
                rw [Nat.add_comm] at hlt2a
                rw [sub_sub_add n t₁.remaining t₂.remaining t₁.hle t₂.hle] at hlt2a
                exact hlt2a
              simp [hlt2, hlt, hlt2', cast_bytes_val',
                sub_sub_add n t₁.remaining t₂.remaining t₁.hle t₂.hle]
            · have hnot : ¬ i.val < n - t₂.remaining := by
                have hsub := sub_sub_add n t₁.remaining t₂.remaining t₁.hle t₂.hle
                have hle1 : n - t₁.remaining ≤ i.val := Nat.le_of_not_gt hlt
                omega
              simp [hlt2, hnot]
              rw [cast_bytes_val_symm (e := Nat.sub_sub_self (Nat.le_trans t₂.hle t₁.hle))]
              rw [cast_bytes_val_symm (e := Nat.sub_sub_self t₂.hle)]
              congr 1
              apply Fin.ext
              change i.val - (n - t₂.remaining) = i.val - (n - t₁.remaining) - (t₁.remaining - t₂.remaining)
              rw [Nat.sub_sub]
              rw [sub_sub_add n t₁.remaining t₂.remaining t₁.hle t₂.hle]
          · exact splice_add (Nat.sub_le t₁.remaining t₂.remaining)
        · exact Nat.sub_sub_self t₁.hle
    · exact splice_add (Nat.sub_le n t₁.remaining)
  · exact splice_add (Nat.sub_le n t₂.remaining)

/-- The `byte`-case analogue of `prepend_assoc`: dropping the first byte of a
non-empty `s : Bytes (k + 1)`, prepending a single byte, recovers `s`. This is
the reconstruction `decode_spec`'s `byte` case needs: the decoder returns
`(s ⟨0, h⟩, Suffix.drop 1 s)`, and re-assembling the dropped prefix with
`Suffix.prepend` gives back the whole input. `[propext, Quot.sound]`-only. -/
theorem prepend_single_bdrop {k : Nat} (s : Bytes (k + 1)) :
    (Suffix.drop 1 s).prepend
      (cast (congrArg Bytes (by omega : 1 = (k + 1) - k)) (single (s ⟨0, Nat.zero_lt_succ k⟩))) = s := by
  apply Bytes.ext
  intro i
  unfold Suffix.drop
  rw [prepend_apply]
  dsimp
  unfold concat
  have hk : k + 1 - k = 1 := by omega
  rw [cast_fin_symm]
  · dsimp
    simp only [hk]
    by_cases h : i.val < 1
    · have h0 : i.val = 0 := by omega
      simp [h0, cast_bytes_val']
      exact congrArg s (Fin.ext (by simp [h0]))
    · have hge : 1 ≤ i.val := Nat.le_of_not_gt h
      simp [h, bdrop]
      exact congrArg s (Fin.ext (by dsimp; omega))
  · omega

/-- `byte` relates a single byte `x` to any length-`1` byte string obtained by
length-transporting `single x`. This is the `Rel_byte` witness of `decode_spec`'s
`byte` forward case (the decoder's `(s ⟨0, ·⟩, Suffix.drop 1 s)` result, whose
remainder length `n - (n-1)` is `1`). `[propext, Quot.sound]`-only. -/
theorem rel_byte_cast {n : Nat} (h : n = 1) (x : UInt8) :
    Rel Codec.byte x (cast (congrArg Bytes h.symm) (single x)) := by
  rw [Rel_byte]
  refine ⟨h, ?_⟩
  subst h
  rfl

/-- Reversing `byte`'s `Rel` transport: if a length-`n` byte string transports (along
`h : n = 1`) to `single x`, then the string itself is the length-transported `single x`.
This is the `decode_spec` `byte` backward case's `s₀ = single x` extraction. `[propext, Quot.sound]`-only. -/
theorem cast_bytes_eq_single {n : Nat} (h : n = 1) (s : Bytes n) (x : UInt8)
    (hs : h ▸ s = single x) : s = cast (congrArg Bytes h.symm) (single x) := by
  subst h
  simpa using hs

/-- The `n ≠ 0` spelling of `prepend_single_bdrop`: dropping the first byte of a
non-empty `s : Bytes n` and prepending the recovered single byte gives back `s`,
with the length cast `n - (n - 1) = 1` named via `Nat.sub_sub_self`. This is the
reconstruction `decode_spec`'s `byte` forward case needs. `[propext, Quot.sound]`-only. -/
theorem prepend_drop_single {n : Nat} (hn : n ≠ 0) (s : Bytes n) :
    (Suffix.drop 1 s).prepend
      (cast (congrArg Bytes (Nat.sub_sub_self (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn))).symm) (single (s ⟨0, Nat.pos_of_ne_zero hn⟩))) = s := by
  apply Bytes.ext
  intro i
  unfold Suffix.drop
  rw [prepend_apply]
  dsimp
  unfold concat
  have hn1 : n - (n - 1) = 1 := Nat.sub_sub_self (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn))
  rw [cast_fin_symm]
  · dsimp
    simp only [hn1]
    by_cases h : i.val < 1
    · have h0 : i.val = 0 := by omega
      simp [h0]
      rw [cast_bytes_val_symm (e := Nat.sub_sub_self (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn)))]
      exact congrArg s (Fin.ext (by simp [h0]))
    · have hge : 1 ≤ i.val := Nat.le_of_not_gt h
      simp [h]
      rw [cast_bytes_val_symm (e := Nat.sub_sub_self (Nat.sub_le n 1))]
      unfold bdrop
      congr 1
      apply Fin.ext
      dsimp
      omega
  · omega

/-- Prepending a prefix `s₀` to the empty suffix recovers the prefix (up to the
`n - 0 = n` length cast). This is the reconstruct for `bidir`'s empty-remainder case:
`(Suffix.empty n).prepend s₀ = cast (congrArg Bytes (Nat.sub_zero n)) s₀` — the
`decode_spec` completeness witness `s₀` (a `Bytes (n - 0)`) reassembles to the whole
input `s : Bytes n`. `[propext, Quot.sound]`-only. -/
theorem prepend_empty {n : Nat} (s₀ : Bytes (n - 0)) :
    (Suffix.empty n).prepend s₀ = cast (congrArg Bytes (Nat.sub_zero n)) s₀ := by
  apply Bytes.ext
  intro i
  unfold Suffix.prepend Suffix.empty
  rw [splice_apply]
  unfold concat
  rw [cast_fin_symm]
  · dsimp
    simp
  · omega

/-- Prepending a prefix `s : Bytes n` (transported to the `Bytes (n - 0)` length
`Suffix.prepend` asks for) to the empty suffix recovers `s` exactly. This is the
`bidir` forward witness: `(Suffix.empty n).prepend (cast (Nat.sub_zero n).symm s) = s`.
`[propext, Quot.sound]`-only. -/
theorem prepend_empty_eq {n : Nat} (s : Bytes n) :
    (Suffix.empty n).prepend (cast (congrArg Bytes (Nat.sub_zero n).symm) s) = s := by
  apply Bytes.ext
  intro i
  unfold Suffix.prepend Suffix.empty
  rw [splice_apply]
  unfold concat
  rw [cast_fin_symm]
  · dsimp
    simp
  · omega

/-- Prepending the empty byte string to the identity suffix recovers the input:
`(Suffix.id n s).prepend (cast (Nat.sub_self n).symm emptyBytes) = s`. This is the
`decode_spec` `pure`-case reconstruction: the decoder accepts `(x₀, Suffix.id n s)`
(consuming nothing), and re-assembling with `Suffix.prepend` — prefix `emptyBytes`, full
`s` remaining — gives back `s`. `[propext, Quot.sound]`-only. -/
theorem prepend_id {n : Nat} (s : Bytes n) :
    (Suffix.id n s).prepend (cast (congrArg Bytes (Nat.sub_self n).symm) emptyBytes) = s := by
  apply Bytes.ext
  intro i
  unfold Suffix.prepend Suffix.id
  rw [splice_apply]
  unfold concat
  rw [cast_fin_symm]
  · dsimp
    have h0 : n - n = 0 := Nat.sub_self n
    have hnot : ¬ i.val < n - n := by rw [h0]; exact Nat.not_lt_zero i.val
    simp
  · omega

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
