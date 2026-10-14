/- Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later -/

import Codec.Codec

/-!
# The nondeterministic decoder

This file gives `decode`, the paper's list-monad decoder (§4.1), over the
length-indexed byte string:

    decode : Codec α → {n : Nat} → Bytes n → List (α × Suffix n)

It returns *all* (value, remaining-bytes) pairs — a relation, not a single
result. Choice (`alt`) is the full backtracking union `decode d₁ s ++ decode d₂ s`,
exactly as in the paper. The remaining buffer is a `Suffix n`: a shorter
`Bytes m` (for some `m ≤ n`) together with the `≤` witness, never a `List` tail
whose length must be recomputed.

The paper notes (§4.4) that this proof-of-concept decoder has exponential
worst-case complexity and a space leak under unlimited backtracking; replacing it
with an efficient implementation of the *same* semantics is future work (not the
semantics of `decode`).
-/

namespace Codec

/-- The nondeterministic decoder: every `(value, remaining)` pair derivable from
the description against the input `s : Bytes n`. The remaining buffer is a
`Suffix n`. -/
def decode {α : Type} (d : Codec α) {n : Nat} (s : Bytes n) : List (α × Suffix n) :=
  match d with
  | Codec.iso i d =>
      (decode d s).filterMap fun (a, t) => (i.apply a).map fun x => (x, t)
  | Codec.seq d₁ d₂ =>
      (decode d₁ s).flatMap fun (x, t₁) =>
        (decode d₂ t₁.bytes).flatMap fun (y, t₂) => [((x, y), Suffix.trans t₁ t₂)]
  | Codec.alt d₁ d₂ => decode d₁ s ++ decode d₂ s
  | Codec.empty => []
  | Codec.pure x => [(x, Suffix.id n s)]
  | Codec.byte =>
      if h : n = 0 then []
      else [(s ⟨0, Nat.pos_of_ne_zero h⟩, Suffix.drop 1 s)]

/-- The **fused** decoder: a `flatMap`/`map`-fused re-staging of `decode` that does not
re-traverse the singleton result of a `seq` pair (the inner ``flatMap (…) [((x, y), t₂)]``
becomes a single ``map``). -/
def decodeFast {α : Type} (d : Codec α) {n : Nat} (s : Bytes n) : List (α × Suffix n) :=
  match d with
  | Codec.iso i d =>
      (decodeFast d s).filterMap fun (a, t) => (i.apply a).map fun x => (x, t)
  | Codec.seq d₁ d₂ =>
      (decodeFast d₁ s).flatMap fun (x, t₁) =>
        (decodeFast d₂ t₁.bytes).map fun (y, t₂) => ((x, y), Suffix.trans t₁ t₂)
  | Codec.alt d₁ d₂ => decodeFast d₁ s ++ decodeFast d₂ s
  | Codec.empty => []
  | Codec.pure x => [(x, Suffix.id n s)]
  | Codec.byte =>
      if h : n = 0 then []
      else [(s ⟨0, Nat.pos_of_ne_zero h⟩, Suffix.drop 1 s)]

/-- `decodeFast` equals `decode` for every description and input. Proved by induction
on `d`; the only non-trivial case is `seq`, where the fused `map` equals the spec's
`flatMap`-over-singleton via the list-fusion identity ``l.flatMap (fun a => [f a]) =
l.map f``. No `Classical.choice`; `[propext, Quot.sound]` only. -/
theorem decodeFast_eq {α : Type} (d : Codec α) :
    ∀ {n : Nat} (s : Bytes n), decodeFast d s = decode d s := by
  induction d with
  | iso i d ih =>
      intro n s
      simp [decodeFast, decode, ih]
  | seq d₁ d₂ ih₁ ih₂ =>
      intro n s
      simp [decodeFast, decode, ih₁, ih₂, List.map_eq_flatMap]
  | alt d₁ d₂ ih₁ ih₂ =>
      intro n s
      simp [decodeFast, decode, ih₁, ih₂]
  | empty =>
      intro n s
      simp [decodeFast, decode]
  | pure x =>
      intro n s
      simp [decodeFast, decode]
  | byte =>
      intro n s
      simp [decodeFast, decode]

/-! ## The repetition decoder (productive `many` as well-founded recursion) -/

/-- An executable mirror of `Productive`: every decoding step strictly shortens
the remaining buffer. Equivalent to `Productive` (see `Sound.productive_iff_consumesByte`);
this is the form the repetition decoder consumes as its well-foundedness witness. -/
def ConsumesByte {α : Type} (p : Codec α) : Prop :=
  ∀ x {n : Nat} (s : Bytes n) (t : Suffix n), (x, t) ∈ decode p s → t.remaining < n

/-- The productive repetition decoder: `decodeRepeat p h n s` enumerates exactly
the paper's `many p` results — the empty list leaving `s` unchanged, plus every
one-or-more prefix — by **well-founded recursion on `n`** (the remaining length).
The recursion is guarded by `h : ConsumesByte p`, the fact that each `decode p`
step strictly shortens the remaining string. Total and `#eval`-able for every
productive `p`. -/
def decodeRepeat {α : Type} (p : Codec α) (h : ConsumesByte p) (n : Nat) (s : Bytes n) :
    List (List α × Suffix n) :=
  (WellFounded.fix
    (InvImage.wf (fun ns : Sigma fun k => Bytes k => ns.1) Nat.lt_wfRel.wf)
    (fun (ns : Sigma fun k => Bytes k) (ih : (ns' : Sigma fun k => Bytes k) → ns'.1 < ns.1 → List (List α × Suffix ns'.1)) =>
      let ⟨n, s⟩ := ns
      ([], Suffix.id n s) :: (decode p s).attach.flatMap fun a =>
        match a with
        | ⟨(x, t), hmem⟩ =>
            (ih ⟨t.remaining, t.bytes⟩ (h x s t hmem)).map fun (xs, r) =>
              (x :: xs, Suffix.trans t r))
    ⟨n, s⟩)

/-- The recursion equation for `decodeRepeat`. Derived from `WellFounded.fix_eq`. -/
theorem decodeRepeat_eq {α : Type} (p : Codec α) (h : ConsumesByte p) (n : Nat) (s : Bytes n) :
    decodeRepeat p h n s =
      ([], Suffix.id n s) :: (decode p s).attach.flatMap fun a =>
        match a with
        | ⟨(x, t), _hmem⟩ =>
            (decodeRepeat p h t.remaining t.bytes).map fun (xs, r) =>
              (x :: xs, Suffix.trans t r) := by
  unfold decodeRepeat
  rw [WellFounded.fix_eq]

/-- The single-byte primitive is productive: decoding one byte always consumes
exactly one byte. This is the `ConsumesByte` witness that makes
`decodeRepeat Codec.byte _` total (and `#eval`-able); the general case is
`Sound.productive_iff_consumesByte`. -/
theorem byteConsumesByte : ConsumesByte Codec.byte := by
  intro x n s t hmem
  by_cases h : n = 0
  · simp [decode, h] at hmem
  · simp [decode, h] at hmem
    rcases hmem with ⟨hx, ht⟩
    subst t
    simp [Suffix.drop]
    omega

/-! ## The full-consumption repetition decoder

The §4.4 blow-up is the *all-prefix* enumeration: `decodeRepeat p h n s`
materializes every prefix. `decodeFull` is the same denotation restricted to the
single full-consumption result: it returns `some xs` for the full consumption
(empty remainder), `none` otherwise, without building every intermediate prefix. -/

/-- Thread the well-founded recursion over the `attach`-ed candidate `decode p s`
results, picking the first step `(x, t)` whose shorter-remainder recursion yields a
full consumption. -/
def decodeFullStep {α : Type} (p : Codec α) (h : ConsumesByte p)
    {n : Nat} (s : Bytes n)
    (ih : (m : Nat) → (s' : Bytes m) → m < n → Option (List α)) :
    List { pr : α × Suffix n // pr ∈ decode p s } → Option (List α)
  | [] => none
  | ⟨(x, t), hm⟩ :: rest =>
      match ih t.remaining t.bytes (h x s t hm) with
      | none => decodeFullStep p h s ih rest
      | some xs => some (x :: xs)

/-- The full-consumption repetition decoder: `decodeFull p h n s = some xs` exactly
when `xs` is a list that `many p` matches against the *whole* input (empty remaining
buffer, and the list must fully consume the input). Defined by `WellFounded.fix` on
`n`. -/
def decodeFull {α : Type} (p : Codec α) (h : ConsumesByte p) (n : Nat) (s : Bytes n) : Option (List α) :=
  (WellFounded.fix
    (InvImage.wf (fun ns : Sigma fun k => Bytes k => ns.1) Nat.lt_wfRel.wf)
    (fun (ns : Sigma fun k => Bytes k) (ih : (ns' : Sigma fun k => Bytes k) → ns'.1 < ns.1 → Option (List α)) =>
      match ns with
      | ⟨0, _s⟩ => some []
      | ⟨_k + 1, s⟩ => decodeFullStep p h s (fun m s' hm => ih ⟨m, s'⟩ hm) (decode p s).attach)
    ⟨n, s⟩)

/-- The empty input is fully consumed by the empty list. -/
theorem decodeFull_zero {α : Type} (p : Codec α) (h : ConsumesByte p) (s : Bytes 0) :
    decodeFull p h 0 s = some [] := by
  unfold decodeFull
  rw [WellFounded.fix_eq]

end Codec
