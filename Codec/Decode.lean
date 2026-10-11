/- Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later -/

import Codec.Codec

/-!
# The nondeterministic decoder

This file gives `decode`, the paper's list-monad decoder (§4.1):

    decode : Codec α → List UInt8 → List (α × List UInt8)

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
onto `List UInt8`, with `|` as list concatenation (unlimited backtracking). -/
def decode {α : Type} (d : Codec α) (s : List UInt8) : List (α × List UInt8) :=
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
def decodeRepeat {α : Type} (p : Codec α) (h : ConsumesByte p) (s : List UInt8) :
    List (List α × List UInt8) :=
  WellFounded.fix (InvImage.wf (fun s : List UInt8 => s.length) Nat.lt_wfRel.wf)
    (fun s ih =>
      ([], s) :: (decode p s).attach.flatMap fun a =>
        match a with
        | ⟨(x, s₁), _hmem⟩ => (ih s₁ (h x s₁ s _hmem)).map fun (xs, r) => (x :: xs, r))
    s

/-- The recursion equation for `decodeRepeat`: the empty result plus every
`cons` step on a strictly-shorter remainder. Derived from `WellFounded.fix_eq`. -/
theorem decodeRepeat_eq {α : Type} (p : Codec α) (h : ConsumesByte p) (s : List UInt8) :
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
def byteRepeat (s : List UInt8) : List (List UInt8 × List UInt8) :=
  decodeRepeat Codec.byte byte_consumesByte s

end Codec
