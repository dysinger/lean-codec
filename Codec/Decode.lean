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
unambiguity gate: `Rel (alt d₁ d₂) = Rel d₁ ∨ Rel d₂` and `decode (alt d₁ d₂) =
decode d₁ ++ decode d₂` agree by construction.

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

end Codec
