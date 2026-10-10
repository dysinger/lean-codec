/- Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later -/

import Codec.Codec

/-!
# The deterministic decoder

This file gives `decode`, the deterministic, single-result decoder:

    decode : Codec α → List UInt8 → Except DecodeError (α × List UInt8)

It is "return-the-rest": on success it returns the decoded value together with
the (possibly empty) remaining bytes; on failure it returns an error carrying
the remaining unconsumed bytes, from which the failure position is derived
structurally as `whole.length - remaining.length`.

There is no cursor, no backtracking, and no peeking; choice (`alt`) is
committed. This is a deliberate, documented departure from the paper's
nondeterministic list decoder (§4.1, §4.4): see the repository README.
-/

namespace Codec

/-- A decode failure, carrying the remaining unconsumed bytes. The position of
the failure (relative to the input `whole`) is `whole.length - remaining.length`. -/
structure DecodeError where
  /-- The bytes not yet consumed when the failure occurred. -/
  remaining : List UInt8
  deriving Repr

/-- The failure position of a decode error against a whole input: the number of
bytes already consumed. -/
def DecodeError.position (e : DecodeError) (whole : List UInt8) : Nat :=
  whole.length - e.remaining.length

/-- The deterministic decoder: one result plus remaining bytes, or a positioned error. -/
def decode {α : Type} (d : Codec α) (s : List UInt8) : Except DecodeError (α × List UInt8) :=
  match d with
  | Codec.iso i d =>
      match decode d s with
      | .error e => .error e
      | .ok (a, s') =>
          match i.apply a with
          | some x => .ok (x, s')
          | none => .error { remaining := s' }
  | Codec.seq d₁ d₂ =>
      match decode d₁ s with
      | .error e => .error e
      | .ok (x, s₁) =>
          match decode d₂ s₁ with
          | .error e => .error e
          | .ok (y, s₂) => .ok ((x, y), s₂)
  | Codec.alt d₁ d₂ =>
      match decode d₁ s with
      | .ok r => .ok r
      | .error _ => decode d₂ s
  | Codec.empty => .error { remaining := s }
  | Codec.pure x => .ok (x, s)
  | Codec.byte =>
      match s with
      | [] => .error { remaining := s }
      | b :: rest => .ok (b, rest)

end Codec
