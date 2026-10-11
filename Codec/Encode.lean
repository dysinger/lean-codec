/- Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later -/

import Codec.Codec

/-!
# The partial encoder

This file gives `encode`, the partial encoder:

    encode : Codec α → α → Option (List UInt8)

Encoding is partial by design: an out-of-domain value (e.g. `pure x₀` given
`x ≠ x₀`, or `subset p` given `¬ p x` through an applied iso) returns `none`.
This is *not* a departure from the paper — it is the paper's `Maybe` printer
(§4.2) kept as-is; we deliberately do not totalize it.
-/

namespace Codec

/-- The partial encoder: produce bytes for a value, or `none` when the value is
outside the description's domain. -/
def encode {α : Type} (d : Codec α) (x : α) : Option (List UInt8) :=
  match d with
  | Codec.iso i d =>
      match i.unapply x with
      | none => none
      | some a => encode d a
  | Codec.seq d₁ d₂ =>
      match x with
      | (x₁, x₂) =>
          match encode d₁ x₁ with
          | none => none
          | some s₁ =>
              match encode d₂ x₂ with
              | none => none
              | some s₂ => some (s₁ ++ s₂)
  | Codec.alt d₁ d₂ => encode d₁ x <|> encode d₂ x
  | Codec.empty => none
  | Codec.pure x₀ => if x = x₀ then some [] else none
  | Codec.byte => some (single x)

/-! ## The total encoder for repetition -/

/-- The total encoder for unbounded repetition: encode each element of `xs` with
`p` and concatenate. This is the `encode` counterpart to `decodeRepeat` (and the
denotation `relRepeat (Rel p)` in `Codec.Codec`). Recursion is structural on the
*value* list `xs`, so it is total for **every** `p` — encoding needs no
productivity witness (unlike `decodeRepeat`, which takes `h : ConsumesByte p`).

Its soundness law is `Codec.Sound.encodeRepeat_rel`. -/
def encodeRepeat {α : Type} (p : Codec α) (xs : List α) : Option (List UInt8) :=
  match xs with
  | [] => some []
  | x :: rest =>
      match encode p x with
      | none => none
      | some s =>
          match encodeRepeat p rest with
          | none => none
          | some t => some (s ++ t)

end Codec
