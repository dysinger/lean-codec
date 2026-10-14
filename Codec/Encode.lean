/- Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later -/

import Codec.Codec

/-!
# The partial encoder

This file gives `encode`, the partial encoder, over the length-indexed byte
string:

    encode : Codec α → α → Option ({n : Nat} × Bytes n)

The encoded bytes *and* their length come back in one sigma, so `roundtrip` can
name the empty remainder `Bytes 0` without a separate length. Encoding is partial
by design: an out-of-domain value returns `none` (the paper's `Maybe` printer,
§4.2, kept as-is; we deliberately do not totalize it).
-/

namespace Codec

/-- The partial encoder: produce a length-indexed byte string for a value, or
`none` when the value is outside the description's domain. -/
def encode {α : Type} (d : Codec α) (x : α) : Option (Sigma fun n => Bytes n) :=
  match d with
  | Codec.iso i d =>
      (i.unapply x).bind fun a => encode d a
  | Codec.seq d₁ d₂ =>
      match x with
      | (x₁, x₂) =>
          (encode d₁ x₁).bind fun ⟨n₁, s₁⟩ =>
            (encode d₂ x₂).map fun ⟨n₂, s₂⟩ => ⟨n₁ + n₂, concat s₁ s₂⟩
  | Codec.alt d₁ d₂ => encode d₁ x <|> encode d₂ x
  | Codec.empty => none
  | Codec.pure x₀ => if x = x₀ then some ⟨0, emptyBytes⟩ else none
  | Codec.byte => some ⟨1, single x⟩

/-! ## The total encoder for repetition -/

/-- The total encoder for unbounded repetition: encode each element of `xs` with
`p` and concatenate, returning the total length and the concatenated bytes (a
`Fin`-sum concat, O(n) in the *type* index — no quadratic `List.append`). Recursion
is structural on the *value* list `xs`, so it is total for **every** `p` — encoding
needs no productivity witness (unlike `decodeRepeat`).

Its soundness law is `Codec.encodeRepeat_rel`. -/
def encodeRepeat {α : Type} (p : Codec α) (xs : List α) : Option (Sigma fun n => Bytes n) :=
  match xs with
  | [] => some ⟨0, emptyBytes⟩
  | x :: rest =>
      (encode p x).bind fun ⟨n₁, s₁⟩ =>
        (encodeRepeat p rest).map fun ⟨n₂, s₂⟩ => ⟨n₁ + n₂, concat s₁ s₂⟩

end Codec
