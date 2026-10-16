# codec Specification

## Purpose

A verified, byte-exact, bidirectional description framework over bytes: one
description value gives both a decoder (bytes → value) and an encoder (value →
bytes) that are provably inverse.

## Requirements

### Requirement: Invertibility by construction

The library SHALL represent a partial isomorphism (`Iso α β`) as a pair of
functions `apply : α → Option β` and `unapply : β → Option α` together with a
proof that they are inverses: `apply a = some b ↔ unapply b = some a`, for all
`a` and `b`.

#### Scenario: An Iso carries its inverse law

- **WHEN** a value of type `Iso α β` is constructed
- **THEN** it MUST include a proof of the inverse law; there is no way to build
  an `Iso` without it.

### Requirement: Nondeterministic (backtracking) decoding

Decoding SHALL be a relation-valued function over a byte buffer, returning
**all** `(value, remaining)` pairs the description admits:

```
decode : Codec α → List UInt8 → List (α × List UInt8)
```

Choice (`|`, the paper's `Alternative`) SHALL be the **backtracking union**:
`decode (d₁ | d₂) s = decode d₁ s ++ decode d₂ s`, matching the denotation
`Rel (d₁ | d₂) = Rel d₁ ∨ Rel d₂` by construction. There is no committed choice,
no cursor, no peeking, and no narrowing to a single result.

#### Scenario: Choice enumerates every branch

- **WHEN** `decode (d₁ | d₂) s` is evaluated
- **THEN** the result is the concatenation of `decode d₁ s` and `decode d₂ s` —
  every `(value, remainder)` pair from either branch, including duplicate values.

### Requirement: Byte-exact roundtrip, unconditional

For every codec `c : Codec α` (with no `NoAlt` gate) and every value `x : α` in
`c`'s domain, encoding then decoding SHALL reproduce the value and consume
exactly the encoded bytes:

`encode c x = some s → (x, []) ∈ decode c s`.

The laws SHALL hold **unconditionally** for every description (including `alt`),
in the presence of full backtracking; no prefix-disjointness or unambiguity
condition is required.

#### Scenario: Encode-then-decode returns the value

- **WHEN** `x` is in the codec's domain and `encode c x = some s`
- **THEN** `(x, [])` is among the results of `decode c s` — the value plus an
  empty remaining buffer.

#### Scenario: The laws hold over choice

- **WHEN** a description contains `alt` (backtracking union)
- **THEN** the bidirectional law `decode_spec` and the roundtrip `roundtrip`
  still hold for it; no prefix condition is imposed.

### Requirement: Lossless capture of allowable bytes

Any run of bytes a codec's predicate permits SHALL be captured as part of the
decoded value and re-emitted verbatim on encode; no byte SHALL be silently
discarded.

#### Scenario: Optional bytes are preserved

- **WHEN** a description decodes a maximal run of bytes satisfying predicate `p`
  via repetition over a `subset p byte` step (denotation `relRepeat`, decoders
  `decodeRepeat`/`encodeRepeat`)
- **THEN** that exact run is part of the decoded value and is re-emitted byte-for-
  byte on encode.

### Requirement: Partial encoding

Encoding SHALL be partial: a codec returns no result for a value outside its
domain.

#### Scenario: Out-of-domain value

- **WHEN** `encode c x` is called with `x` outside `c`'s domain (e.g. `pure x₀`
  given `x ≠ x₀`, or `subset p` given `¬ p x`)
- **THEN** it returns `none`.

### Requirement: Composition is inverse-preserving

The combinators `$` (apply an iso), `*` (product/sequential), `|` (backtracking
choice), and `empty` SHALL preserve invertibility: composing proven-inverse
descriptions yields a proven-inverse description.

#### Scenario: Composition preserves the roundtrip

- **WHEN** two codecs `c₁`, `c₂` are composed with `*`
- **THEN** `encode (c₁ * c₂) (x₁, x₂)` roundtrips through `decode` to
  `((x₁, x₂), [])` whenever each component roundtrips.

### Requirement: Unbounded repetition is a total denotation

Unbounded repetition (`many`, paper §3.4) SHALL be realized as a total
least-fixpoint denotation with three separate interpretations, **not** as a
finite description value:

- `relRepeat (Rel p)` — the denotational relation (total for every step `p`);
- `decodeRepeat p h` — the productive decoder, well-founded on the input's
  length, taking `h : ConsumesByte p` (each step consumes ≥ 1 byte) as its
  totality witness;
- `encodeRepeat p` — the total encoder, structural on the value list.

#### Scenario: Productive repetition decodes in bounded steps

- **WHEN** `p` is productive (`Productive p`, equivalently `ConsumesByte p`)
- **THEN** `decodeRepeat p h` is a total function enumerating exactly the
  `relRepeat (Rel p)` results.

#### Scenario: Empty-matching repetition is genuinely infinite

- **WHEN** `p` matches the empty byte string (e.g. `pure ()`)
- **THEN** no finite `List` decoder can enumerate all results (the value lists
  are unbounded: `relRepeat_unbounded_of_empty`), so `decodeRepeat` is defined
  only for productive `p` and never faked with a finite result.
