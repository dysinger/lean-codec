# Spec Delta

## Purpose

A verified, byte-exact, bidirectional description framework over bytes: one
description value gives both a decoder (bytes → value) and an encoder (value →
bytes) that are provably inverse.

## ADDED Requirements

### Requirement: Invertibility by construction

The library SHALL represent a partial isomorphism (`Iso α β`) as a pair of
functions `apply : α → Option β` and `unapply : β → Option α` together with a
proof that they are inverses: `apply a = some b ↔ unapply b = some a`, for all
`a` and `b`.

#### Scenario: An Iso carries its inverse law

- **WHEN** a value of type `Iso α β` is constructed
- **THEN** it MUST include a proof of the inverse law; there is no way to build
  an `Iso` without it.

### Requirement: Byte-exact roundtrip

For every **`alt`-free** codec `c : Codec α` (i.e. `NoAlt c`, descriptions built
from `$`, `*`, `empty`, `pure`, and `byte` only) and every value `x : α` in
`c`'s domain, encoding then decoding SHALL reproduce the exact value and consume
exactly the encoded bytes:

`encode c x = some s → decode c s = .ok (x, [])`.

`alt` (committed choice) is **out of scope** for this guarantee: the committed
decoder's left-bias disagrees with the backtracking `Rel` relation whenever two
branches accept competing prefixes of the same input. Soundness over `alt` is a
separate, deferred requirement (`alt` prefix-disjointness, below).

#### Scenario: Encode-then-decode returns the value

- **WHEN** `x` is in the codec's domain and `encode c x = some s`
- **THEN** `decode c s` returns `(x, [])` — the value plus an empty remaining
  buffer.

#### Scenario: Committed choice is excluded from the guarantee

- **WHEN** a description contains `alt` (committed `|`)
- **THEN** the unconditionally-proven roundtrip does **not** extend to it; the
  decoder's single-result, left-biased semantics can disagree with `Rel` when
  branches overlap on a prefix.

### Requirement: Lossless capture of allowable bytes

Any run of bytes a codec's predicate permits SHALL be captured as part of the
decoded value and re-emitted verbatim on encode; no byte SHALL be silently
discarded.

#### Scenario: Optional bytes are preserved

- **WHEN** a description decodes a maximal run of bytes satisfying predicate `p`
  via `many (subset p byte)`
- **THEN** that exact run is part of the decoded value and is re-emitted byte-for-
  byte on encode.

### Requirement: Deterministic, positional decoding

Decoding SHALL be a deterministic, single-result function over a byte buffer (a
`List UInt8`) that returns the decoded value together with the (possibly empty)
remaining bytes; on failure it SHALL return an error whose position is the
length of the unconsumed prefix.

#### Scenario: Failure reports a position

- **WHEN** a decode fails
- **THEN** the returned error carries the remaining unconsumed bytes, from which
  the failure position is `whole.length - remaining.length`.

### Requirement: Partial encoding

Encoding SHALL be partial: a codec returns no result for a value outside its
domain.

#### Scenario: Out-of-domain value

- **WHEN** `encode c x` is called with `x` outside `c`'s domain (e.g. `pure x₀`
  given `x ≠ x₀`, or `subset p` given `¬ p x`)
- **THEN** it returns `none`.

### Requirement: Composition is inverse-preserving

The combinators `$` (apply an iso), `*` (product/sequential), `|` (choice), and
`empty` SHALL preserve invertibility: composing proven-inverse descriptions
yields a proven-inverse description.

#### Scenario: Composition preserves the roundtrip

- **WHEN** two codecs `c₁`, `c₂` are composed with `*`
- **THEN** `encode (c₁ * c₂) (x₁, x₂)` roundtrips through `decode` to `((x₁, x₂), [])` whenever each component roundtrips.

### Requirement: `alt` prefix-disjointness (future)

Soundness of the committed `|` decoder SHALL require the two branches to accept
**prefix-disjoint** byte strings: no string accepted by the left branch SHALL be
a (possibly improper) prefix of a string accepted by the right branch, and vice
versa. This is a **named future condition**, not yet implemented; it shares its
core with the deferred coinductive `iterate`/`foldl` combinators.

#### Scenario: Prefix overlap is rejected

- **WHEN** two branches `d₁ | d₂` accept strings where one is a prefix of the
  other (e.g. `byte | (byte * byte)`)
- **THEN** the description does **not** satisfy the prefix-disjointness
  condition, and no roundtrip claim is made for it.
