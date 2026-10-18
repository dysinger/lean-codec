# Spec Delta

## Purpose

Add the `satisfy` byte-predicate primitive to core `Codec`, and derive variable-
length runs over it, so byte-alphabet and variable-length tokens are expressible
as `Codec` values — the substrate-level building block for "only the codec
changes" across the whole stack.

## ADDED Requirements

### Requirement: The byte-predicate primitive `satisfy`

The core `Codec` SHALL provide `satisfy : (UInt8 → Bool) → Codec UInt8`, the
byte-token-with-guard. `satisfy p` relates a byte `b` to `single b` exactly when
`p b = true`; `decode` consumes one byte iff `p b`, else returns the empty list;
`encode` succeeds iff `p b`. It is the single substrate-touching leaf beyond
`byte`; no BE/LE/fixed-width/`varint`/text/tagged-sum constructor is added.

#### Scenario: A predicate byte decodes and encodes

- **WHEN** `satisfy p` is decoded on a leading byte `b` and encoded on a byte `b`
- **THEN** decode yields `b` iff `p b` (else no result) and encode yields the
  single byte iff `p b` (else `none`); the roundtrip holds `[propext, Quot.sound]`.

#### Scenario: A single digit is a valid decode

- **WHEN** `satisfy isHexDigit` decodes a single hex nibble
- **THEN** it succeeds for that one byte — the primitive does not force an even
  number of digits (grouping into pairs is a `count`/`iso` above the primitive).

### Requirement: Runs are derived, not constructors

Variable-length tokens (alphabet runs, varint, UTF-8, JSON string bodies) SHALL
be a maximal run of `satisfy p`, realized by the existing repetition layer
(`decodeRepeat`/`encodeRepeat`/`many`), not a new `Codec` constructor.

#### Scenario: A varint is a run with a terminator

- **WHEN** a varint-like token is decoded
- **THEN** it is `takeWhile highBitSet` + an `iso` folding the 7-bit groups — the
  terminator is the first byte with the high bit clear, expressed as a run, not
  a per-byte lookahead.
