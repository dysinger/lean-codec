# Spec Delta

## Purpose

De-duplicate the `basen` leaf modules: each base SHALL be a thin `Nat`-level digit
codec lifted through a single shared `UInt8` lift, rather than seven bespoke
copies of `encode`/`decode`/`roundtrip` and the `Nat↔UInt8<256` bridge. No new
core-`Codec` primitives, no BE/LE/fixed-width/`varint` codecs.

## ADDED Requirements

### Requirement: One package covers all seven bases (uniform leaf API)

The `basen` package SHALL provide encoders/decoders for base 2, 4, 8, 10, 16, 32,
and 64 in a single package, under one `BaseN` module namespace — **expressed as
instances of one shared `UInt8` lift over their `Nat`-level digit codecs**, not as
seven bespoke `encode`/`decode` function sets. The RFC 4648 encodings SHALL
still match RFC 4648 and the base2/4/10 digit math SHALL still be this package's
own spec.

#### Scenario: All seven bases are present

- **WHEN** a consumer imports `BaseN`
- **THEN** encoders/decoders for base 2, 4, 8, 10, 16, 32, and 64 are all
  available, each reusing the shared lift (not a bespoke `encode`/`decode`).

#### Scenario: The RFC 4648 bases match the RFC

- **WHEN** base16, base32, or base64 encode a byte string
- **THEN** the output uses the RFC 4648 alphabet with the RFC's padding rules.

#### Scenario: No core primitives are added

- **WHEN** this de-duplication lands
- **THEN** `Codec/` is untouched — no `satisfy`, `sum`, big/little-endian,
  fixed-width, or `varint` combinator is added to the core `codec` package.

### Requirement: Encoders and decoders are stated over the codec byte substrate (via the lift)

Each `BaseN` encoder/decoder SHALL remain a pure function over `List UInt8` with
`encode : List UInt8 → List UInt8` and `decode : List UInt8 → Option (List
UInt8)` — now _produced_ by the shared lift from a `Nat`-level codec, not
hand-written per base. A decoder still rejects malformed input.

#### Scenario: An encoder is a byte renderer

- **WHEN** `encode_base16_bytes` (or the per-base equivalent) is applied
- **THEN** it returns a `List UInt8` of ASCII alphabet bytes (always succeeding),
  via the shared lift.

#### Scenario: A decoder rejects malformed input

- **WHEN** `decode` is applied to a list that is not valid for that base
- **THEN** the result is `none` (the rejection is whatever the base's `Nat`-level
  `decodeN` determines, threaded through the lift).

### Requirement: Every base satisfies a roundtrip law (proved once over the lift)

For each of the seven bases, `decode (encode bs) = some bs` SHALL hold
unconditionally, `[propext, Quot.sound]`-only — **proved once over the shared
lift** and instantiated per base, not re-proved seven times.

#### Scenario: Roundtrip holds for every base

- **WHEN** the roundtrip theorem for base `N` is checked
- **THEN** `#print axioms` reports only `[propext, Quot.sound]`, and the per-base
  `roundtrip` is obtained from the shared lift (each base supplies only its
  `Nat`-level `decodeN (encodeN bs) = some bs`).

### Requirement: A shared `UInt8` lift over `Nat`-level digit codecs

The `basen` package SHALL provide one shared lift that turns a `Nat`-level codec
(`encodeN : List Nat → List Nat`, `decodeN : List Nat → Option (List Nat)`, with
digit bytes `< 256`) into the `UInt8`-level `encode`/`decode`, proving the
`Nat↔UInt8<256` bridge once.

#### Scenario: The bridge is proved once

- **WHEN** a base supplies its `Nat`-level codec and digit `< 256` facts
- **THEN** the shared lift yields `encode`/`decode` and the `UInt8` transparency
  (`toByte (codeWord b.toNat) …`, `.toNat` roundtrip) without per-base
  re-proof.
