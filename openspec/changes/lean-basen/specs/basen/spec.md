# Spec Delta

## Purpose

Defines the base-`N` encoding/decoding package `basen`: one verified package
covering base 2, 4, 8, 10, 16, 32, and 64, each with a byte-list encoder and
decoder, a roundtrip law, and the single-substrate + axiom-discipline invariants
inherited from `codec`.

## ADDED Requirements

### Requirement: One package covers all seven bases

The `basen` package SHALL provide encoders and decoders for base 2, 4, 8, 10,
16, 32, and 64 in a single package, under one `BaseN` module namespace. The
four RFC 4648 encodings (base16, base32, base64) SHALL match RFC 4648, base8
SHALL be three octal digits per byte, and base2/base4/base10 SHALL be defined by
this package's own spec (bit/quartet digit math, and decimal digit math
respectively).

#### Scenario: All seven bases are present

- **WHEN** a consumer imports `BaseN`
- **THEN** encoders/decoders for base 2, 4, 8, 10, 16, 32, and 64 are all
  available (not spread across multiple packages or absent).

#### Scenario: The RFC 4648 bases match the RFC

- **WHEN** base16, base32, or base64 encode a byte string
- **THEN** the output uses the RFC 4648 alphabet (base16 `0-9A-F`; base32
  `A-Z2-7`; base64 `A-Za-z0-9+/`) with the RFC's padding rules.

### Requirement: Encoders and decoders are stated over the codec byte substrate

Each `BaseN` encoder and decoder SHALL be a pure function over `List UInt8` (the
`codec` `Bytes n` element type), with `encode : List UInt8 → List UInt8` and
`decode : List UInt8 → Option (List UInt8)` (the `Option` for rejecting
malformed input). No other carrier (no `String`, no opaque buffer) is the spec
substrate.

#### Scenario: An encoder is a byte renderer

- **WHEN** `encode_base16_bytes` (or the per-base equivalent) is applied to a
  `List UInt8`
- **THEN** it returns a `List UInt8` of ASCII alphabet bytes (always succeeding).

#### Scenario: A decoder rejects malformed input

- **WHEN** `decode` is applied to a list that is not valid for that base
  (wrong length, or a byte outside the alphabet)
- **THEN** the result is `none`.

### Requirement: Every base satisfies a roundtrip law

For each of the seven bases, `decode` SHALL invert `encode`: for every byte
string `bs`, `decode (encode bs) = some bs`. The proof SHALL hold
unconditionally (no partiality beyond the `Option`), for `[propext, Quot.sound]`
alone.

#### Scenario: Roundtrip holds for every base

- **WHEN** the roundtrip theorem for base `N` is checked (e.g. `BaseN.roundtrip`)
- **THEN** `#print axioms` reports only `[propext, Quot.sound]`, and the
  theorem is `decode_baseN (encode_baseN bs) = some bs` for all `bs`.

#### Scenario: Known vectors are byte-exact

- **WHEN** a base's encoder/decoder is `#eval`'d on a known vector (RFC 4648
  §10, or a hand vector for base2/4/10)
- **THEN** the output matches the known-good bytes exactly (byte-for-byte, not
  length-only).

### Requirement: The axioms discipline is inherited from codec

Every law in `basen` SHALL be provable with only `propext` and `Quot.sound`, and
SHALL NOT introduce `Classical.choice` or any `sorry`. No `@[extern]`/Layer-2 C
seam is introduced: this package is pure Lean.

#### Scenario: No C seam and no extra axioms

- **WHEN** `basen` is built and `#print axioms` is run on its laws
- **THEN** the build has zero `sorry`/warnings and the axioms are exactly
  `[propext, Quot.sound]`; there is no per-format C and no Layer-2 trust seam.
