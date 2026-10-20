# Spec Delta

## Purpose

Defines the base-`N` encoding/decoding package `basen`: one verified package
covering base 2, 4, 8, 10, 16, 32, and 64, each as a `codec` `Codec` value over
`satisfy`/`count`/`iso` plus the productive repetition layer (no bespoke
`encode`/`decode`), with an inherited roundtrip law and the single-substrate +
axiom-discipline invariants inherited from `codec`.

This delta supersedes the original `lean-basen` bespoke-surface delta (the
`encode : List UInt8 → List UInt8` / `decode : List UInt8 → Option (List UInt8)`
statement). The bespoke phase was re-derived as `Codec` values by
`basen-uniform-leaf-api` (archived); this delta records the final surface.

## ADDED Requirements

### Requirement: One package covers all seven bases

The `basen` package SHALL provide base 2, 4, 8, 10, 16, 32, and 64 in a single
package, under one `BaseN` module namespace, each as a `codec` `Codec` value.
The four RFC 4648 encodings (base16, base32, base64) SHALL match RFC 4648,
base8 SHALL be three octal digits per byte, and base2/base4/base10 SHALL be
defined by this package's own spec (bit/quartet digit math, and decimal digit
math respectively).

#### Scenario: All seven bases are present

- **WHEN** a consumer imports `BaseN`
- **THEN** the seven per-base modules are all available (not spread across
  multiple packages or absent), each exposing a `Codec` value and its run triple.

#### Scenario: The RFC 4648 bases match the RFC

- **WHEN** base16, base32, or base64 encode a byte string
- **THEN** the output uses the RFC 4648 alphabet (base16 `0-9A-F`; base32
  `A-Z2-7`; base64 `A-Za-z0-9+/`) with the RFC's padding rules.

### Requirement: Every base satisfies a roundtrip law

For each of the seven bases, the whole-input decoder SHALL invert the encoder:
for every value `bs`, `Codec.decodeFull {x}Elem {x}ConsumesByte` applied to the
substrate produced by `encode{X} bs`/`encodeB{X} bs` returns `some bs`. The
proof SHALL be the inherited `roundtrip` law, `[propext, Quot.sound]`-only.

#### Scenario: Roundtrip holds for every base

- **WHEN** the roundtrip theorem for base `N` is checked (e.g.
  `BaseN.Base8.roundtrip`)
- **THEN** `#print axioms` reports only `[propext, Quot.sound]`, and the
  theorem is the inherited `decodeFull (encode bs) = some bs` for all `bs`.

#### Scenario: Known vectors are byte-exact

- **WHEN** a base's block encoder is `#eval`'d on a known vector (RFC 4648 §10,
  or a hand vector for base2/4/8/10)
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

## MODIFIED Requirements

### Requirement: The `basen` bases are `Codec` values

Each `BaseN` base SHALL be a `codec` `Codec` **element** plus a productive
repetition **run triple** — **not** a single `Codec (List UInt8)` value and
**not** a bespoke `encode`/`decode` function. The fixed-width bases (2/4/8/10/16)
have element `{x}Elem : Codec UInt8` (one byte per element); the block bases
(32/64) have element `b32Elem`/`b64Elem : Codec (List UInt8)` (a 5-byte / 3-byte
block), each composed from `satisfy`/`count`/`iso` (no `many` constructor
exists; the repetition layer is `decodeRepeat`/`encodeRepeat`). The run triple
is `decode{X} = decodeRepeat {x}Elem {x}ConsumesByte`, `encode{X} =
encodeRepeat {x}Elem`, `rel{X} = relRepeat (Rel {x}Elem)`; the whole-input
decoder is `Codec.decodeFull {x}Elem {x}ConsumesByte` (result `List UInt8` for
fixed-width, `List (List UInt8)` for block bases) and the encoder is
`encode{X}`/`encodeB{X}` over the `Bytes n` substrate.

#### Scenario: Base16/32/64 are Codec values

- **WHEN** a consumer uses base16/32/64
- **THEN** each is a `Codec` **element** (`hexElem : Codec UInt8`,
  `b32Elem`/`b64Elem : Codec (List UInt8)`) plus a run triple; the entry points
  are `Codec.decodeFull {x}Elem {x}ConsumesByte` and `encode{X}`/`encodeB{X}` —
  there is no `BaseN.Base16.decode` bespoke function.

#### Scenario: The bases compose from the codec primitives

- **WHEN** a base module is inspected
- **THEN** its element is `Codec.iso <blockIso> (count k (Codec.satisfy <digit>))`
  and its decoder/encoder are `decodeRepeat`/`encodeRepeat` — no hand-written
  per-format `decode`/`encode`.

#### Scenario: A decoder rejects malformed input (whole-input)

- **WHEN** `Codec.decodeFull {x}Elem {x}ConsumesByte` is applied to a `Bytes n`
  that is not a whole number of valid code words for that base
- **THEN** the result is `none`. (The full rejection contract — bad alphabet
  byte, illegal padding, wrong arity, trailing data after `=`, overflow — is the
  separate `basen-rfc-conformance-theorems` change, not this one.)
