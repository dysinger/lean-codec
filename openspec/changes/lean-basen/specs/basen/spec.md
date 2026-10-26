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
repetition **run** — **not** a single `Codec (List UInt8)` value and **not** a
bespoke per-format decoder/encoder _triple_. The fixed-width bases (2/4/8/10/16)
have element `{x}Elem : Codec UInt8` (one byte per element); the padded bases
(32/64) are a composition of a full-block element `b32BlockElem`/`b64BlockElem :
Codec (List UInt8)` (a 5-byte / 3-byte block) run through the derived repetition
layer, followed by a terminal-tail element `b32TailElem`/`b64TailElem`, `iso`-ed
to the terminal-tail value type `B32`/`B64`. Each element is composed from
`satisfy`/`count`/`iso` (no `many` constructor exists; the repetition layer is
`relRepeat`/`decodeRepeat`/`encodeRepeat`). The whole-input decoder is
`Codec.decodeFull`/the base's own `decodeFullB{32,64}` over the composition, and
the encoder is `encode{X}`/`encodeB{X}` over the `Bytes n` substrate; `B32`/`B64`
is a proved total bijective relabeling of `List UInt8`.

The padded bases' shape makes illegal "data after `=`" unrepresentable **at the
canonical value type**, and this is a proved equivalence. `B32`/`B64` are block/tail
spines with **terminal** tails (`nil` / `full` / `tail1`…/`tail2`…) and no
constructor continuing after a tail, and they are a proved total bijection with
`List UInt8` (`b{64,32}BytesOf_ofBytes` / `b{64,32}OfBytes_bytesOf`). The
characterization law `decodeFullB{64,32}_char_via_type` shows the decoder's image is
**exactly** the image of `encodeB{64,32} ∘ b{64,32}BytesOf`: a byte string decodes
iff it is the encoding of some canonical `B32`/`B64`. A string carrying data after a
terminal `=` admits no such value, because the type has no inhabitant for the
tail-followed-by-block shape (`b{64,32}BytesOf_tail1_eq` makes terminality
definitional). The rejection laws state the same fact as an inequation over the
decoder composition; the two agree.

"No bespoke `encode`/`decode`" SHALL be read as **no per-format decoder/encoder
triple** (no `parseB64`/`encodeB64Strict`/`decodeB64Strict`): the whole-input
base32/64 composition is legitimately exposed as `decodeFullB{32,64}`/
`encodeB{32,64}` over the `Bytes n` substrate, and those are the value's own
entry points, not a parallel bespoke implementation.

#### Scenario: Base16/32/64 are Codec values

- **WHEN** a consumer uses base16/32/64
- **THEN** each is a `Codec`-based value decoded/encoded by `Codec.decode`/
  `Codec.encode` (base16 an element `Codec UInt8` + its `Run`; base32/64 the
  terminal-tail `B32`/`B64` value type reached via `iso` over the block-run +
  tail composition); there is no `BaseN.Base16.decode`-style per-format function.

#### Scenario: The bases compose from the codec primitives

- **WHEN** a base module is inspected
- **THEN** its element is `Codec.iso <blockIso> (count k (Codec.satisfy <digit>))`
  and its decoder/encoder are `decodeRepeat`/`encodeRepeat` — no hand-written
  per-format `decode`/`encode` triple.

#### Scenario: A decoder rejects malformed input (whole-input)

- **WHEN** `Codec.decodeFull {x}Elem {x}ConsumesByte` (or `decodeFullB{32,64}` over
  the padded composition) is applied to a `Bytes n` that is not a whole number of
  valid code words for that base
- **THEN** the result is `none`. (The full rejection contract — bad alphabet
  byte, illegal padding, wrong arity, trailing data after `=`, overflow — is the
  separate `basen-rfc-conformance-theorems` change, not this one.)

#### Scenario: Trailing data after `=` is rejected by proof _and_ by the type

- **WHEN** the padded bases' decoder is applied to input carrying data after a
  terminal `=`
- **THEN** the result is `none`, established two ways that are proved to agree: by
  the rejection laws (an inequation over the composition), and by the type-level
  characterization `decodeFullB{64,32}_char_via_type`, whose right-hand side
  quantifies only over canonical `B32`/`B64` values — and the terminal-tail shape
  of those values has no constructor that can carry trailing data.
