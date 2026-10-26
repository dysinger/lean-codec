# basen Specification

## Purpose

Express the `basen` bases as `Codec` values so decoding base64 and decoding JSON
are the same `Codec.decode` call — only the codec changes.

## Requirements

### Requirement: Format codecs are `Codec` values

Every concrete format (base16/32/64, and later JSON, HTTP, ASTs) SHALL be a
`Codec α` value decoded/encoded by the single `Codec.decode`/`Codec.encode` — the
only thing that differs between formats is the `Codec` value, not the operation
shape.

#### Scenario: Decoding base64 and JSON is the same call

- **WHEN** a consumer decodes base64 and JSON
- **THEN** both are `Codec.decode <codec> <bytes>` with `<codec>` a
  `Codec (List UInt8)` / `Codec JSON` value; there is no per-format
  `decode`/`encode` function.

### Requirement: The `basen` bases are `Codec` values

The `basen` package SHALL provide base2/4/8/10/16/32/64 as `Codec`-based values
(the fixed-width bases 2/4/8/10/16 as an element `Codec UInt8` (`count k
(satisfy p) ≫ blockIso`) whose unbounded repetition is the derived `Run` = `many`;
the padded bases 32/64 as a
composition of a full-block `Codec (List UInt8)` run + a terminal-tail `Codec`,
`iso`-ed to the terminal-tail value type `B32`/`B64`) composed from
`satisfy`/`count`/`iso`/`alt`, **with unbounded repetition as the derived `many`**
(`relRepeat`/`decodeRepeat`/`encodeRepeat` — never a `Codec` constructor),
roundtrip given by the inherited per-component
`decodeRepeat_spec`/`encodeRepeat_rel`/`decodeFull_spec` laws, plus one block-run/
tail split-uniqueness lemma for the padded bases.

The padded bases' composition makes illegal "data after `=`" unrepresentable **at
the canonical value type**, and this is a proved equivalence, not a convenience.
`B32`/`B64` are block/tail spines with **terminal** tails (`nil` / `full` /
`tail1`…/`tail2`…) and no constructor that continues after a tail, and they are a
proved total bijection with `List UInt8` (`b{64,32}BytesOf_ofBytes` /
`b{64,32}OfBytes_bytesOf`). The characterization law
`decodeFullB{64,32}_char_via_type` shows the decoder's image is **exactly** the
image of `encodeB{64,32} ∘ b{64,32}BytesOf`: a byte string decodes iff it is the
encoding of some canonical `B32`/`B64`. A string carrying data after a terminal
`=` admits no such value, because the type has no inhabitant for the tail-followed-
by-block shape (`b{64,32}BytesOf_tail1_eq` makes terminality definitional). The
conformance rejection laws state the same fact as an inequation over the decoder
composition; the two agree.

There is no per-format decoder/encoder **triple** (no `parseB64`/
`encodeB64Strict`/`decodeB64Strict`); the whole-input base32/64 composition is
exposed as `decodeFullB{32,64}`/`encodeB{32,64}`, the value's own entry points.

#### Scenario: Base16/32/64 are Codec values

- **WHEN** a consumer uses base16/32/64
- **THEN** each is a `Codec`-based value decoded/encoded by `Codec.decode`/
  `Codec.encode` (base16 an element `Codec UInt8` + its `Run`; base32/64 the
  terminal-tail `B32`/`B64` value type reached via `iso` over the block-run +
  tail composition); there is no `BaseN.Base16.decode`-style per-format function.

#### Scenario: Trailing data after `=` is rejected by proof _and_ by the type

- **WHEN** the padded bases' decoder is applied to input carrying data after a
  terminal `=`
- **THEN** the result is `none`, and this is established two ways that are proved
  to agree: by the conformance rejection laws (an inequation over the decoder
  composition), and by the type-level characterization
  `decodeFullB{64,32}_char_via_type`, whose right-hand side quantifies only over
  canonical `B32`/`B64` values — and the terminal-tail shape of those values has
  no constructor that can carry trailing data.
