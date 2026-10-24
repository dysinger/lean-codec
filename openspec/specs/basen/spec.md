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
`iso`-ed to the terminal-tail value type `B32`/`B64`, so illegal "data after `=`"
is unrepresentable) composed from `satisfy`/`count`/`iso`/`alt`, **with unbounded
repetition as the derived `many`** (`relRepeat`/`decodeRepeat`/`encodeRepeat` —
never a `Codec` constructor), roundtrip given by the inherited per-component
`decodeRepeat_spec`/`encodeRepeat_rel`/`decodeFull_spec` laws, plus one block-run/
tail split-uniqueness lemma for the padded bases, and no bespoke `encode`/`decode`.

#### Scenario: Base16/32/64 are Codec values

- **WHEN** a consumer uses base16/32/64
- **THEN** each is a `Codec`-based value decoded/encoded by `Codec.decode`/
  `Codec.encode` (base16 an element `Codec UInt8` + its `Run`; base32/64 the
  terminal-tail `B32`/`B64` value type reached via `iso` over the block-run +
  tail composition); there is no `BaseN.Base16.decode`-style per-format function.
