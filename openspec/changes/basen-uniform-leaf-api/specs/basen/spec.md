# Spec Delta

## Purpose

Express the `basen` bases as `Codec` values so decoding base64 and decoding JSON
are the same `Codec.decode` call — only the codec changes.

## ADDED Requirements

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

The `basen` package SHALL provide base2/4/8/10/16/32/64 as `Codec (List UInt8)`
values composed from `satisfy`/`count`/`many`/`iso`/`alt`, with roundtrip given
by the inherited `Codec.roundtrip`, and no bespoke `encode`/`decode`.

#### Scenario: Base16/32/64 are Codec values

- **WHEN** a consumer uses base16/32/64
- **THEN** each is a `Codec (List UInt8)` value; `Codec.decode base16Codec` and
  `Codec.encode base16Codec` are the only entry points (no `BaseN.Base16.decode`).
