# Spec Delta

## Purpose

Strengthens the `basen` specification from "roundtrip holds" to **complete RFC
4648 conformance**: per base, the encoder's output is canonical (alphabet-only,
terminal-only padding), the decoder rejects _every_ malformed input, and
`decode xs = some ys → encode ys = xs` (unique canonical inverse). The rules for
Base16/32/64 are the `rfc4648.md` reference; Base2/4/8/10 are governed by this
package's own spec, with the same rejection/canonical discipline applied.

## MODIFIED Requirements

### Requirement: A decoder rejects malformed input

Each `BaseN` decoder SHALL return `none` for **every** input that is not a valid
encoding for that base. "Not valid" SHALL mean _any one_ of: (a) a byte outside
the base's alphabet (or, for base16, not a case-insensitive hex digit); (b) for
the padded bases (base32/base64), a `=` in an illegal position — including a `=`
in the first/second/third data position of any block, a lone/partial `=` group,
or **any data after the terminal `=`**; (c) a wrong arity (a byte count that is
not a whole number of that base's code words); and (d) a value that overflows
the reconstructed byte (e.g. a base8/10 digit triple `> 255`, relevant to the
fixed-digit bases). The rejection SHALL be proved (`decode … = none`) for each
class, `[propext, Quot.sound]`-only, not merely true by construction.

#### Scenario: A byte outside the alphabet is rejected

- **WHEN** `decode` is applied to a list containing a byte that is not in the
  base's alphabet (e.g. `!` for base64, or a non-`0/1` byte for base2)
- **THEN** the result is `none`, and a theorem states exactly that.

#### Scenario: Illegal or non-terminal padding is rejected

- **WHEN** a padded-base decoder is applied to a list where `=` appears in an
  illegal position — the first position of a block, a lone partial pad group, or
  followed by any non-`=` data (`"Zg==AAAA"`, `"MY======AAAAAAAA"`)
- **THEN** the result is `none` (the `=` is terminal-only per RFC 4648 §3.2).

#### Scenario: Wrong arity is rejected

- **WHEN** a decoder is applied to a list whose length is not a whole number of
  code words for that base (e.g. 2 base64 chars, 3 base32 chars)
- **THEN** the result is `none`.

#### Scenario: An overflowing reconstructed byte is rejected

- **WHEN** a fixed-digit base (base8/base10) decoder is applied to a digit trio
  that exceeds `255` (e.g. octal `377` or decimal `255` is fine; `400`/`256` is
  not) or any base reconstructs a byte `≥ 256`
- **THEN** the result is `none`.

## ADDED Requirements

### Requirement: The encoder is canonical

For each base, `encode` SHALL be the RFC 4648 (or this package's own spec)
**canonical** form: every output byte is in the base's alphabet, and for the
padded bases the `=` pad characters appear **only** in the terminal positions
with exactly the RFC §4.7/§6.7 pad count for the input's remainder. Formally,
for base32/base64, `encode bs` ends in the RFC-mandated `0/1/3/4/6` run of `=`
(and never has `=` followed by data); for base16/2/4/8/10 (no padding) every
output byte is an alphabet character.

#### Scenario: Encoded output uses only the alphabet

- **WHEN** `encode` is applied to a byte string
- **THEN** there is a theorem that every element of the result is in the base's
  alphabet (the RFC §4/§6/§8 table, or the hand alphabet for base2/4/8/10).

#### Scenario: Padding is terminal and arity-correct

- **WHEN** base32/base64 encode a byte string of length `n`
- **THEN** the output's `=` characters occupy exactly the RFC §6.7/§4.7 tail
  (0, 1, 3, 4, or 6 / 0, 1, or 2 pads respectively) and appear only at the very
  end, never followed by data — as a theorem, not an observation.

### Requirement: Decode is the unique canonical inverse

For each base, `decode` SHALL be the **unique** inverse of `encode`: whenever
the decoder accepts `xs` (returns `some ys`), `encode ys` reproduces `xs`
byte-for-byte, and `encode` is injective on byte strings. Combined with the
existing roundtrip law (`decode (encode bs) = some bs`), this makes `encode` and
`decode` a partial isomorphism with a single canonical representation per byte
string.

#### Scenario: A successful decode re-encodes to the input

- **WHEN** `decode xs = some ys` for some `xs, ys`
- **THEN** `encode ys = xs` (a theorem, proved `[propext, Quot.sound]`-only).

#### Scenario: Encoding is injective

- **WHEN** `encode bs = encode bs'` for byte strings `bs, bs'`
- **THEN** `bs = bs'` (each valid encoding identifies exactly one byte string).

### Requirement: The conformance laws are gated like the roundtrip laws

Every new canonical/ rejection/ converse/ injectivity theorem SHALL be provable
with only `propext` and `Quot.sound`, zero `sorry`, no `Classical.choice`, and
SHALL be covered by a bench-lane vector (an `example` or `#eval`) so the gate
exercises them, matching the F* reference's `decode_*_invalid` vector set.

#### Scenario: The gate covers the new laws

- **WHEN** `lake build` and `#print axioms` run on the conformance laws
- **THEN** the build has zero `sorry`/warnings, `#print axioms` reports only
  `[propext, Quot.sound]` for each new theorem, and the bench lane value-checks
  each rejection/canonical vector byte-for-byte.
