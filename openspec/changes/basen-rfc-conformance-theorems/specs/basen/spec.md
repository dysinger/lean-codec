# Spec Delta

## Purpose

Strengthens the `basen` specification from "roundtrip holds" to **complete RFC
4648 conformance**, anchored to the already-synced **`Codec`-value surface**
(the base spec already requires every base to be a `Codec (List UInt8)` value
with no bespoke `encode`/`decode`). Per base: the encoder's output is canonical
(alphabet-only, terminal-only padding), the whole-input decoder
(`Codec.decodeFull {x}Elem {x}ConsumesByte`) rejects _every_ malformed input,
and `decodeFull … = some ys → encode ys` reproduces the input (unique canonical
inverse), with `encode` injective. The rules for Base16/32/64 are the
`rfc4648.md` reference; Base2/4/8/10 are governed by this package's own spec,
with the same rejection/canonical discipline applied.

## ADDED Requirements

### Requirement: A decoder rejects malformed input

Each `BaseN` decoder — the whole-input decoder
`Codec.decodeFull {x}Elem {x}ConsumesByte n s` (for the fixed-width bases, the
`{x}Elem` run over `Bytes n`; for base32/64, the `b32Elem`/`b64Elem` run) —
SHALL return `none` for **every** input `s` that is not a valid encoding for
that base. "Not valid" SHALL mean _any one_ of: (a) a byte outside the base's
alphabet (for base16, outside the **uppercase canonical** alphabet `0-9A-F` —
lowercase `a-f` is _not_ accepted by the `Codec` value, which is a strict
uppercase bijection; see the non-goal below); (b) for the padded
bases (base32/base64), a `=` in an illegal position — including a `=` in the
first/second/third data position of any block, a lone/partial `=` group, or
**any data after the terminal `=`**; (c) a wrong arity (a whole-input byte count
that is not a whole number of that base's code words); and (d) a value that
overflows the reconstructed byte (e.g. a base8/10 digit triple `> 255`). The
rejection SHALL be proved (`Codec.decodeFull … = none`) for each class,
`[propext, Quot.sound]`-only, not merely true by construction. One class —
trailing data after a terminal `=` (RFC 4648 §3.2) — is a **code** change (the
padded bases' run-level guard, see `design.md` §D3): the other classes are
already rejected by construction (block `iso`/`satisfy`/arity/overflow) and
need only the proving theorem.

#### Scenario: A byte outside the alphabet is rejected

- **WHEN** `Codec.decodeFull {x}Elem {x}ConsumesByte` is applied to a `Bytes n`
  containing a byte that is not in the base's alphabet (e.g. `!` for base64, or
  a non-`0/1` byte for base2)
- **THEN** the result is `none`, and a theorem states exactly that.

#### Scenario: Illegal or non-terminal padding is rejected

- **WHEN** a padded-base whole-input decoder is applied to a `Bytes n` where `=`
  appears in an illegal position — the first position of a block, a lone partial
  pad group, or followed by any non-`=` data (`"Zg==AAAA"`, `"MY======AAAAAAAA"`
  as the terminal-`=`-then-data two-block case)
- **THEN** the result is `none` (the `=` is terminal-only per RFC 4648 §3.2).

#### Scenario: Wrong arity is rejected

- **WHEN** a whole-input decoder is applied to a `Bytes n` whose length is not a
  whole number of code words for that base (e.g. 2 base64 chars, 3 base32 chars)
- **THEN** the result is `none`.

#### Scenario: An overflowing reconstructed byte is rejected

- **WHEN** a fixed-digit base (base8/base10) decoder is applied to a digit trio
  that exceeds `255` (e.g. octal `377` or decimal `255` is fine; `400`/`256` is
  not)
- **THEN** the result is `none`. (Base2/4/16 cannot overflow a byte by
  construction; no such theorem is needed for them.)

### Requirement: The encoder is canonical

For each base, the encoder (`encode{X}` over `List UInt8` for the fixed-width
bases, `encodeB{X}` over `List (List UInt8)` for base32/64) SHALL be the RFC 4648
(or this package's own spec) **canonical** form: every output byte is in the
base's alphabet, and for the padded bases the `=` pad characters appear **only**
in the terminal positions with exactly the RFC §4.7/§6.7 pad count for the input
block's length. Formally, for base32/base64, a block of fixed byte length encodes
to exactly the RFC tail (base32 byte length → pad count: 1→6, 2→4, 3→3, 4→1,
5→0; base64: 1→2, 2→1, 3→0) and `=`
never precedes a non-`=` byte in the whole output; for base16/2/4/8/10 (no
padding) every output byte is an alphabet character.

#### Scenario: Encoded output uses only the alphabet

- **WHEN** `encode{X}`/`encodeB{X}` is applied to a value
- **THEN** there is a theorem that every element byte of the result satisfies
  the base's digit predicate (the RFC §4/§6/§8 table, or the hand alphabet for
  base2/4/8/10), with `=` permitted only for the padded bases.

#### Scenario: Padding is terminal and arity-correct

- **WHEN** base32/base64 encode a block of a given byte length
- **THEN** the output's `=` characters occupy exactly the RFC tail for that
  byte length, stated as **byte length → pad count**: base32 1→6, 2→4, 3→3,
  4→1, 5→0; base64 1→2, 2→1, 3→0 — and appear only at the very end of the
  block, never followed by data — as a theorem, not an observation.

### Requirement: Decode is the unique canonical inverse

For each base, the whole-input decoder SHALL be the **unique** inverse of the
encoder: whenever `Codec.decodeFull {x}Elem {x}ConsumesByte n s` returns
`some ys`, the encoder `encode{X} ys`/`encodeB{X} ys` reproduces `s`
byte-for-byte, and the encoder is injective on its value. Combined with the
existing roundtrip law (`decodeFull (encode bs) = some bs`), this makes the
encoder and decoder a partial isomorphism with a single canonical
representation per value.

#### Scenario: A successful decode re-encodes to the input

- **WHEN** `Codec.decodeFull {x}Elem {x}ConsumesByte n s = some ys` for some
  `s, ys`
- **THEN** `encode{X} ys`/`encodeB{X} ys = some ⟨n, s⟩` (a theorem, proved
  `[propext, Quot.sound]`-only).

#### Scenario: Encoding is injective

- **WHEN** `encode{X} bs = encode{X} bs'` (or the `encodeB{X}` analogue) for
  values `bs, bs'`
- **THEN** `bs = bs'` (each valid encoding identifies exactly one value).

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
