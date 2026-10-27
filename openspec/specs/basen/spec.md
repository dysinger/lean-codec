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

### Requirement: A decoder rejects malformed input

Each `BaseN` decoder — the whole-input decoder
`Codec.decodeFull {x}Elem {x}ConsumesByte n s` over the base's element
`Codec UInt8` `{x}Elem` (for the fixed-width bases; the whole-input format is the
derived `Run` over that element) or, for base32/64, the
whole-input decoder over the base's **composition** (the full-block `Run` =
derived `many`, followed by the terminal-tail `Codec` `{x}TailElem`, with the
result `iso`-ed to the terminal-tail value type `B32`/`B64`; see the D7 note
— there is **no** single `Codec B32`/`Codec B64` value, because the `Codec` AST
has no repetition node) — SHALL return `none` for **every**
input `s` that is not a valid encoding for that base. There is no bespoke
`decodeB32Strict`/`decodeB64Strict` function: rejection is a theorem over the
uniform `Codec.decode`/`decodeFull` composition, not a per-format decoder. "Not valid" SHALL mean
_any one_ of: (a) a byte outside the base's alphabet (for base16, outside the
**hex alphabet** `0-9a-fA-F` — the `Codec` value is a strict **uppercase**
bijection, and RFC 4648 §8's requirement that a decoder accept both cases is
satisfied by the separate case-insensitive decoder `Base16.decodeHexFold`, which
applies the canonicality-preserving case fold **outside** that `Iso` via
`Codec.Normal`; see the §8 requirement below); (b) for the padded bases (base32/base64), a `=` in an illegal position
— including a `=` in the first/second/third data position of any block, a
lone/partial `=` group, or **any data after the terminal `=`**; (c) a wrong
arity (a whole-input byte count that is not a whole number of that base's code
words); and (d) a value that overflows the reconstructed byte (e.g. a base8/10
digit triple `> 255`). The rejection SHALL be proved (`… = none`),
`[propext, Quot.sound]`-only, as an **inequation over the composition** — the
whole-input decoder is `List.head? ((decodeRepeat {x}Elem …).filterMap (decodeFull
{x}TailElem …))` over the byte-list value, so `= none` follows by the
pad-dichotomy: a full block never contains `=` (so the run cannot consume the
trailing-data block), and a terminal-tail block must contain `=` (so the leftover
alphabet-only bytes cannot decode as a tail). The `B32`/`B64` terminal-tail value
types are the **canonical block/tail spine** — a proved total bijection with
`List UInt8` whose tails are terminal (no constructor continues after a tail).
Because they are canonical, the malformed shape has no inhabitant, and
`decodeFullB{64,32}_char_via_type` proves the decoder's image is exactly the image
of `encodeB{64,32} ∘ b{64,32}BytesOf`: the inequation above and the type-level fact
agree, rather than the type being merely decorative.

#### Scenario: A byte outside the alphabet is rejected

- **WHEN** `Codec.decodeFull {x}Elem {x}ConsumesByte` is applied to a `Bytes n`
  containing a byte that is not in the base's alphabet (e.g. `!` for base64, or
  a non-`0/1` byte for base2)
- **THEN** the result is `none`, and a theorem states exactly that.

#### Scenario: Illegal or non-terminal padding is rejected

- **WHEN** the uniform decoder over the padded-base composition (the full-block
  `Run` + terminal-tail `Codec`, `iso`-ed to `B64`/`B32`) is applied to a `Bytes n`
  where `=` appears in an illegal position — the first position of a block, a lone
  partial pad group, or followed by any non-`=` data (`"Zg==AAAA"`,
  `"MY======AAAAAAAA"` as the terminal-`=`-then-data two-block case)
- **THEN** the result is `none` (the `=` is terminal-only per RFC 4648 §3.2),
  proved as an **inequation** — the full-block run stops at the first `=` (no
  `b64BlockElem`/`b32BlockElem` value contains `=`), the leftover alphabet-only
  bytes cannot decode as a `b64TailElem`/`b32TailElem` (which must contain `=`),
  so `decodeFullB64`/`decodeFullB32 = none`.

#### Scenario: Wrong arity is rejected

- **WHEN** a whole-input decoder is applied to a `Bytes n` whose length is not a
  whole number of code words for that base (e.g. 2 base64 chars, 3 base32 chars)
- **THEN** the result is `none`.

#### Scenario: Rejection is the general law, not a vector set

The rejection requirement is quantified over **every** input, and the shipped
theorems are that quantifier — not a collection of named examples. For each of
`Base64` and `Base32`:

- **WHEN** a byte failing the base's alphabet-or-pad predicate (`b64OrPad`/
  `b32OrPad`) occurs at **any** index `i : Fin n` of a `Bytes n`
- **THEN** `decodeFullB{64,32} s = none`
  (`decodeFullB{64,32}_reject_invalid_at`) — generalising the index-0-only
  `reject_first_invalid` to every position.
- **WHEN** a `=` occurs at code-word slot `0` or `1` (i.e. `i % 4 ∈ {0,1}` for
  base64, `i % 8 ∈ {0,1}` for base32) — the non-terminal-padding class, of which
  `"Zg==Zg=="` / `"MY======MY======"` are instances
- **THEN** `decodeFullB{64,32} s = none`
  (`decodeFullB{64,32}_reject_pad_at_low_slot`). This holds for **all** `s`: the
  full-block region is alphabet-only and code-word aligned, and a terminal-tail
  block pads only at slots `≥ 2` (`Rel_b{64,32}TailElem_pad_pos`).
- **WHEN** the byte count is not a whole number of code words — `n % 4 ≠ 0` for
  base64, `n % 8 ≠ 0` for base32
- **THEN** `decodeFullB{64,32} s = none` (`decodeFullB{64,32}_reject_arity`),
  because a successful decode consumes exactly `4 · (|blocks| + |tails|)` bytes
  (resp. `8 · …`) — see `decodeFullB{64,32}_arity`.
- **AND** each of these is `[propext, Quot.sound]`-only, pinned by the `Axioms.lean`
  gate, with a concrete bench vector.

#### Scenario: An overflowing reconstructed byte is rejected

- **WHEN** a fixed-digit base (base8/base10) decoder is applied to a digit trio
  that exceeds `255` (e.g. octal `377` or decimal `255` is fine; `400`/`256` is
  not)
- **THEN** the result is `none`. (Base2/4/16 cannot overflow a byte by
  construction; no such theorem is needed for them.)

### Requirement: The encoder is canonical

For each base, the encoder (`Codec.encode {x}Elem`, equivalently `encode{X}`
over `List UInt8` for the fixed-width bases; `Codec.encode` over the base32/64
composition — full-block `Run` + terminal-tail `Codec`, `iso`-ed to `B32`/`B64`) SHALL
be the RFC 4648 (or this package's own spec) **canonical**
form: every output byte is in the base's alphabet, and for the padded bases the
`=` pad characters appear **only** in the terminal tail with exactly the RFC
§4.7/§6.7 pad count for the tail's length. Formally, for base32/base64, a
tail of byte length `k` encodes to exactly the RFC pad run (base32 byte length
→ pad count: 1→6, 2→4, 3→3, 4→1, 5→0; base64: 1→2, 2→1, 3→0) and `=` never
precedes a non-`=` byte in the whole output; for base16/2/4/8/10 (no padding)
every output byte is an alphabet character.

#### Scenario: Encoded output uses only the alphabet

- **WHEN** `encode{X}`/`Codec.encode <baseCodec>` is applied to a value
- **THEN** there is a theorem that every element byte of the result satisfies
  the base's digit predicate (the RFC §4/§6/§8 table, or the hand alphabet for
  base2/4/8/10), with `=` permitted only for the padded bases.

#### Scenario: Padding is terminal and arity-correct

- **WHEN** base32/base64 encode a terminal tail of a given byte length
- **THEN** the output's `=` characters occupy exactly the RFC tail for that
  byte length, stated as **byte length → pad count**: base32 1→6, 2→4, 3→3,
  4→1, 5→0; base64 1→2, 2→1, 3→0 — and appear only at the very end of the
  output, never followed by data — as a theorem, not an observation.

### Requirement: Decode is the unique canonical inverse

For each base, the whole-input decoder SHALL be the **unique** inverse of the
encoder: whenever the decoder (`Codec.decodeFull {x}Elem {x}ConsumesByte n s`
for the fixed-width bases; the whole-input form over the base32/64
composition — full-block `Run` + terminal-tail `Codec`, `iso`-ed to `B64`/`B32`) returns `some v`, the encoder `encode{X} v`/`Codec.encode <codec> v`
reproduces `s` byte-for-byte, and the encoder is injective on its value. Combined with the
existing roundtrip law (`decodeFull (encode bs) = some bs`), this makes the
encoder and decoder a partial isomorphism with a single canonical
representation per value.

#### Scenario: A successful decode re-encodes to the input

- **WHEN** the whole-input decoder (`Codec.decodeFull {x}Elem {x}ConsumesByte n s`,
  or the whole-input form over the base32/64 composition — full-block `Run` +
  terminal-tail `Codec`, `iso`-ed to `B64`/`B32`) returns
  `some v` for some `s, v`
- **THEN** `encode{X} v`/`Codec.encode <codec> v = some ⟨n, s⟩` (a theorem, proved
  `[propext, Quot.sound]`-only).

#### Scenario: Encoding is injective

- **WHEN** `encode{X} v = encode{X} v'` (or `Codec.encode <codec> v = Codec.encode
<codec> v'` for base32/64) for values `v, v'`
- **THEN** `v = v'` (each valid encoding identifies exactly one value).

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

### Requirement: Base16 decoding accepts both cases (RFC 4648 §8)

The Base16 decoder SHALL accept hex digits in **either** case, as RFC 4648 §8
requires, and SHALL return the same value for a block and its case-folded form.
The canonical alphabet SHALL remain uppercase and the encoder SHALL emit only it.
Case-insensitivity SHALL be supplied by a fold applied **outside** the strict
`Iso` — never by weakening `Iso.law` — so the `Codec` value stays a strict
uppercase bijection and the widening is confined to decoding.

#### Scenario: Both cases decode to the same value

- **WHEN** a byte string and its uppercase-folded form are decoded
- **THEN** both produce the same value: `decodeHexFold s = decodeHexFold
(foldList s)` for one block (`decodeHexBlockFold_case_insensitive`) and
  `decodeHexFold s = decodeFull hexRun (foldByteBytes s)` at whole-input level.

#### Scenario: The strict decoder still rejects lowercase

- **WHEN** lowercase input is fed to the strict `Codec`-value decoder
  `decodeFull hexElem hexConsumesByte`
- **THEN** it returns `none` — the canonical bijection is unchanged
  (`rejects_lowercase`), and this is **not** a §8 divergence because the
  conformant surface is the separate `decodeHexFold`. The earlier
  "a case-insensitive alphabet would break `Unambiguous`" rationale is withdrawn:
  the constraint is the canonicality of encode.

#### Scenario: The encoder emits a normal form (the layer's obligation)

- **WHEN** the encoder produces a block (`hexBlockUnapply b = some cs`)
- **THEN** that block is already a **fixed point** of the fold (`foldList cs = cs`,
  `foldList_hexBlockUnapply`) — the per-instance hypothesis the normalising
  decoder requires, without which `norm` applied before `unapply` could make
  decoding fail on the encoder's own output.

#### Scenario: The fold is upward, and idempotent

- **WHEN** the case fold is applied
- **THEN** it maps `a`–`f` **up** to `A`–`F` (so the canonical uppercase encoding
  is a fixed point) and is idempotent (`foldByte_idem`, `foldList_idem`), which is
  the `Normalizer` law that makes the quotient type well-formed. It is
  length-preserving by construction (`Bytes n → Bytes n`), which is the class of
  variation `Codec.Normal` is specified for.
