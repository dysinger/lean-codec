# codec Specification

## Purpose

A verified, byte-exact, bidirectional description framework over bytes: one
description value gives both a decoder (bytes → value) and an encoder (value →
bytes) that are provably inverse.

## Requirements

### Requirement: Invertibility by construction

The library SHALL represent a partial isomorphism (`Iso α β`) as a pair of
functions `apply : α → Option β` and `unapply : β → Option α` together with a
proof that they are inverses: `apply a = some b ↔ unapply b = some a`, for all
`a` and `b`.

#### Scenario: An Iso carries its inverse law

- **WHEN** a value of type `Iso α β` is constructed
- **THEN** it MUST include a proof of the inverse law; there is no way to build
  an `Iso` without it.

### Requirement: Nondeterministic (backtracking) decoding

Decoding SHALL be a relation-valued function over the length-indexed byte
string, returning **all** `(value, remaining-buffer)` pairs the description
admits:

```
decode : Codec α → {n : Nat} → Bytes n → List (α × ({m : Nat} × Bytes m))
```

where the remaining buffer `Bytes m` records the consumed length via `m ≤ n`.
Choice (`|`, the paper's `Alternative`) SHALL be the **backtracking union**:
`decode (d₁ | d₂) s = decode d₁ s ++ decode d₂ s`, matching the denotation
`Rel (d₁ | d₂) = Rel d₁ ∨ Rel d₂` by construction. There is no committed choice,
no cursor, no peeking, and no narrowing to a single result, and `decode d s`
itself is stated over the single `Bytes n` carrier (no `List UInt8`/`Array`/
`ByteArray`/`Buffer` carrier replaces it). A **Layer-2 fast path** (a
distinct-named surface such as `commitRemainder` or `decodeArrayFast`) MAY carry
data on `Array UInt8`/`ByteArray`, provided it is proved (or definitionally)
equal to `Bytes n`, never presented as `decode`/`encode` themselves, and never
conflated with the `Bytes n` spec substrate.

#### Scenario: Choice enumerates every branch

- **WHEN** `decode (d₁ | d₂) s` is evaluated
- **THEN** the result is the concatenation of `decode d₁ s` and `decode d₂ s` —
  every `(value, remainder)` pair from either branch, including duplicate values.

#### Scenario: The remaining buffer is length-indexed

- **WHEN** `decode c (s : Bytes n)` returns a `(value, remainder)` pair
- **THEN** `remainder : Bytes m` for a `m ≤ n` witnessed at the type, and the
  byte string is the single `Bytes` carrier — no separate `List` spec and no
  opaque run-model slab.

#### Scenario: A Layer-2 fast path does not displace the `Bytes n` substrate

- **WHEN** a distinct-named Layer-2 surface (e.g. `commitRemainder`, `decodeArrayFast`) carries data
  on `Array UInt8`/`ByteArray`
- **THEN** it is documented as proved (or definitionally) equal to `Bytes n`, never named
  `decode`/`encode`, and the `Bytes n` spec substrate remains the single denotation carrier; `decode`
  itself is unchanged.

### Requirement: Byte-exact roundtrip, unconditional

For every codec `c : Codec α` (with no `NoAlt` gate) and every value `x : α` in
`c`'s domain, encoding then decoding SHALL reproduce the value and consume
exactly the encoded bytes:

`encode c x = some ⟨n, s⟩ → (x, ⟨_, Bytes.empty⟩) ∈ decode c s`

(an empty remaining buffer `Bytes 0`, the length-indexed spelling of `[]`).
The laws SHALL hold **unconditionally** for every description (including `alt`),
in the presence of full backtracking; no prefix-disjointness or unambiguity
condition is required.

#### Scenario: Encode-then-decode returns the value

- **WHEN** `x` is in the codec's domain and `encode c x = some ⟨n, s⟩`
- **THEN** `(x, ⟨_, Bytes.empty⟩)` is among the results of `decode c s` — the
  value plus an empty remaining buffer.

#### Scenario: The laws hold over choice

- **WHEN** a description contains `alt` (backtracking union)
- **THEN** the bidirectional law `decode_spec` and the roundtrip `roundtrip`
  still hold for it; no prefix condition is imposed.

### Requirement: Lossless capture of allowable bytes

Any run of bytes a codec's predicate permits SHALL be captured as part of the
decoded value and re-emitted verbatim on encode; no byte SHALL be silently
discarded. Capture-and-re-emit SHALL be understood as the **identity normalizer**
(the degenerate case of the normal-form layer): the strict inverse law then holds
with no normalisation and no relaxation. A codec MAY instead model
**information-free variation** — presentation that carries no information, such as
the case of a hexadecimal digit — as a normal form, provided: the variation is
carried by a **total, idempotent, length-preserving** normalizer applied **outside**
the partial isomorphism; the encoder is proved to emit a **normal form** (so
decoding its own output still succeeds); and the encoder still emits exactly one
canonical spelling. Formatting is not semantic: an AST SHALL NOT be required to
carry presentation (whitespace-run length, leading zeros, case) in order to satisfy
this requirement.

#### Scenario: Optional bytes are preserved

- **WHEN** a description decodes a maximal run of bytes satisfying predicate `p`
  via repetition over a `subset p byte` step (denotation `relRepeat`, decoders
  `decodeRepeat`/`encodeRepeat`)
- **THEN** that exact run is part of the decoded value and is re-emitted byte-for-
  byte on encode.

#### Scenario: Capture-verbatim is the identity normalizer

- **WHEN** a codec captures a permitted run and re-emits it verbatim
- **THEN** its normalizer is the identity: no normalisation is applied and the
  strict inverse law holds with no relaxation, which is the degenerate case of the
  normal-form layer rather than an argument that no normal form can exist.

#### Scenario: A normalising decoder leaves the `Iso` strict

- **WHEN** a format accepts information-free variant spellings of the same value
  (e.g. case-insensitive hex digits)
- **THEN** the variants are absorbed by a total, idempotent, length-preserving
  `norm` composed before the `Iso`'s `unapply`; the `Iso` and its field-carried
  inverse law are unchanged; the encoder emits the one canonical spelling and is
  proved to emit a normal form; and no byte is discarded by the encoder.

#### Scenario: Presentation is not information

- **WHEN** a format's concrete syntax permits presentation choices that carry no
  information (case of a digit, amount of whitespace, number of leading zeros)
- **THEN** the specification does not require the decoded value to preserve them;
  preserving them is not a conformance obligation, and a codec that normalises them
  away satisfies this requirement provided the encoder's output is canonical and
  re-decodes to the same value.

### Requirement: Partial encoding

Encoding SHALL be partial: a codec returns no result for a value outside its
domain.

#### Scenario: Out-of-domain value

- **WHEN** `encode c x` is called with `x` outside `c`'s domain (e.g. `pure x₀`
  given `x ≠ x₀`, or `subset p` given `¬ p x`)
- **THEN** it returns `none`.

### Requirement: Composition is inverse-preserving

The combinators `$` (apply an iso), `*` (product/sequential), `|` (backtracking
choice), and `empty` SHALL preserve invertibility: composing proven-inverse
descriptions yields a proven-inverse description.

#### Scenario: Composition preserves the roundtrip

- **WHEN** two codecs `c₁`, `c₂` are composed with `*`
- **THEN** `encode (c₁ * c₂) (x₁, x₂)` roundtrips through `decode` to
  `((x₁, x₂), [])` whenever each component roundtrips.

### Requirement: Unbounded repetition is a total denotation

Unbounded repetition (`many`, paper §3.4) SHALL be realized as a total
least-fixpoint denotation with three separate interpretations, **not** as a
finite description value:

- `relRepeat (Rel p)` — the denotational relation (total for every step `p`),
  now over the length-indexed `Bytes n`;
- `decodeRepeat p h` — the productive decoder, well-founded on the input's
  length `n`, taking `h : ConsumesByte p` (each step consumes ≥ 1 byte) as its
  totality witness, over `Bytes n`;
- `encodeRepeat p` — the total encoder, structural on the value list, returning
  a `Bytes n` whose length is the sum of the element encodes.

#### Scenario: Productive repetition decodes in bounded steps

- **WHEN** `decodeRepeat p h (s : Bytes n)` is evaluated for a productive `p`
  (`Productive p`, equivalently `ConsumesByte p`)
- **THEN** it is a total function returning a finite list of
  `(value-list, remaining-buffer)` pairs in `n + 1` well-founded steps, each step
  consuming ≥ 1 byte of `s`, enumerating exactly the `relRepeat (Rel p)` results.

#### Scenario: Empty-matching repetition is genuinely infinite

- **WHEN** `p` matches the empty byte string (e.g. `pure ()`)
- **THEN** no finite decoder can enumerate all results (the value lists are
  unbounded: `relRepeat_unbounded_of_empty`), so `decodeRepeat` is defined only
  for productive `p` and never faked with a finite result.

#### Scenario: Repetition is over the single carrier

- **WHEN** `encodeRepeat p xs` and `decodeRepeat p h s` are called
- **THEN** both operate on the single length-indexed `Bytes` carrier; there is
  no transfer between a `List` spec and a slab run-model, and no `Classical.choice`
  enters the repetition laws.

### Requirement: The byte-predicate primitive `satisfy`

The core `Codec` SHALL provide `satisfy : (UInt8 → Bool) → Codec UInt8`, the
byte-token-with-guard. `satisfy p` relates a byte `b` to `single b` exactly when
`p b = true`; `decode` consumes one byte iff `p b`, else returns the empty list;
`encode` succeeds iff `p b`. It is the single substrate-touching leaf beyond
`byte`; no BE/LE/fixed-width/`varint`/text/tagged-sum constructor is added.

#### Scenario: A predicate byte decodes and encodes

- **WHEN** `satisfy p` is decoded on a leading byte `b` and encoded on a byte `b`
- **THEN** decode yields `b` iff `p b` (else no result) and encode yields the
  single byte iff `p b` (else `none`); the roundtrip holds `[propext, Quot.sound]`.

#### Scenario: A single digit is a valid decode

- **WHEN** `satisfy isHexDigit` decodes a single hex nibble
- **THEN** it succeeds for that one byte — the primitive does not force an even
  number of digits (grouping into pairs is a `count`/`iso` above the primitive).

### Requirement: Runs are derived, not constructors

Variable-length tokens (alphabet runs, varint, UTF-8, JSON string bodies) SHALL
be a maximal run of `satisfy p`, realized by the existing repetition layer
(`relRepeat`/`decodeRepeat`/`encodeRepeat`, exposed as the derived `takeWhile p`
run combinator), **not** a new `Codec` constructor. `many` is a derived recursive
combinator (paper §3.4), never an AST node.

#### Scenario: A varint is a run with a terminator

- **WHEN** a varint-like token is decoded
- **THEN** it is `takeWhile highBitSet` + an `iso` folding the 7-bit groups — the
  terminator is the first byte with the high bit clear, expressed as a run, not
  a per-byte lookahead.

### Requirement: Unbounded repetition is a derived run, surfaced as a first-class value

Unbounded repetition SHALL remain a **derived** run over the three already-defined
interpretations (`relRepeat (Rel p)`, `decodeRepeat p h`, `encodeRepeat p`), and
a concrete format SHALL surface it as a **first-class run value** (a structure
bundling the element description, its productivity witness, and the three
interpretations) rather than a bespoke per-format function. There SHALL be no
`many` constructor and no `decodeB32Strict`/`encodeB64Strict`-style leaf.

#### Scenario: A base is one run value, not three functions

- **WHEN** a base (e.g. base16, base64) is defined
- **THEN** it is a single run value whose decode is `decodeRepeat <elem> <witness>`
  and encode is `encodeRepeat <elem>`, with the laws inherited from
  `decodeRepeat_spec`/`encodeRepeat_rel` — the caller holds one value, never names
  `decodeB32Strict`.

#### Scenario: Repetition is not a constructor

- **WHEN** unbounded repetition is needed
- **THEN** it is the existing `relRepeat`/`decodeRepeat`/`encodeRepeat` (the paper's
  `many`, F\*'s `satisfy_many0`), **not** a `Codec.many` constructor — a
  constructor carries a denotational productivity witness that is not definable in
  Lean (definition-order cycle; rejected mutual-inductive universe mismatch).

### Requirement: Concrete formats are `Codec`-surfaced values (uniform `decode`/`encode`)

A concrete format SHALL be a value decoded/encoded by the single uniform
`Codec.decode` / `Codec.encode` — the _same two operations_ every `Codec` value
enjoys — never a bespoke per-format `encode`/`decode`/`rel`. There is **no**
`Base` enum and no `encode (b : Base)` / `decode (b : Base)` dispatcher: a
runtime radix selector is a bespoke function by another name, it erases the
value type (`UInt8` vs the padded bases' full-block/tail split), and it has no
client. The radix lives _in the value the caller already
holds_ (`hexElem` vs `b32BlockElem`), never on a dispatch index.

#### Scenario: base32/64 are values, not run triples

- **WHEN** base32/base64 are defined
- **THEN** each is a **composition** of a full-block `Run` (derived `many`) + a
  finite terminal-tail `Codec`, with the result `iso`-ed to the terminal-tail
  value type `B32`/`B64`; there is no `decodeB32Strict`/`encodeB64Strict`/
  `relB64Strict` triple to call. (There is **no** single `Codec B32`/`Codec B64`
  value: the `Codec` AST has no repetition node, and `many` is derived — the
  unbounded full-block prefix is the `Run`'s `decodeRepeat`/`encodeRepeat`, not an
  AST description.)

#### Scenario: No radix-dispatching facade

- **WHEN** a consumer encodes/decodes a value of some base
- **THEN** it calls `Codec.decode`/`Codec.encode` (or `decodeRepeat`/`encodeRepeat`
  for the run) on the base's own `Codec`/`Run` value — `Codec.decodeFull hexElem …`,
  `encodeB32 bs`, `decodeFullB64 s` — and the value type is `List UInt8` (the whole
  byte list), with `B32`/`B64` as the canonical block/tail spine used only to
  specify the full-block/tail split. There is **no**
  `encode (b : Base)` / `decode (b : Base)` and no `Base` inductive.
