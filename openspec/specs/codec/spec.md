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
discarded.

#### Scenario: Optional bytes are preserved

- **WHEN** a description decodes a maximal run of bytes satisfying predicate `p`
  via repetition over a `subset p byte` step (denotation `relRepeat`, decoders
  `decodeRepeat`/`encodeRepeat`)
- **THEN** that exact run is part of the decoded value and is re-emitted byte-for-
  byte on encode.

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
