# Spec Delta

## Purpose

Adopts the paper's API shapes (PAPER.md §4): `encode` is a partial function
(`Option` / the paper's `print :: … → Maybe String`), and `decode` is a
**single-valued** `Option` result (committed `|`, the paper's printer-side
`mplus`), not the paper's nondeterministic parser list. No error positions, no
new error type.

## MODIFIED Requirements

### Requirement: Nondeterministic (backtracking) decoding

Decoding SHALL be a **single-valued** partial function over the length-indexed
byte string, not a relation:

```
decode : Codec α → {n : Nat} → Bytes n → Option (α × Suffix n)
```

Choice (`|`) SHALL be **committed** (first success): `decode (d₁ | d₂) s` is
`decode d₁ s` when that returns `some`, and `decode d₂ s` otherwise. There is no
`List` of results, no backtracking union, and no `Functional`/`Unambiguous`
predicate in the public surface. The single `Bytes n` carrier is unchanged; a
Layer-2 fast path remains a proved-equal distinct-named surface, never
`decode`/`encode` themselves.

#### Scenario: Choice enumerates every branch

- **WHEN** `decode (d₁ | d₂) s` is evaluated
- **THEN** it returns `decode d₁ s` when that is `some`, and `decode d₂ s`
  otherwise — a single committed `some`/`none`, which (for a description whose
  branches are disjoint) picks the one that succeeds.

#### Scenario: The remaining buffer is length-indexed

- **WHEN** `decode c (s : Bytes n)` returns `some (value, remainder)`
- **THEN** `remainder : Suffix n` records the consumed length, and the byte string
  is the single `Bytes` carrier.

#### Scenario: A Layer-2 fast path does not displace the `Bytes n` substrate

- **WHEN** a distinct-named Layer-2 surface (e.g. `commitRemainder`, `decodeArrayFast`) carries data
  on `Array UInt8`/`ByteArray`
- **THEN** it is documented as proved (or definitionally) equal to `Bytes n`, never named
  `decode`/`encode`, and the `Bytes n` spec substrate remains the single denotation carrier; `decode`
  itself is unchanged.

### Requirement: Byte-exact roundtrip, unconditional

For every codec `c : Codec α` and every value `x : α` in `c`'s domain, encoding
then decoding SHALL reproduce the value and consume exactly the encoded bytes,
with the laws **unconditional**:

`encode c x = some ⟨n, s⟩ → decode c s = some (x, Suffix.empty n)`

and the converse `decode c s = some (x, Suffix.empty n) → encode c x = some
⟨n, s⟩` holds without any `Functional`/`Unambiguous` side-condition.

#### Scenario: Encode-then-decode returns the value

- **WHEN** `x` is in the codec's domain and `encode c x = some ⟨n, s⟩`
- **THEN** `decode c s = some (x, Suffix.empty n)` — the value plus an empty
  remaining buffer.

#### Scenario: The laws hold over choice

- **WHEN** a description contains `alt`
- **THEN** the bidirectional and roundtrip laws hold for it, with no prefix or
  unambiguity condition.

### Requirement: Partial encoding

Encoding SHALL be partial, matching the paper's `print :: Printer α → α → Maybe
String`: a codec returns `none` for a value outside its domain.

#### Scenario: Out-of-domain value

- **WHEN** `encode c x` is called with `x` outside `c`'s domain (e.g. `pure x₀`
  given `x ≠ x₀`, or `subset p` given `¬ p x`)
- **THEN** it returns `none`.

## ADDED Requirements

### Requirement: One description, two directions, one result shape family

The library SHALL provide exactly two operations — `encode`/`decode` — each
returning `Option`, the two doors of a single `Codec` description. A concrete
format SHALL be a `Codec` value (not a bespoke `encode`/`decode`), inheriting the
two operations from `codec`.

#### Scenario: A concrete codec is a `Codec` value

- **WHEN** a concrete format (e.g. `base16`, a fixed-width field) is defined
- **THEN** it is a `Codec …` value composed from `byte`/`seq`/`iso`/`alt`/`many`,
  and it uses the inherited `encode`/`decode` — it does not define its own
  `encode`/`decode` with a different return shape.

#### Scenario: A single result on both directions

- **WHEN** `encode c x` or `decode c s` is evaluated
- **THEN** each returns `Option` — `some` on success, `none` on failure — with no
  error position (a future change may add one to `decode` without touching
  `encode`).
