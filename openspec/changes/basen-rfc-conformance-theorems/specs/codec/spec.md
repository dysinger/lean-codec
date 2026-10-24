# Spec Delta

## Purpose

Re-assert the uniform-`decode`/`encode` surface without a `many` constructor.
Unbounded repetition (`many`, paper §3.4) is a **derived** recursive combinator —
never an AST node — and the concrete bases are decoded/encoded by the _single_
`Codec.decode` / `Codec.encode` through a first-class **run value** that bundles
the proved repetition interpretations, so a consumer never names a per-format
decoder.

This corrects no _requirement_ in the synced `codec` spec but tightens its
"Unbounded repetition" section, which already states repetition is `relRepeat`/
`decodeRepeat`/`encodeRepeat` (not a finite description value). It records that
this is the **right** reading (the paper/F\* both derive `many`), and that a
`many` constructor is not merely "not a finite description" but is
**un-implementable** in Lean (a `Productive`/`ConsumesByte` field creates the
`Codec → witness → Rel → Codec` definition-order cycle, and the mutual-inductive
escape is rejected by the `Type 1`-vs-`Prop` universe check).

## ADDED Requirements

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
value type (`UInt8` vs `B32`/`B64`) that carries the unrepresentable-illegal-state
guarantee, and it has no client. The radix lives _in the value the caller already
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
  `encodeB32 bs`, `decodeFullB64 s` — and the value type is the base's natural
  type (`UInt8` for fixed-width, `B32`/`B64` for padded). There is **no**
  `encode (b : Base)` / `decode (b : Base)` and no `Base` inductive.
