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
`decode`/`encode` (or the facade `decode (b : Base)` / `encode (b : Base)`),
never a bespoke per-format `encode`/`decode`/`rel`.

#### Scenario: base32/64 are values, not run triples

- **WHEN** base32/base64 are defined
- **THEN** each is a run value over the terminal-tail value type `B32`/`B64`
  (realized via `iso`); there is no `decodeB32Strict`/`encodeB64Strict`/
  `relB64Strict` triple to call.

#### Scenario: The facade dispatches over one value type

- **WHEN** a consumer encodes/decodes a value of some base
- **THEN** it calls `encode (b : Base)` / `decode (b : Base)`, which `cases` over
  the base and applies the uniform operation to the base's run value — the radix
  lives on the `Base` index, never on a bespoke function name.
