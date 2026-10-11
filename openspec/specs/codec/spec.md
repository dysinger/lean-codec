# codec Specification

## Purpose

`codec` is the byte codec capability: a `Codec` description (an inductive AST of
`iso`/`seq`/`alt`/`empty`/`pure`/`byte`) that gives one syntax description both a
decoder and an encoder over bytes, following Rendel & Ostermann's _Invertible
Syntax Descriptions_. The decoder is nondeterministic (backtracking union `|`),
unbounded repetition (`many`) is a well-founded, productive decoder over the
least-fixpoint relation `relRepeat`, and the bidirectional laws
(`decode_spec`, `encode_rel`, `roundtrip`) hold unconditionally with only
`[propext, Quot.sound]` as axioms and zero `sorry`.

## Requirements

### Requirement: correct, productive repetition decoder

The repetition (`many`) decoder SHALL be well-founded recursion on the consumed
byte string, never a fuel counter or a `Productive` precondition, and SHALL NOT
return wrong results for an empty-matching body.

#### Scenario: productive `many` is total and exact

- **WHEN** `p` consumes at least one byte per application (every `Rel p x s₁`
  has `s₁ ≠ []`)
- **THEN** `decode (many p) s` terminates and enumerates exactly the paper's
  results (`[]` and every non-empty prefix), e.g. `decode (many byte) [1,2,3]`
  = `[([],…), ([1],…), ([1,2],…), ([1,2,3],…)]`

#### Scenario: empty-matching `many` is genuinely infinite, stated as a fact

- **WHEN** `p` can match the empty string (`p = pure ()`)
- **THEN** `decode (many p) s` is recognized as non-terminating (infinitely many
  `[]` results) — asserted as a **theorem**, never faked with a finite result

#### Scenario: no fuel, no precondition, no new constructor

- **WHEN** the decoder is implemented
- **THEN** there is no fuel counter, no `Productive`/`AllProductive` predicate in
  the semantics, and no `Codec.many` constructor (`many` stays a derived
  combinator)

### Requirement: proved totality boundary

The library SHALL provide a theorem stating precisely where `decode (many p)`
terminates.

#### Scenario: totality theorem

- **WHEN** the change lands
- **THEN** there is a theorem: `decode (many p) s` terminates iff
  `∀ x s₁, Rel p x s₁ → s₁ ≠ []` — proved, not assumed

### Requirement: laws preserved unconditionally

The laws (`decode_spec`, `bidir`, `encode_rel`, `decode_encode`, `roundtrip`)
SHALL remain unconditional and SHALL be re-proved over the unchanged `Rel`, with
`#print axioms` = `[propext, Quot.sound]` and zero `sorry`.

#### Scenario: the `many` case is the least-fixpoint law, over unchanged `Rel`

- **WHEN** the change lands
- **THEN** the core `Rel` (the six constructors) is unchanged; the `many` case
  is realized by `relRepeat` (the least fixpoint) and `decodeRepeat_spec` (the
  `many`-case bidirectional law), and `#print axioms` on each law reports
  `[propext, Quot.sound]` with zero `sorry`.
