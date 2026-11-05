# codec/law-coverage Specification

## Purpose

Guarantee that public surface carries proof: every public `def` a porter is told to
reproduce has a statement about it, or is explicitly on record as deliberately
lawless. The third audit found five of the eight `Codec` values the README presents
as "the bounded eight … a porter must have" had either no theorem at all or only a
degenerate case, while the module docstring claimed their characterizations were
free — so a downstream author was told a combinator came with theorems it did not
have.

## ADDED Requirements

### Requirement: A named public value has a characterizing law

Every public value the repository presents as part of its usable surface SHALL have
at least one theorem characterizing its meaning, and the characterizing law SHALL be
non-degenerate — it SHALL state the case in which the value's inductive or
compositional structure does the work, not only a base case that a reader already
knows.

A law whose only stated case is a base case SHALL NOT be presented, in prose or in
documentation, as if it characterized the value. Where a value's general law is not
proved, its documentation SHALL say so and SHALL name what is missing.

#### Scenario: A derived combinator's characterization is stated or declared missing

- **WHEN** a derived combinator (`seqRight`, `seqLeft`, `between`, `maybe`,
  `manyUpTo`, `count`, `optional`, `choice`) is presented to a reader as part of the
  usable surface
- **THEN** either its `Rel` characterization is proved, or its documentation states
  that the characterization is absent — it is never described as a definitional
  consequence that has not been written.

#### Scenario: A base-case-only law is not counted as coverage

- **WHEN** a value's only theorem states its degenerate case (for example a
  fixed-count repetition's law at count zero)
- **THEN** the repository does not present that value as having a characterizing
  law, and the missing general case is named as missing.

### Requirement: A declared "free theorem" is either proved or withdrawn

Where documentation claims that a class of values inherits laws automatically — for
example that a derived combinator's laws follow definitionally from its primitives'
laws, or that an unconditionally-stated law therefore holds for it — that claim SHALL
be backed by the laws existing, or it SHALL be withdrawn.

The claim SHALL NOT rest on the laws being stated for a more general type: a law
proved by structural induction over a description does not automatically specialize
to a value whose structure is indexed by an unquantified parameter, and documentation
SHALL NOT imply that it does.

#### Scenario: An unsupported "these follow for free" claim is corrected

- **WHEN** a module docstring states that the full laws hold for a family of derived
  values via a shared proof
- **THEN** either each value's characterization exists, so the claim is true, or the
  docstring states precisely which values are covered and which are not, and why.

### Requirement: Under-covered derived triples are completed or scoped

Where a family of related triples (a relation with its decoder and encoder) is
presented as having a uniform shape, and some members have a directional law that
others lack, the repository SHALL either supply the missing law or state the
asymmetry at the point where the uniform shape is claimed.

#### Scenario: A triple lacking its encoder-completeness half is named

- **WHEN** a relation/decoder/encoder triple is presented as having the same shape
  as a sibling triple that also proves encoder completeness
- **THEN** the missing half is either proved for it, or the documentation records
  which triples have it and which do not, so a consumer does not assume a guarantee
  it will not get.

### Requirement: Public surface with no proof is removed or justified

A public definition that no theorem mentions and no caller uses SHALL NOT remain
part of the repository's surface. It SHALL be either given a law that states what
its docstring advertises, or removed.

#### Scenario: A dead definition is resolved rather than left

- **WHEN** a public definition is found to have no theorem and no caller
- **THEN** the change either adds the law its docstring promises or deletes the
  definition, so a porter is not told to reproduce surface that carries no proof.
