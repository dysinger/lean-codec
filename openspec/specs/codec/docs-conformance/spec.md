# codec/docs-conformance Specification

## Purpose

The repository's statements about its own tree are treated as claims that can be wrong,
so the ones that can be generated are generated, the ones that cannot be attributed are
deleted, and the ones that describe how a check works are made to assert what they say.

## Requirements

### Requirement: A quoted output block is generated or it is deleted

Where the repository quotes the output of a command it runs — the gate's build log, a
`#print axioms` result, a version string — that quotation SHALL be produced by the run
it describes, not transcribed by hand.

A transcription of an asserted output is itself an unasserted number: the arm it quotes
can stay green while the quotation rots, which has happened in this repository. A quoted
block SHALL therefore either be generated from the same build that produces the asserted
counts, or be replaced by a pointer to the command.

#### Scenario: A hand-transcribed gate output goes stale

- **WHEN** a document quotes a gate's output lines and a later change moves an asserted
  count without regenerating the quotation
- **THEN** the build fails naming the discrepancy, rather than the document silently
  disagreeing with the gate it quotes.

#### Scenario: A range excludes its own derivation

- **WHEN** a document states an interval derived from two or more committed figures
- **THEN** each endpoint of the interval is recomputable from those figures by a command
  in the repository, and an endpoint that excludes its own derivation's value is a build
  failure.

### Requirement: A statement of a check's method matches the check

A sentence that describes _how_ a check works — its scope, its ordering, its comparison —
SHALL correspond to what the code does, and SHALL be either generated from the code or
backed by an assertion of the property it names.

Prose that names a method the code does not implement is the same defect as a false
theorem: the reader is told a guarantee exists. This SHALL NOT be closed by adding an arm
alone; the sentence and the code SHALL be made to agree, in one place.

#### Scenario: An ordering sentence is asserted by its effect

- **WHEN** documentation states that a matching list is consulted in a particular order
- **THEN** an assertion demonstrates that each entry in that list still produces its own
  result, so a reordering that changes the outcome is a build failure rather than a
  silently mis-labelled input.

#### Scenario: A scope word is checked against the environment

- **WHEN** documentation scopes a claim by a path, a namespace or a predicate ("every
  `Codec`/`Iso` theorem", "a `grep` of `Codec/`")
- **THEN** the claim's scope is either asserted from the environment the check actually
  walks, or the scope word is removed — because a scope whose stated path excludes the
  file that falsifies it is indistinguishable, to a reader, from a true claim.

### Requirement: A reviewer finding is resolvable from the repository

Where the source cites an external finding by identifier, the repository SHALL contain
the record that resolves it: at minimum, the finding itself, the evidence that established
it, and what closed it.

An identifier whose record lives only in a scratch directory is a citation to a file that
will not exist for the next reader, and a citation set whose identifiers collide resolves
to the wrong finding.

#### Scenario: A cited identifier has no record

- **WHEN** source or documentation cites a finding identifier that no repository file
  defines
- **THEN** the build fails naming the identifier.

#### Scenario: Two findings share an identifier

- **WHEN** two distinct findings are recorded under the same identifier
- **THEN** the build fails, so a citation cannot resolve to the wrong one.

### Requirement: A count in documentation is derivable by a command

A count stated in documentation — how many theorems, how many laws a family has, how many
projects of a kind — SHALL be either generated from the tree or accompanied by the command
that produces it.

A short list presented as an enumeration is a completeness claim, and a completeness claim
that no command produces fails silently: it is not wrong-looking, it is merely short.

#### Scenario: An enumeration is short by one

- **WHEN** documentation enumerates a set the tree also exposes ("the six law families",
  "the eight combinators")
- **THEN** either the count is derived from the tree at build time, or a command in the
  document reproduces it, so a missing member is visible to the reader who checks.
