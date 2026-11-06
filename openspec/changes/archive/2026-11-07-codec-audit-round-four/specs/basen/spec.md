## MODIFIED Requirements

### Requirement: The conformance laws are gated like the roundtrip laws

Every new canonical/ rejection/ converse/ injectivity theorem SHALL be provable
with only `propext` and `Quot.sound`, zero `sorry`, no `Classical.choice`, and
SHALL be covered by a bench-lane vector (an `example` or `#eval`) so the gate
exercises them, matching the F* reference's `decode_*_invalid` vector set.

The gate's coverage SHALL be a property of the mechanism, not of a list a
maintainer remembers to update. The package SHALL contain a build-time check over
the compiled environment that fails the build — printing the offending name — when
a public theorem is not gated, and when a pinned name has no matching theorem. A
gate whose population depends on remembering to add a line SHALL NOT be described
as covering the package's laws: it covers exactly the laws someone listed, and one
added theorem makes that claim false without any build failing.

The gate SHALL partition **definitions** as well as theorems: the package's gate
SHALL match the dependency's, so that a public definition named by no theorem is a
build failure unless listed with a reason. A gate that partitions theorems only
leaves a public definition invisible — neither gated nor computed — and a definition
that no theorem and no proof line consumes is then dead surface that the gate cannot
report.

The gate's **prose** SHALL be gated too. Where the gate's module documentation states
counts, those counts SHALL be asserted by a build-time check, or the prose SHALL be
deleted. A header table that is asserted while the paragraph beside it is remembered
is not gated: the paragraph can be falsified by a regeneration that updates the table
and leaves the prose stale, with every check green.

#### Scenario: The gate covers the new laws

- **WHEN** `lake build` and `#print axioms` run on the conformance laws
- **THEN** the build has zero `sorry`/warnings, `#print axioms` reports only
  `[propext, Quot.sound]` for each new theorem, and the bench lane value-checks
  each rejection/canonical vector byte-for-byte.

#### Scenario: A law added without a gate entry fails the build

- **WHEN** a public theorem is added to a `BaseN` module and no corresponding
  footprint check is added
- **THEN** `lake build` fails and prints that theorem's name, so the gate cannot go
  green while a law is unchecked.

#### Scenario: A stale gate entry fails the build

- **WHEN** a pinned name in the gate has no matching theorem in the environment
  (a rename, or a deletion)
- **THEN** `lake build` fails naming it, so the gate cannot rot into a snapshot of a
  past tree.

#### Scenario: A public definition with no law fails the build

- **WHEN** a public `BaseN` definition is named by no gated theorem's type and is
  absent from the definition-surface allowlist
- **THEN** `lake build` fails naming it, matching the behaviour the `codec`
  dependency already has.

#### Scenario: Gate prose stating counts is asserted, not remembered

- **WHEN** the gate's module documentation states how many theorems are pinned,
  allowlisted, or total
- **THEN** a build-time check compares those figures with the compiled environment,
  or the prose is removed, so a stale paragraph cannot survive a regeneration.

#### Scenario: The gate's error messages are arithmetically true

- **WHEN** a gate check reports counts in a message
- **THEN** any equation it prints holds of the sets it names, rather than combining
  figures from two different sets into one line.
