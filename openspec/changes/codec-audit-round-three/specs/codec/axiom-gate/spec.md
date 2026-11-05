# codec/axiom-gate Specification (delta)

## MODIFIED Requirements

### Requirement: The axiom footprint of every public theorem is checked on every build

The repository SHALL contain an in-repo axiom gate that collects the axiom
footprint of every public theorem and fails the build when any theorem depends on
an axiom outside `[propext, Quot.sound]`. The gate SHALL run as part of the default
`lake build` target, so no consumer can compile the library unguarded.

The gate SHALL NOT be a separate manual step, a documentation recipe, or a lint a
reader is asked to remember to run. It SHALL be a compiled artifact whose
`#guard_msgs` (or equivalent) blocks make a regression a build error.

The gate's coverage SHALL be a **complete partition** of the public theorems, not a
filter over them: every public theorem SHALL be either footprint-checked or listed
by name in an explicit allowlist of compiler-generated declarations, and the build
SHALL fail when a theorem is in neither. A declination mechanism that can drop an
authored law by matching its name alone SHALL NOT be the sole authority, because
such a mechanism can silently un-gate a law a human wrote.

The allowlist SHALL record, in place, the reason each entry is not a law. Where an
entry is a structure field rather than a compiler-generated auxiliary, the reason
SHALL say so, since a field is part of a type a caller supplies rather than a
theorem proved about it.

#### Scenario: A `Classical.choice` regression fails the build

- **WHEN** any theorem in the gaited set comes to depend on `Classical.choice` — for
  example because a definition it cites is reimplemented through a classical decision
- **THEN** `lake build` fails non-zero and names the offending declaration, so the
  regression cannot reach a green build.

#### Scenario: The gate is load-bearing, not decorative

- **WHEN** a theorem's footprint is deliberately perturbed (a cited definition
  swapped for one that reaches classical logic)
- **THEN** the gate fails, demonstrating that it observes the compiler's actual axiom
  set rather than a hand-maintained list that could drift.

#### Scenario: The gate covers newly added theorems by default

- **WHEN** a new public theorem is added to `Codec/`
- **THEN** it enters the gaited set without anyone editing the gate, so coverage is a
  property of the mechanism rather than of a list someone remembers to update.

#### Scenario: A theorem whose name matches a compiler-generated pattern is still gated

- **WHEN** an authored theorem's name ends in one of the patterns the gate uses to
  recognise compiler-generated auxiliaries (for example a law named
  `…eq_irrel`, or one whose last component is `dec`)
- **THEN** the build either gates it or fails because it is neither gated nor
  allowlisted — it is never silently omitted, so a name collision cannot un-gate a
  law a human wrote.

#### Scenario: A theorem in neither set fails the build

- **WHEN** a public theorem is neither footprint-checked nor in the
  generated-declaration allowlist
- **THEN** `lake build` fails and prints that theorem's name, so the gate cannot go
  green while a law is covered by neither path.

#### Scenario: A theorem in both sets fails the build

- **WHEN** a declaration appears both in the gated set and in the allowlist
- **THEN** `lake build` fails, because the two sets are required to partition the
  public theorems and an overlap makes the gate's own record self-contradictory.

## ADDED Requirements

### Requirement: The partition extends to public definitions, not only theorems

The gate's universe SHALL include public `def`s, not only public theorems. A public
`def` with no proof about it is a hole of the same kind as an un-gated law, and it
SHALL be covered by the same partition: every public `def` in the gated namespaces
SHALL either be mentioned by the statement of at least one gated theorem, or be
listed by name in an explicit definition-surface allowlist with a recorded reason.
The build SHALL fail when a public `def` satisfies neither condition, printing the
name.

Because "has a law" is not decidable, the mechanism SHALL check the decidable proxy
— whether a gated theorem's _type_ mentions the definition — and the gate's
documentation SHALL state that this is a proxy, so it is never read as a guarantee
that the law is strong. The proxy's guarantee is that no public definition can be
covered by _silence_, which is the failure mode the partition exists to prevent.

#### Scenario: A public definition with no law fails the build

- **WHEN** a public `def` is added to `Codec`/`Iso` and no gated theorem mentions it
- **THEN** `lake build` fails and prints the definition's name, so it cannot ship as
  public surface with no statement about it.

#### Scenario: A definition allowlisted with a reason passes

- **WHEN** a public `def` is deliberately shipped without a law (for example a
  convenience alias) and is listed in the definition-surface allowlist with a reason
- **THEN** the build passes, so the decision to omit a law is on the record rather
  than an accident.

#### Scenario: The definition check finds the gaps the theorem partition cannot

- **WHEN** the definition check is first run against the existing tree
- **THEN** it names every public `def` with no gated law — the derived
  combinators among them — so the enumeration is performed by the mechanism rather
  than by a reviewer reading the source.

### Requirement: The reported footprint distribution is generated, not remembered

The gate's header SHALL report the axiom-footprint distribution of the gated set,
and that distribution SHALL be produced by the generator from the environment it
compiled, rather than transcribed by hand. A hand-written table can drift from the
body it summarizes without any check noticing, because the partition and coverage
checks compare set membership and not counts.

#### Scenario: The reported counts match the body

- **WHEN** the generated body and the header's footprint table are compared
- **THEN** the per-footprint counts agree, because both are emitted by the same
  generation step rather than one being maintained alongside the other.
