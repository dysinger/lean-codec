# codec/axiom-gate Specification

## Purpose

Define the machine-enforced axiom discipline: every public theorem's axiom footprint
is checked on every build, so a `Classical.choice` regression fails the build rather
than being discovered later by a reader comparing prose against `#print axioms`.

## Requirements

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

### Requirement: An axiom exclusion is explicit and justified in place

The gate SHALL make the excluded set explicit rather than implicit. Every theorem
carrying `Classical.choice` that is knowingly excluded from the discipline — the
Layer-2 trust seams — SHALL be listed by name in the gate with the reason recorded
in place, so an exclusion is a decision on the record and never a silent omission.

An excluded law SHALL be described in prose as **excluded**, never as clean, and its
docstring SHALL state the measured footprint rather than an aspirational one.

#### Scenario: An exclusion is explicit and justified in place

- **WHEN** a Layer-2 seam's law is excluded from the `[propext, Quot.sound]`-only
  discipline
- **THEN** the gate lists that declaration by name with its measured footprint and
  the reason, so a reader can distinguish "excluded by decision" from "never
  checked".
