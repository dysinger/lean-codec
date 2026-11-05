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
