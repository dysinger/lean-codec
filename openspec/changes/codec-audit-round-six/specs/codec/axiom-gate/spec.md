## MODIFIED Requirements

### Requirement: An axiom exclusion is explicit and justified in place

The gate SHALL make the excluded set explicit rather than implicit. Every theorem
carrying `Classical.choice` that is knowingly excluded from the discipline — the
Layer-2 trust seams — SHALL be listed by name in the gate with the reason recorded
in place, so an exclusion is a decision on the record and never a silent omission.

An excluded law SHALL be described in prose as **excluded**, never as clean, and its
docstring SHALL state the measured footprint rather than an aspirational one.

**A stated footprint is a claim, and a claim SHALL be checked like any other.** Where
a declaration's docstring states an axiom footprint — "axiom-free", "no axioms at
all", "`[propext]`-only", "`[propext, Quot.sound]`-only" — the build SHALL compare
that statement with the footprint the environment reports and SHALL fail, naming the
declaration and both values, when they differ. The comparison SHALL run in both
directions: a claim that is **too strong** (an "axiom-free" declaration that is not)
and one that is **too weak** (a "`[propext, Quot.sound]`-only" declaration that uses
fewer axioms) SHALL both be build failures, because the weaker claim understates a
result the file elsewhere treats as evidence and the stronger one is a false
statement of measurement.

The stated footprint SHALL be written from the measurement, not from inspection of
the statement or the proof script. No syntactic property of a theorem's statement
SHALL be treated as predicting its footprint: a declaration whose statement mentions
the byte substrate may be axiom-free and one whose statement is a bare `↔` between
two definitions may report `propext`. An authored rule from statement shape to
footprint SHALL NOT be recorded, because such a rule is falsifiable and has been
falsified.

Where a docstring discusses the footprint of a **different** declaration (a survey, a
comparison, a table), the claim SHALL name the declaration it describes, so that the
check can attribute it. A docstring that states a footprint without saying whose
SHALL NOT be read as a claim about the declaration it is attached to.

#### Scenario: An exclusion is explicit and justified in place

- **WHEN** a Layer-2 seam's law is excluded from the `[propext, Quot.sound]`-only
  discipline
- **THEN** the gate lists that declaration by name with its measured footprint and
  the reason, so a reader can distinguish "excluded by decision" from "never
  checked".

#### Scenario: A footprint claim that overstates the axioms fails the build

- **WHEN** a declaration's docstring states that it is axiom-free and the
  environment reports that it depends on `[propext, Quot.sound]`
- **THEN** the build fails naming the declaration, the stated footprint and the
  measured one.

#### Scenario: A footprint claim that understates the axioms fails the build

- **WHEN** a declaration whose docstring states `[propext, Quot.sound]`-only is
  measured to depend on no axioms, or on `[propext]` alone
- **THEN** the build fails naming both values, because the understatement is a
  measurement claim that is untrue and hides the stronger result.

#### Scenario: A footprint stated for another declaration names it

- **WHEN** a docstring surveys or tabulates the footprints of several declarations
  rather than its own
- **THEN** each claim names the declaration it describes, so that a stated
  footprint can be attributed and checked rather than silently misattributed to the
  declaration the docstring is attached to.

## ADDED Requirements

### Requirement: An exclusion list cannot rot without a build failure

The gate's exclusion list SHALL be checked for staleness on the same principle it
already applies to the allowlist: a name listed as excluded SHALL be a public
theorem that exists, and a name that does not SHALL be a build failure. An exclusion
is a measured footprint plus a reason; an entry that names nothing is an
unfalsifiable claim and would let a later reader believe a law was measured when it
was not.

The gate SHALL also verify that an excluded name is **actually outside** the
discipline, so that an exclusion cannot be used to un-gate a law that is already
clean. An exclusion whose declaration reports only `[propext, Quot.sound]` or fewer
axioms SHALL be a build failure rather than a silent un-gating.

#### Scenario: A stale exclusion fails the build

- **WHEN** the exclusion list names a declaration that is not a public theorem in
  the environment (a rename or a deletion)
- **THEN** the build fails naming it, so the list cannot rot into a snapshot of a
  past tree.

#### Scenario: Excluding a clean law fails the build

- **WHEN** a declaration on the exclusion list is measured to depend only on
  `[propext, Quot.sound]` or fewer axioms
- **THEN** the build fails, because an exclusion is reserved for a measured
  departure and using it on a clean law is un-gating by silence.

### Requirement: A gate branch that cannot fail is not a check

Where the gate computes a boolean condition intended to catch an inconsistent
count, that condition SHALL be capable of being true for some input. A condition
that is arithmetically false for every input — an identity such as
`a - b + b ≠ a`, or a comparison of a quantity with itself — SHALL NOT be presented
as a consistency check, because it reads in the source exactly like the live
checks beside it while enforcing nothing.

Where such a branch is found, it SHALL be replaced by the condition the table it
guards actually requires, so that the named inconsistency is the one detected. A
check whose comment names one identity and whose expression names a different one
SHALL be a defect.

#### Scenario: A dead consistency branch is replaced

- **WHEN** a gate's count check is written so that it is false for every possible
  pair of counts, including the inconsistent ones it claims to detect
- **THEN** it is a defect, and the branch is rewritten to compare the sum of the
  parts against the total, so that an inconsistency is the thing that fires.

#### Scenario: Text matching in a gate is robust to legal spellings

- **WHEN** a gate counts occurrences of a construct by comparing whole lines of
  source text
- **THEN** it accounts for the legal spellings of that construct — a trailing
  comment, the tactic on a shared line, an inline `by` form — or it is replaced by a
  comparison that cannot be evaded by formatting, so that the count it asserts is
  the count the source contains.
