# Spec Delta — `codec/review-remediation`

## ADDED Requirements

### Requirement: The proof gate SHALL be enforced, not observed

The repository SHALL fail its build when a proof is incomplete. A `sorry` in any
library source SHALL cause the `check` gate to fail; the gate SHALL NOT rely on a
human noticing a compiler warning. Because `lake build` reports `sorry` as a
warning rather than an error, the gate SHALL add an explicit enforcement step
(turning warnings into errors, or scanning the sources for `sorry`/`admit`) and
SHALL be documented as _enforced_ only once that step exists. Documentation SHALL
NOT describe an invariant as "the proof gate" when the build does not check it.

The gate's axiom check SHALL be runnable inside this repository. A documented
`#print axioms` example SHALL name a `lean-codec` declaration and be executable
here, not only in a downstream repository.

#### Scenario: A stubbed theorem fails the build

- **WHEN** any theorem in `Codec/` or `Codec.lean` is replaced by `sorry`
- **THEN** the `check` gate fails (non-zero), and the failure names the
  declaration or at least the file, so the gate cannot go green with an
  incomplete proof.

#### Scenario: The documented axiom check runs in-repo

- **WHEN** a reader follows the documentation's "check one law by hand" recipe
- **THEN** the commands reference a `lean-codec` declaration
  (`#print axioms Codec.roundtrip`) and the repository's own toolchain, and they
  succeed from a clean checkout.

### Requirement: A proof ergonomics rule SHALL be recorded where it is consulted, once

A `Classical.choice`-leak rule that the project has verified SHALL be recorded in
the proof-ergonomics guidance a reader consults when a law is dirty, together with
a reproducing probe and the clean alternative. The same fact SHALL NOT be kept in
two places in mutually inconsistent states; if a change history mentions it, that
mention SHALL defer to the ergonomics entry rather than restate a partial version.

The catalogue SHALL include all verified leak shapes, at minimum:
(1) a dependent `cases`/`match` on a term whose length equation is in context;
(2) `decide_eq_true` applied to an `omega` proof of a **disjunction**;
(3) a `match` on a `Bool` occurring in the goal.

#### Scenario: A disjunctive `omega` proof is flagged

- **WHEN** a law's proof closes a `decide (A ∨ B) = true` goal via
  `decide_eq_true (by omega)`
- **THEN** the guidance identifies this as a `Classical.choice` leak source and
  prescribes building the disjunct explicitly (`Or.inl`/`Or.inr`) so that `omega`
  only closes the arithmetic leaf.

#### Scenario: The catalogue has one home

- **WHEN** the leak catalogue is consulted or amended
- **THEN** there is exactly one authoritative list of shapes, and any other
  mention (a change's history, a changelog) points at it instead of holding a
  divergent copy.

### Requirement: Documentation SHALL distinguish quoted from derived claims

Where the project cites an external source, a verbatim quotation SHALL be
faithful to that source, and any _reason_ the project gives for a design decision
SHALL be independently correct — a correct quotation does not license an incorrect
derivation. Where two design entries describe the same declaration's guarantee,
they SHALL agree; a contradiction between entries SHALL be resolved rather than
left for the reader to arbitrate.

A departure entry SHALL be classified as a departure only if the observable
semantics change; an entry whose body describes a superset or an unchanged
behaviour SHALL be filed as a strengthening or removed.

#### Scenario: A quotation is accurate but its gloss is not

- **WHEN** a design entry quotes a source correctly but attributes a mechanism to
  it that the source does not state
- **THEN** the entry is a defect even though the quotation checks out, and it is
  corrected to state the mechanism the source actually gives.

#### Scenario: Two entries contradict each other on one declaration

- **WHEN** one entry calls a declaration's law unconditional and another records
  a domain restriction or witness precondition for that same declaration
- **THEN** the two entries are reconciled so that the precondition is stated once
  and neither entry's guarantee is overstated.

### Requirement: Agent operating instructions SHALL name the correct repository for each command

An instruction file that covers more than one repository SHALL group its commands
by repository, so a reader running the recipe top-to-bottom cannot execute a
command against the wrong tree. Every command SHALL be valid in the repository it
is attributed to. A rule forbidding a practice (e.g. long foreground builds) SHALL
not be immediately contradicted by the example offered for entering the
environment.

A cross-repository failure mode that is not self-explanatory SHALL be recorded
with its symptom, cause, and fix, so that a future reader does not "fix" the wrong
file.

#### Scenario: A recipe spanning two repositories is unambiguous

- **WHEN** an instruction file documents verification steps for more than one
  repository
- **THEN** each step appears under a heading naming its repository, and a step
  that must run in a different tree is marked as such inline.

#### Scenario: A confusing cross-repo failure has a recorded diagnosis

- **WHEN** a build fails because a dependency's pinned revision predates a module
  that the source imports
- **THEN** the instructions record the symptom, the diagnostic (the pinned
  revision in the lockfile), and the fix (advance the input and re-resolve), and
  explicitly warn against editing the importing source instead.
