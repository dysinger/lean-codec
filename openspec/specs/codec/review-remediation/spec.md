# codec/review-remediation Specification

## Purpose

Constraints that keep this repository's _proof and prose_ honest after a review
round: the build fails on an incomplete proof instead of merely warning; a rule a
future author needs is recorded once, at the point of use; documentation
distinguishes what it _quotes_ from what it _derives_; and agent-facing instructions
name the correct repository for each command. These are the requirements whose breach
is invisible to the compiler, which is why they are written down rather than assumed.

## Requirements

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

The **axiom half** of this gate SHALL be enforced on every build, not merely
runnable by hand. `#print axioms` being available to a reader does not satisfy this
requirement: a law whose footprint drifted to include `Classical.choice` would go
unnoticed until someone chose to check it. The repository SHALL therefore gate the
footprint of every public theorem automatically (see the `codec/axiom-gate`
capability), and SHALL NOT describe a law's axiom footprint in prose unless that
prose matches what the gate measures. Where a law is knowingly excluded from the
`[propext, Quot.sound]`-only discipline, the exclusion SHALL be recorded as an
exclusion — a measured footprint plus a reason — never as a claim of cleanliness.

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

#### Scenario: A documented axiom footprint matches the measurement

- **WHEN** a law's docstring or `README.md` states an axiom footprint
- **THEN** that statement matches what `#print axioms` actually reports for it, so a
  law carrying `Classical.choice` is never described as `[propext]`-only, and a law
  excluded from the discipline is described as excluded rather than clean.

#### Scenario: A claim of "proved" names a declaration that exists

- **WHEN** a docstring or a `README.md` section cites a declaration by name as
  authority for a claim (including in a departure/invariant anchor such as `[S3]`)
- **THEN** that name resolves to a real declaration in the same repository, so no
  text asserts a fact "proved as `X`" while `X` was never written and no anchor
  names a symbol that does not exist.

#### Scenario: A guaranteed behaviour names the theorem that guarantees it

- **WHEN** prose states that an input class is rejected, canonical, or otherwise
  guaranteed a property (for example that non-canonical encodings are refused)
- **THEN** that guarantee is stated by a theorem, or is explicitly described as
  unchecked; prose SHALL NOT claim a behaviour is guaranteed when only the
  mechanism that happens to produce it is present and no law pins it.

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

A verbatim quotation that elides intervening text SHALL mark the elision, so a
reader cannot mistake two non-contiguous fragments for one continuous passage.

A claim presented inside a paragraph introduced as an external source's own point
SHALL be that source's point. Where the project's own inference or measurement is
stated there, it SHALL be marked as the project's, and a claim that has not been
measured SHALL be marked unmeasured rather than stated as established.

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

#### Scenario: A spliced quotation marks its elision

- **WHEN** a passage quotes two non-contiguous fragments of one source passage
- **THEN** the elision is marked between them, so the reader can tell the two are
  not adjacent in the original.

#### Scenario: A project inference is not presented as the source's claim

- **WHEN** a paragraph introduced as an external source's admitted cost continues
  with the project's own account of where a cost falls, or with an unmeasured
  expectation about performance
- **THEN** that sentence is marked as the project's own and, if unmeasured, as
  unmeasured — the introduction's attribution does not carry over to it.

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

### Requirement: An ordering or implication claim between predicates SHALL be proved

Where documentation states that one predicate is stronger than, weaker than, or
implied by another — or that some witness cannot exist — that claim SHALL be a
theorem, or it SHALL be explicitly marked as unproven. Documentation SHALL NOT
advise a caller which hypothesis to discharge on the strength of an unproved
ordering, because the advice is what a downstream author will act on.

Where an ordering claim is found false, the repository SHALL record the
refutation as a theorem exhibiting the failure and SHALL correct the advice,
rather than deleting the claim: the sentence exists to steer a caller's proof
effort, and a deleted sentence leaves the steering to be re-derived wrongly.

"Marked as unproven" SHALL mean _open_ only when no theorem settles the question
either way. Where a refutation exists — in particular where a witness already in
the tree satisfies one predicate and violates the other — the claim SHALL be
recorded as refuted, and SHALL NOT be described as open. A claim of the form "no
theorem settles it either way" is itself falsifiable, and its falsity is a defect
of the same severity as a false theorem, because it tells a reader that a witness
is not worth hunting for when one is already present.

A predicate-ordering record SHALL state every edge of the family, not only the
edges that are proved, so that a reader can see which non-implications are known
to fail and which are genuinely unexamined.

#### Scenario: A predicate-ordering claim carries its proof or its caveat

- **WHEN** a docstring asserts that one hypothesis family implies, or is strictly
  stronger than, another
- **THEN** the implication is a theorem in the repository, or the assertion is
  marked unproven in place.

#### Scenario: A refuted ordering is corrected with a counterexample

- **WHEN** a documented ordering between two predicate families is found to be
  false
- **THEN** the repository contains a theorem exhibiting a member of one family
  outside the other, and the documentation states the measured relationship —
  including, where it applies, that the families are incomparable — so a caller is
  not advised to discharge a hypothesis that will not serve the law they need.

#### Scenario: An "open" claim is refuted rather than restated

- **WHEN** documentation records an implication as open, "neither proved nor
  refuted"
- **THEN** either no counterexample is exhibited anywhere in the tree, or the
  record is corrected to refuted with the counterexample named, because a witness
  satisfies one predicate and violates the other and a reviewer has found it.

#### Scenario: A non-implication is recorded even with productivity added

- **WHEN** two hypotheses are jointly needed by a law and a reader could reasonably
  expect one to imply the other once the law's third premise is supplied
- **THEN** the refutation SHALL be proved in the strengthened form — with that third
  premise added as a hypothesis — so the reader cannot attribute the failure to its
  absence.
