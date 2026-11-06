## MODIFIED Requirements

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
