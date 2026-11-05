# codec/review-remediation Specification (delta)

## MODIFIED Requirements

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

## ADDED Requirements

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
