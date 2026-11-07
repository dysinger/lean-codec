## ADDED Requirements

### Requirement: Every constant kind in the gate's namespace is either gated or counted

The gate SHALL define what it means by its universe for **every** `ConstantInfo`
constructor, not for the two it happens to walk. Where a constant kind is deliberately
excluded from the gated set — `opaque` and `axiom` declarations have no proof body to
footprint-check — the gate SHALL count the excluded constants and **print the count**,
so "zero" is a measurement rather than an absence.

A constant kind that is in neither the gated set nor a printed count SHALL be treated
as a hole in the gate, because an authored `opaque` is a law-shaped claim and is
invisible to every arm. The exclusion list SHALL NOT be the mechanism that hides such
a constant: an exclusion is for a measured departure from the axiom discipline, not for
a constant the universe never enumerated.

#### Scenario: An unexamined constant kind is reported

- **WHEN** a constant in the gated namespaces has a kind the gate does not walk
  (`opaque`, `axiom`)
- **THEN** the build prints how many such constants exist, so a non-zero count is
  visible without reading the source, and the header's statement that the universe is
  "every constant in the namespace" is either true or explicitly qualified.

#### Scenario: A deliberate exclusion is a count, not a silence

- **WHEN** a constant kind is excluded from footprint checking by design
- **THEN** the gate states that decision and prints the number of constants affected,
  rather than omitting the kind from the walk and leaving it unreported.

### Requirement: A gate name-list asserts the property it exists to represent

Where a gate maintains a list of names whose entries are justified by a _structural_
property — "these are all structure-field projections", "these all come from the
compiler" — the build SHALL assert that each listed name actually has that property.
A list audited only for absence of stale entries is audited in one direction; the
other direction is where a non-qualifying name enters silently and stops being
checked.

A docstring claim that a list is audited SHALL correspond to an arm that audits it. A
list whose only check is "the name still exists" SHALL be described as such, and not as
one whose "invalid entries would fail".

#### Scenario: A name that does not have the list's property fails the build

- **WHEN** a name is added to a list whose entries are claimed to share a structural
  property, and that name does not have the property
- **THEN** the build fails naming it, so the list cannot accumulate exemptions that are
  not exemptions.

#### Scenario: The prose matches the mechanism

- **WHEN** a gate's documentation says an invalid entry in a list "would fail"
- **THEN** an arm exists that fails on such an entry; if it does not, the sentence is
  corrected to describe what is actually checked.

### Requirement: A stated measurement is a measurement, or it is a classification

Every allowlist entry SHALL carry either a measurement supporting its reason or an
explicit statement that it was classified without one. A reason written as an assertion
("this restates its own definition") SHALL NOT be presented in the register of a
measured fact unless a check or a `#print` of the body supports it.

Where a group of entries shares one prose reason that is a claim about content, the
documentation SHALL say whether that claim was verified for the group, sampled, or
assumed, so a reader can tell a measured exemption from a name-based one.

#### Scenario: Content claims are marked as unverified or backed

- **WHEN** an allowlist group's reason asserts something about the entry's content
  rather than its shape
- **THEN** the reason records whether that was verified, and by what, or states plainly
  that the entry is classified by name and checked only for existence.

### Requirement: A figure is committed only with the run that produced it

A numeric cell in a performance table SHALL be either printed by a named lane in a
committed run or marked as absent. A cell that no lane emits SHALL be removed rather
than carried, because a number a reader cannot reproduce is indistinguishable from a
number that was never measured.

Where a cell's value cannot be derived from any other committed cell in the same table,
that is evidence it came from a different session or was transcribed; the cell SHALL be
dropped rather than qualified.

#### Scenario: An underivable cell is dropped

- **WHEN** a per-step cell in a table cannot be reproduced from any committed row of
  that table, and the table's caption says all its cells come from one session
- **THEN** the cell is removed and the row points at the lane that prints the number it
  actually measures.

#### Scenario: The count a check reports has a denominator

- **WHEN** a build-time check reports how many items it examined
- **THEN** it also reports how many items were candidates, or otherwise distinguishes
  "checked and correct" from "not checked at all", so a narrowed scope is visible.
