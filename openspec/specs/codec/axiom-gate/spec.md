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

No theorem SHALL be excluded from the axiom gate without an explicit, in-place
justification. A gate that silently skips a theorem is indistinguishable from a gate
that would have caught nothing.

Where the gate's footprint check declines to examine a claim, it SHALL report the
declined claims **decomposed by the reason for declining**, not as a single total. Two
declines with unrelated causes — a survey paragraph that names several other
declarations, and a claim with no resolvable owner at all — are different facts, and a
total that sums them cannot show that the second is rare or absent.

The footprint check SHALL state which kinds of declaration it examines and which it
does not, and the count it reports SHALL be described in those terms. A check scoped
to one `ConstantInfo` kind SHALL NOT be described as covering "every footprint claim",
because a declared footprint belongs to a docstring and docstrings are attached to
definitions too.

#### Scenario: An exclusion is explicit and justified in place

- **WHEN** a theorem is not covered by the footprint check
- **THEN** the reason is recorded next to it, so the exclusion is a decision.

#### Scenario: A footprint claim that overstates the axioms fails the build

- **WHEN** a docstring states a superset of the axioms a declaration actually depends on
- **THEN** the build fails naming the declaration and the two footprints.

#### Scenario: A footprint claim that understates the axioms fails the build

- **WHEN** a docstring states a subset of the axioms a declaration actually depends on
- **THEN** the build fails naming the declaration and the two footprints.

#### Scenario: A footprint stated for another declaration names it

- **WHEN** a docstring states a footprint for a declaration other than the one the
  docstring documents
- **THEN** the claim is attributed to the named declaration, and the arm does not
  silently count it against the wrong owner.

#### Scenario: Declined claims are reported by reason

- **WHEN** the footprint check skips a claim
- **THEN** the skip is counted under its cause, and a claim with no resolvable owner is
  its own reported number rather than part of a survey-paragraph total.

#### Scenario: The kind restriction is stated

- **WHEN** the footprint check examines only one constant kind
- **THEN** its reported counts say so, and a footprint claim attached to a definition
  is recorded as outside the check rather than as a claim that passed it.

### Requirement: The partition extends to public definitions, not only theorems

The axiom gate's universe SHALL be the public **theorems** _and_ the public
**definitions**, and a definition that no gated theorem names SHALL be a build
failure unless it is listed in a definition-surface allowlist with its reason in
place.

The check SHALL be documented as a **mention proxy**, and its documented property
SHALL be stated as the narrow one it has: no public definition can be covered by
silence. The documentation SHALL state that the proxy can be satisfied vacuously by
a theorem whose statement mentions the constant trivially, and SHALL NOT present the
check as a guarantee of law strength or as soundness.

The reported counts SHALL distinguish what the proxy measured from what it did not:
a definition named by a gated theorem's type SHALL NOT be described as "having a
stated law", because an identity unfold (`def f := g; theorem f_eq : f = g := rfl`)
satisfies the proxy while stating nothing about behaviour.

Every **name-based declination** that removes a definition from the gate's universe
SHALL itself be audited, on the same principle the theorem partition already
applies. A definition excluded because its name matches a compiler-machinery pattern
is not "mentioned" — it is outside the universe, which is indistinguishable to the
check from a definition that was never written. The gate SHALL therefore fail unless
every such excluded name appears in an allowlist with its reason in place, so that
removal from the universe is a recorded decision rather than a silent one. The
classifier's pattern list SHALL itself be verified: an entry that matches no
declaration, or one that removes authorial API, SHALL be a build failure rather than
an unexamined default.

The classifier's pattern list SHALL report its removals **decomposed by pattern**, not
as a single total. A total cannot distinguish a pattern that removes one declaration
by coincidence from one that removes ninety by design, and a pattern whose only match
is a single name is one rename away from matching nothing.

The gate SHALL NOT describe a declaration as a law when the declaration is a
structure-field projection. A `Prop`-valued field of a structure is part of the type
a caller supplies, so gating it measures the structure's shape rather than any
behaviour; such fields SHALL be classified consistently — either all projected fields
are allowlisted with that reason, or all are described as law-shaped — and the gate's
documentation SHALL NOT argue, in one place, that gating them proves nothing while
gating them in another.

Where a definition is removed from the universe by a **mention**-only path — an
allowlisted theorem whose statement names it — the gate SHALL account for that
naming explicitly rather than allowing the mention to discharge the definition
silently. A recursion principle that names its own function SHALL NOT be the only
reason that function is considered covered.

#### Scenario: A public definition with no law fails the build

- **WHEN** a public definition in the library namespace is named by no gated
  theorem's type and is absent from the allowlist
- **THEN** the build fails, naming the definition.

#### Scenario: A definition allowlisted with a reason passes

- **WHEN** a public definition is named by no gated theorem but appears in the
  definition-surface allowlist together with a reason it is not a law
- **THEN** the build passes, and the reason is readable in place next to the entry.

#### Scenario: The definition check finds the gaps the theorem partition cannot

- **WHEN** a public definition exists that the theorem partition cannot see,
  because the gate's theorem universe is `thmInfo` only
- **THEN** the definition check names it rather than staying green by omission.

#### Scenario: The reported counts do not overstate what the proxy measured

- **WHEN** the gate's header table reports how many definitions the check covers
- **THEN** the column describes a _mention_ rather than a characterized law, and the
  header names any definition whose only naming theorem is an identity unfold, so a
  reader cannot read the count as "this many definitions have real laws".

#### Scenario: A name-based exclusion cannot hide a definition from the gate

- **WHEN** a public definition is excluded from the gate's universe because its name
  matches a compiler-machinery pattern, and it appears in no allowlist
- **THEN** the build fails naming it, so the exclusion is a recorded decision rather
  than a silent gap the check cannot report.

#### Scenario: A classifier entry that matches nothing fails the build

- **WHEN** a compiler-machinery pattern in the classifier matches no declaration in
  the environment, or matches an authored declaration
- **THEN** the build fails and names the pattern, so the classifier cannot rot into a
  list of defaults that quietly removes API from the check.

#### Scenario: A pattern's removals are reported individually

- **WHEN** the gate prints how many declarations the classifier removed
- **THEN** the count is decomposed per pattern, so a pattern that removes exactly one
  declaration is a reviewed decision rather than a coincidence nothing notices.

#### Scenario: A recursion principle does not cover its own function

- **WHEN** a function's definition-coverage is satisfied only by an allowlisted
  theorem that names the function, and that theorem is the function's own recursion
  principle
- **THEN** the gate records the naming explicitly rather than counting it as coverage,
  so the proxy's vacuous-satisfaction mode cannot be reached through the recursion
  principle.

#### Scenario: A reason citing a declaration resolves

- **WHEN** an allowlist entry's reason names a declaration as its supporting evidence
- **THEN** that name resolves in the environment, so the voucher for the exemption is
  findable rather than a stale spelling.

#### Scenario: A projection of a hypothesis is distinguished from a theorem application

- **WHEN** a gated theorem's body applies a constant whose arguments include a
  caller-supplied hypothesis
- **THEN** the classification considers what the constant is applied to, so a law whose
  body unwraps a proved theorem is not reclassified as a mere projection of a
  hypothesis.

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

### Requirement: A structure-field projection is not reported as a law

Where the gate covers a `Prop`-valued structure field by name, its documentation
SHALL describe it as a projection of a type the caller supplies rather than as a
theorem the package proves, and the classification SHALL be uniform across fields of
that shape: a field of the same kind SHALL NOT be gated in one place and allowlisted
as "not a theorem" in another.

A structure-field projection SHALL NOT be counted as evidence that a definition has a
characterised law, and it SHALL NOT be counted as a law for the purpose of any
diagnostic that infers "this is a restatement" from an empty axiom footprint. An empty
footprint SHALL be described as consistent with a restatement, never as its signature:
`#print axioms` reporting no axioms is neither necessary nor sufficient for a
declaration being an identity, and the gate SHALL NOT name a declaration as vacuous on
that basis without `#print`ing its body.

The structural test for "this declaration's body is a projection" SHALL recognise a
projection **wherever Lean elaborates one**, not only where it elaborates to
`Expr.proj`. A projection out of a conjunction or an equivalence elaborates to a
constructor **applied to an argument** (`And.left hal`, `Iff.mp h`), which is a
constant application and not a structure projection node; a test that matches only
`Expr.proj` therefore cannot see this whole class. The gate SHALL decide the
classification of such a body by structure, and a `Prop`-shaped projection of a
caller-supplied hypothesis SHALL NOT be gated as a law.

#### Scenario: The same field shape is classified the same way everywhere

- **WHEN** two `Prop`-valued structure-field projections are both visible to the gate
- **THEN** both are either allowlisted with the "part of the type a caller supplies"
  reason or both are documented as law-shaped, and the gate's prose does not assert
  that covering them proves nothing while covering one of them.

#### Scenario: An axiom footprint does not identify a restatement

- **WHEN** the gate's documentation characterises a declaration as a restatement
  because its axiom footprint is empty
- **THEN** that characterisation is backed by the declaration's own body being an
  identity (`#print`), and the documentation does not present the empty footprint as a
  signature of vacuity, because honest laws of a definitional equality also have an
  empty footprint.

#### Scenario: A projection of a conjunction is recognised as a projection

- **WHEN** a gated theorem's body is the first or second conjunct of its own hypothesis,
  or an implication direction out of an equivalence the caller supplied
- **THEN** the structural test reports it as a projection, and the gate classifies it
  with the other projections rather than pinning its footprint as a law.

### Requirement: A completeness claim over the gate's universe is checked, not grepped

Where documentation states that a list of declarations is **complete** — "the full
list", "every value in the tree is one of these", "exactly two others" — that
enumeration SHALL be produced by walking the compiled environment, and the stated
count SHALL match the walk. A claim of completeness SHALL NOT rest on a textual search
of definition headers, because a search for a leading `def` misses declarations whose
signatures span lines and cannot see through a type alias.

The documentation SHALL distinguish a list of values a porting reader must reproduce
from an enumeration of every value the tree contains. Where the two differ, the
difference SHALL be stated rather than resolved by calling the shorter list complete:
values that exist only as counterexample witnesses are part of the environment and are
not part of the reproduction surface.

#### Scenario: A "complete inventory" is falsified by the environment

- **WHEN** documentation calls a table of definitions the complete inventory for a
  type, and walking the environment finds a public definition of that type in no row
- **THEN** the claim is a defect, and the table is restated to name the list's actual
  scope (what a porter must reproduce) or extended to cover every value.

#### Scenario: An enumeration claim states how it was obtained

- **WHEN** documentation asserts a count of declarations of some shape
- **THEN** the count comes from an environment walk and the text says so, rather than
  citing a pattern search that a multi-line signature or an alias defeats.

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

The rule SHALL apply to **every** name list that re-admits a declaration the
classifier would otherwise remove, not only to lists of projections. An exemption list
that names an authored law carrying a generated-looking suffix is a list of one, and
it SHALL be checked in both directions: the name exists, it is gated, and the suffix
rule would have removed it. A rename or an unrelated theorem sharing the exempted
suffix is otherwise accepted by every arm at once.

An allowlisted declaration that carries a non-empty axiom footprint SHALL NOT be
allowlisted as "not a law". A footprint is evidence that the declaration's proof
consults an axiom, which a bare structure projection never does; so a footprinted
entry in a "not a law" group is either a mis-filed law or a mis-stated reason, and
the gate SHALL report the footprint of every allowlisted theorem rather than
presuming the group is empty-footprinted.

#### Scenario: A name that does not have the list's property fails the build

- **WHEN** a name is added to a list whose entries are claimed to share a structural
  property, and that name does not have the property
- **THEN** the build fails naming it, so the list cannot accumulate exemptions that are
  not exemptions.

#### Scenario: The prose matches the mechanism

- **WHEN** a gate's documentation says an invalid entry in a list "would fail"
- **THEN** an arm exists that fails on such an entry; if it does not, the sentence is
  corrected to describe what is actually checked.

#### Scenario: An authored-suffix exemption is checked in both directions

- **WHEN** a name is exempted from the classifier's suffix rule because it is an
  authored law that the rule would wrongly remove
- **THEN** the build asserts the name exists, is gated, and would have been removed by
  the suffix rule alone, so the exemption invalidates itself when either side changes.

#### Scenario: An allowlisted law with a footprint is not filed as "not a law"

- **WHEN** an allowlisted theorem's footprint is non-empty
- **THEN** the gate reports it, so an entry whose stated reason is "this is not a law"
  cannot carry a proof that consults an axiom unnoticed.

#### Scenario: A predicate used by two arms has one definition

- **WHEN** two arms must classify the same declarations by the same structural property
- **THEN** both call one named definition, and a comment asserting they share it is
  backed by their sharing it rather than by prose.

### Requirement: A stated measurement is a measurement, or it is a classification

Every allowlist entry SHALL carry either a measurement supporting its reason or an
explicit statement that it was classified without one. A reason written as an assertion
("this restates its own definition") SHALL NOT be presented in the register of a
measured fact unless a check or a `#print` of the body supports it.

Where a group of entries shares one prose reason that is a claim about content, the
documentation SHALL say whether that claim was verified for the group, sampled, or
assumed, so a reader can tell a measured exemption from a name-based one.

A **derived interval** SHALL be a measurement in the same sense. Where documentation
states a range whose endpoints are obtained from committed figures — an interval of
per-step costs, a quotient's span, a spread — each endpoint SHALL be recomputable from
those figures, and an interval that excludes a value it was derived from SHALL NOT stand.
Padding a single measurement until it covers a second one produces an interval whose
stated width is not evidence, and it SHALL be corrected to the values themselves rather
than widened.

#### Scenario: Content claims are marked as unverified or backed

- **WHEN** an allowlist group's reason asserts something about the entry's content
  rather than its shape
- **THEN** the reason records whether that was verified, and by what, or states plainly
  that the entry is classified by name and checked only for existence.

#### Scenario: A range excludes the value it was derived from

- **WHEN** documentation states an interval whose endpoints come from two committed
  measurements, and one endpoint excludes its own derivation's value
- **THEN** the interval is a defect: it is corrected to the values, and it is not
  "qualified" by prose, because a padded range is indistinguishable from a measured one
  to every reader who does not re-derive it.

#### Scenario: A range is reproduced by a command

- **WHEN** a document states a derived interval
- **THEN** a command in the repository reproduces both endpoints from the committed
  figures, so the interval is checkable by the reader it warns.

### Requirement: A figure is committed only with the run that produced it

A numeric cell in a performance table SHALL be either printed by a named lane in a
committed run or marked as absent. A cell that no lane emits SHALL be removed rather
than carried, because a number a reader cannot reproduce is indistinguishable from a
number that was never measured.

Where a cell's value cannot be derived from any other committed cell in the same table,
that is evidence it came from a different session or was transcribed; the cell SHALL be
dropped rather than qualified.

The same discipline SHALL apply to a count that a **build-time check** reports. Every
diagnostic arm SHALL report two quantities: the **denominator** — the universe of
declarations its claim is about — and the **removals** it made from that universe,
decomposed by the reason for each removal. A bare total SHALL NOT be accepted as a
report: an arm that prints how many items it examined, without printing how many items
the claim is about, cannot be distinguished from an arm that examined nothing, and a
single removal count covering several unrelated causes cannot show that any one of those
causes is rare or absent.

Both quantities SHALL be asserted, so that a narrowing of the walk or a widening of a
filter is a build failure rather than a smaller number in a log. Where the gate's
documentation enumerates an arm's reported numbers it SHALL say which are asserted and
which are printed-only, because a number that cannot fail the build is weaker evidence
than one that can. Where an arm cannot state a denominator it SHALL record that fact and
its reason in place, so that "no denominator" is a decision on the record rather than an
omission.

This SHALL apply to an arm whose input is a **call-site list in prose** as much as to one
whose input is an environment walk: a completeness claim about how many call sites,
declarations or claim sites exist SHALL be obtained by enumeration, and an enumeration
SHALL NOT be written from memory.

A **quotation of an assertable output** SHALL be treated as a figure. Where documentation
reproduces the lines a check prints, the reproduction SHALL be generated by the run it
quotes, because a hand-transcribed output is an unasserted number that rots while the
check it quotes stays green.

#### Scenario: An underivable cell is dropped

- **WHEN** a per-step cell in a table cannot be reproduced from any committed row of
  that table, and the table's caption says all its cells come from one session
- **THEN** the cell is removed and the row points at the lane that prints the number it
  actually measures.

#### Scenario: The count a check reports has a denominator

- **WHEN** a build-time check reports how many items it examined
- **THEN** it also reports how many items were candidates, or otherwise distinguishes
  "checked and correct" from "not checked at all", so a narrowed scope is visible.

#### Scenario: Removals are decomposed by cause

- **WHEN** an arm removes items from its input for more than one reason
- **THEN** each reason's count is reported separately, so a removal that should be
  rare or absent can be seen to be so.

#### Scenario: A printed-but-unasserted number is described as such

- **WHEN** the gate's documentation enumerates an arm's reported numbers
- **THEN** it says which are asserted and which are printed-only.

#### Scenario: A prose enumeration is obtained by enumeration

- **WHEN** a task, comment or docstring claims how many call sites, declarations or
  claim sites exist
- **THEN** the count came from a command whose output is quoted, not from recall.

#### Scenario: A quoted gate output drifts from the gate

- **WHEN** a document reproduces the lines a check prints, and a later change moves an
  asserted count without regenerating the reproduction
- **THEN** the build fails, because the reproduction is a figure and is subject to the
  same rule as a table cell.
