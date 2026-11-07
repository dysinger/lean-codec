## MODIFIED Requirements

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
