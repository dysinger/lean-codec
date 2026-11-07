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

The gate SHALL NOT describe a declaration as a law when the declaration is a
structure-field projection. A `Prop`-valued field of a structure is part of the type
a caller supplies, so gating it measures the structure's shape rather than any
behaviour; such fields SHALL be classified consistently — either all projected fields
are allowlisted with that reason, or all are described as law-shaped — and the gate's
documentation SHALL NOT argue, in one place, that gating them proves nothing while
gating them in another.

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

## ADDED Requirements

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
