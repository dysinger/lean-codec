## MODIFIED Requirements

### Requirement: A declared "free theorem" is either proved or withdrawn

Where documentation claims that a class of values inherits laws automatically — for
example that a derived combinator's laws follow definitionally from its primitives'
laws, or that an unconditionally-stated law therefore holds for it — that claim SHALL
be backed by the laws existing, or it SHALL be withdrawn.

The claim SHALL NOT rest on the laws being stated for a more general type: a law
proved by structural induction over a description does not automatically specialize
to a value whose structure is indexed by an unquantified parameter, and documentation
SHALL NOT imply that it does.

Where documentation advertises a law that is _stated in a weaker form than
advertised_ — a round-trip form where the prose promises a form at the caller's own
index, a specialised instance where the prose promises the general statement — either
the stronger statement SHALL be proved, or the advertisement SHALL be corrected to
describe exactly what is proved. This is the same defect as a false "free theorem":
the reader is told a law is available under a form the repository does not supply.

The converse SHALL also hold: where a law is specialised away from a general form
that is obtainable, the documentation SHALL state whether the general form is
provable, and SHALL NOT claim the specialisation is forced by a limitation that does
not exist.

#### Scenario: An unsupported "these follow for free" claim is corrected

- **WHEN** a module docstring states that the full laws hold for a family of derived
  values via a shared proof
- **THEN** either each value's characterization exists, so the claim is true, or the
  docstring states precisely which values are covered and which are not, and why.

#### Scenario: An advertised law is absent in the form advertised

- **WHEN** a docstring says a definition's law holds "at the caller's own index", or
  offers any specific form of the statement
- **THEN** that exact form is a theorem in the repository; if only a weaker or
  round-tripped form exists, the docstring states the form that exists.

#### Scenario: A specialisation's stated reason is checked against the general form

- **WHEN** a docstring justifies specialising a law to one instance by naming a
  limitation that prevents the general statement
- **THEN** the limitation is verified — by attempting the general statement or by
  inspecting the cited lemma's statement — and a specialisation whose general form is
  provable is documented as a convenience, not as a forced choice.
