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

A **completeness** claim behaves like a quotation claim and SHALL meet the same bar.
Where documentation says a list is "the full" list or "complete", the enumeration
SHALL match an environment walk rather than a textual search of definition headers,
because a search for a leading `def` misses multi-line signatures and cannot see
through an alias — the method, not only the number, is part of the claim.

A **figure stated to two derivations** SHALL be derived from figures measured in one
run. Where a quantity is obtained by subtracting two committed figures, both terms
SHALL come from the same table and the same session, and the text SHALL say which
table. This project has recorded three successive performance-figure defects of
exactly this shape — a subtraction across sessions that produces a number readable as
an improvement — and a section that forbids the practice in one bullet SHALL NOT
commit it in another.

A **signature quoted as the library's own** SHALL match a declaration that exists at
that type. A shorthand such as `decode (encode bs)` that resembles a total inverse
but corresponds to no declaration SHALL NOT be rendered inside backticks as if it
were one, and where a document forbids such a shorthand in one place it SHALL NOT use
it in another.

A claim about **why a declaration is kept** SHALL name a reason that holds. "It is
cited by anchor X" SHALL be checked against anchor X's text; where the anchor does not
in fact cite it, the justification is corrected or the declaration is deleted rather
than kept on a false footing.

#### Scenario: A completeness claim states how it was obtained

- **WHEN** documentation asserts that a list of declarations is complete
- **THEN** the enumeration matches a walk of the compiled environment, and the text
  states that it was obtained that way rather than by searching for a leading `def`.

#### Scenario: A derived figure uses one table and one run

- **WHEN** documentation derives a quantity by subtracting two committed figures
- **THEN** both figures appear in the same table, from the same session, and the text
  names that table, so a reader can reproduce the subtraction without crossing runs.

#### Scenario: A quoted signature matches a real declaration

- **WHEN** documentation presents an equation in backticks as the library's own
  statement of a law
- **THEN** the identifiers in it exist at those types; a shorthand that corresponds to
  no declaration is not rendered as if it did, and a document that forbids such a
  shorthand elsewhere does not use it.

#### Scenario: A retention reason names something that holds

- **WHEN** documentation justifies keeping a declaration by saying another document
  cites it
- **THEN** that other document does cite it, and the justification is corrected if it
  does not.
