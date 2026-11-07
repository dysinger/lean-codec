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
reader cannot mistake two non-contiguous fragments for one continuous passage. A
sentence that puts a **paraphrase** inside quotation marks, or attributes to the
source a claim the source states in a weaker form ("the invariant holds only modulo
equivalence classes" for a source that says it will "sometimes interpret this
condition modulo equivalence classes"), SHALL be corrected to quote what the source
says and to state the project's reading outside the quotation.

A claim presented inside a paragraph introduced as an external source's own point
SHALL be that source's point. Where the project's own inference or measurement is
stated there, it SHALL be marked as the project's, and a claim that has not been
measured SHALL be marked unmeasured rather than stated as established.

A **completeness** claim behaves like a quotation claim and SHALL meet the same bar.
Where documentation says a list is "the full" list or "complete", the enumeration
SHALL match an environment walk rather than a textual search of definition headers,
because a search for a leading `def` misses multi-line signatures and cannot see
through an alias — the method, not only the number, is part of the claim.

**A completeness claim that is also an arithmetic claim SHALL have arithmetic that
closes.** Where a document states a total and then enumerates the parts it is
composed of, the parts SHALL sum to the total, and a reader SHALL be able to check
that without consulting the tree. A total that is correct while its stated
decomposition is not SHALL be treated as a defect in the claim, not as a rounding
difference: it is the shape that survives a correction, because the number looks
right and only the sum is wrong.

A **figure stated to two derivations** SHALL be derived from figures measured in one
run. Where a quantity is obtained by subtracting two committed figures, both terms
SHALL come from the same table and the same session, and the text SHALL say which
table. This project has recorded three successive performance-figure defects of
exactly this shape — a subtraction across sessions that produces a number readable as
an improvement — and a section that forbids the practice in one bullet SHALL NOT
commit it in another.

A **per-step or per-element figure** SHALL state the span it was divided by, and
that span SHALL be the one its own row used. Where a table's caption gives one span
for all rows and a row was measured over a different span, the row's figure is wrong
by the ratio of the two spans, and a reader who divides by the caption gets a number
that contradicts the row. The span SHALL be given per row, or the caption SHALL
name which rows differ.

A **signature quoted as the library's own** SHALL match a declaration that exists at
that type. A shorthand such as `decode (encode bs)` that resembles a total inverse
but corresponds to no declaration SHALL NOT be rendered inside backticks as if it
were one, and where a document forbids such a shorthand in one place it SHALL NOT use
it in another. A **fully-qualified name** SHALL resolve: a name invented by prefixing
a module name onto a constant whose namespace does not include it (`Codec.Sound.…`
for a constant declared as `Codec.…` in that file) does not exist, and SHALL NOT be
presented as a citation a reader can check.

A **cross-reference** SHALL resolve. An intra-document link whose anchor matches no
heading is a promised section the document does not contain, and SHALL be corrected
or removed.

A claim about **why a declaration is kept** SHALL name a reason that holds. "It is
cited by anchor X" SHALL be checked against anchor X's text; where the anchor does not
in fact cite it, the justification is corrected or the declaration is deleted rather
than kept on a false footing.

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

#### Scenario: A completeness claim states how it was obtained

- **WHEN** documentation asserts that a list of declarations is complete
- **THEN** the enumeration matches a walk of the compiled environment, and the text
  states that it was obtained that way rather than by searching for a leading `def`.

#### Scenario: A completeness total and its decomposition agree

- **WHEN** documentation states a total count and then names the parts that make it
  up
- **THEN** the parts sum to the total, so a reader can verify the arithmetic without
  re-walking the environment, and a total that is right while its parts are not is
  treated as a defect.

#### Scenario: A derived figure uses one table and one run

- **WHEN** documentation derives a quantity by subtracting two committed figures
- **THEN** both figures appear in the same table, from the same session, and the text
  names that table, so a reader can reproduce the subtraction without crossing runs.

#### Scenario: A per-step figure uses the span of its own row

- **WHEN** documentation presents a per-step figure in a table whose caption states a
  single burst span for every row
- **THEN** either every row was measured over that span, or the row's own span is
  given, so that dividing the row's time by the caption's span cannot produce a
  number contradicting the row.

#### Scenario: A quoted signature matches a real declaration

- **WHEN** documentation presents an equation in backticks as the library's own
  statement of a law
- **THEN** the identifiers in it exist at those types; a shorthand that corresponds to
  no declaration is not rendered as if it did, and a document that forbids such a
  shorthand elsewhere does not use it.

#### Scenario: A cited name resolves in the environment

- **WHEN** documentation cites a declaration by a fully-qualified name and invites
  the reader to check it
- **THEN** that name resolves, and a name constructed from a file name rather than a
  namespace does not — the citation is corrected to the constant the environment
  actually exports.

#### Scenario: A cross-reference resolves

- **WHEN** documentation links to a section by anchor
- **THEN** the anchor matches a heading in the same document, so the link is not a
  promise of a section the document does not contain.

#### Scenario: A retention reason names something that holds

- **WHEN** documentation justifies keeping a declaration by saying another document
  cites it
- **THEN** that other document does cite it, and the justification is corrected if it
  does not.
