## ADDED Requirements

### Requirement: The numeric codec's value type is a number, not a byte list

The package SHALL provide a decimal codec whose value type is a **number**, not a
byte list. A byte array is an acceptable intermediate representation inside the
implementation, but it SHALL NOT be the type the caller receives: a caller asking
for base-10 decoding is asking for a number, and a byte array obliges them to
re-implement the arithmetic the package exists to provide.

The encoder SHALL emit the **minimal** numeral and SHALL NOT zero-pad to a block
width: `enc 0 = "0"`, `enc 1 = "1"`, `enc 10 = "10"`. Zero SHALL NOT encode to the
empty byte string.

The strict isomorphism's codomain SHALL carry canonicity rather than mere length,
because a bare fixed-length byte string admits `"001"` — a well-formed three-byte
string that names no distinct value — and an isomorphism including it has a false
law at that element.

#### Scenario: The encoder emits minimal digits

- **WHEN** a number is encoded
- **THEN** the result is its minimal decimal numeral — `0` becomes `"0"`, `1`
  becomes `"1"`, `10` becomes `"10"` — with no padding to a block width and no
  empty encoding for zero.

#### Scenario: The codomain carries canonicity, not just length

- **WHEN** the strict isomorphism's codomain is chosen
- **THEN** it is not a bare `Bytes n`, because `"001"` is a well-formed three-byte
  string that names no distinct value; a codomain admitting it makes the inverse
  law false at that element rather than merely unproved.

### Requirement: A leading zero is rejected, not read

The strict decoder SHALL reject a numeral with a redundant leading zero (`"01"`,
`"007"`) and SHALL reject the empty input, because the encoder never produces
either. A leading zero carries no numeric information — `"01"` and `"1"` name the
same value — so a decoder accepting both while the encoder emits one makes the
inverse law a **false** proposition rather than an unproved one. Padding is not
whitespace and does not get ignored: the strict reader accepts exactly the
encoder's image.

A single codec value that both accepts a non-canonical spelling and claims the
canonical one is the only encoding SHALL be treated as a defect, not as an
untested edge case, because the two claims contradict each other and no proof work
reconciles them.

#### Scenario: The strict decoder rejects a leading zero

- **WHEN** the strict decoder is given a numeral with a redundant leading zero
  (`"01"`, `"007"`)
- **THEN** it returns `none`, and a witness theorem records that rejection, so a
  decoder that later accepts the input fails the build rather than silently
  falsifying the inverse law.

#### Scenario: The strict decoder rejects the empty input

- **WHEN** the strict decoder is given an empty byte string
- **THEN** it returns `none`, because the encoder never produces it — zero encodes
  as `"0"`, not as nothing.

### Requirement: Tolerant input is a separate layer, outside the isomorphism

Where a caller must accept a non-canonical spelling, the package SHALL supply it as
a **lenient** decoder that trims the spelling first and then defers to the strict
one, proved to agree with it on canonical input, and composed **outside** the strict
isomorphism. The package SHALL NOT satisfy a request for tolerant input by
relaxing the strict inverse law instead.

The two decoders SHALL be distinguishable by name and SHALL NOT be conflated into
one codec value carrying two laws, because whether a lax spelling is accepted is a
property of the layer above the isomorphism, not of the isomorphism.

Leniency SHALL be bounded honestly: a normaliser that trims leading zeros cannot
express a lax spelling differing in _length_ from its canonical form, so the
tolerant layer is a trimmer, not an equivalence-class quotient.

#### Scenario: The lenient decoder agrees with the strict one on canonical input

- **WHEN** the lenient decoder is given a numeral the encoder produced
- **THEN** it returns the same value as the strict decoder, and this agreement is a
  theorem rather than a restatement — the lenient path normalises and then defers.

#### Scenario: Leniency does not weaken the inverse law

- **WHEN** the lenient decoder accepts a spelling the encoder never produces
- **THEN** the strict codec's inverse law is unchanged, because the normalisation
  is composed outside the isomorphism.

#### Scenario: The normaliser's limit is stated

- **WHEN** the tolerant layer is documented
- **THEN** it states which lax spellings it cannot express — those differing in
  length from the canonical form — so a reader cannot take "lenient" to mean
  "accepts anything".
