## ADDED Requirements

### Requirement: The numeric codec's value type is a number, not a byte list

The package SHALL provide a decimal codec whose value type is a **number**, not a
byte list. A byte array is an acceptable intermediate representation inside the
implementation, but it SHALL NOT be the type the caller receives: a caller asking for
base-10 decoding is asking for a number, and a byte array obliges them to
re-implement the arithmetic the package exists to provide.

The encoder SHALL emit the **minimal** numeral and SHALL NOT zero-pad to a block
width: `enc 0 = "0"`, `enc 1 = "1"`, `enc 10 = "10"`. Zero SHALL NOT encode to the
empty byte string.

The isomorphism's codomain SHALL be the **quotient of concrete syntax by
information-free variation** — canonical numerals — rather than a bare fixed-length
byte string. A bare `Bytes n` admits `"001"`, a well-formed three-byte string that
names no distinct value, and an isomorphism including it has a false law at that
element.

#### Scenario: The encoder emits minimal digits

- **WHEN** a number is encoded
- **THEN** the result is its minimal decimal numeral — `0` becomes `"0"`, `1`
  becomes `"1"`, `10` becomes `"10"` — with no padding to a block width and no
  empty encoding for zero.

#### Scenario: The codomain carries canonicity, not just length

- **WHEN** the isomorphism's codomain is chosen
- **THEN** it is not a bare `Bytes n`, because `"001"` is a well-formed three-byte
  string that names no distinct value; a codomain admitting it makes the law false
  at that element rather than merely unproved.

### Requirement: Information-free variation is normalised, not rejected

Some spellings of a numeral differ only in content that carries no numeric
information: leading whitespace, a redundant leading zero, the all-blank run.
`"1"`, `"01"` and `"   1"` all name the same value. These SHALL be treated as **one
phenomenon** — lax names for the single canonical image — and SHALL NOT be treated as
a second image, nor as an error.

The numeric decoder SHALL return the same value for every such spelling, so
`decode "1" = decode "01" = decode "   1" = some 1`, while the encoder emits `"1"`.
The number is isomorphic to its canonical numeral; the lax spellings are resolved
_before_ the isomorphism is consulted, so it remains a total bijection with an
unconditional law.

**The variation set is per base, and the bases SHALL be allowed to differ.** Which
spellings are information-free depends on the alphabet, not on a global rule:

- a leading zero is inert wherever the digits are a bare numeral (decimal, and the
  fixed-width bit groupings of bases 2/4/8/16/32/64), because it adds no digit;
- a **base prefix** (`0x`, `0o`, `0b`) is a different question: it names the base
  rather than padding within one, so whether it is absorbed, required, or rejected
  is a decision per base and SHALL NOT be inherited from the decimal rule;
- in the C-family `0`-prefix idiom a leading zero _changes the base_ of the literal
  (`017` is octal), so the package SHALL NOT silently apply the decimal leading-zero
  rule to a base where a caller could read it as a radix marker.

Each base's normaliser SHALL state its own variation set, and the package SHALL NOT
present one base's normalisation policy as another's.

Only input that names nothing SHALL be rejected: the empty string, and any byte that
is neither a decimal digit nor an absorbed blank. Rejection SHALL NOT be used as the
mechanism for resolving a non-canonical spelling, and leading zeros SHALL NOT be
given a different treatment from leading whitespace.

#### Scenario: Every spelling of a numeral decodes to its value

- **WHEN** the numeric decoder is given `"1"`, `"01"`, `"   1"`, or `"007"`
- **THEN** it returns the same value in every case — `some 1` for the first three,
  `some 7` for the last — and a theorem records that the spellings agree.

#### Scenario: Only unreadable input is rejected

- **WHEN** the numeric decoder is given the empty byte string, or a numeral
  containing a byte that is neither a decimal digit nor an absorbed blank
- **THEN** it returns `none`, because there is no value the input could name; this
  is the only rejection, and a leading zero or a leading blank is never a reason for
  one.

#### Scenario: The quotient, not the law, carries the equivalence

- **WHEN** the acceptance of `"01"` or `"   1"` is justified
- **THEN** the justification is that the codomain is the quotient of concrete syntax
  by information-free variation, so those spellings are not elements of it and the
  law is never consulted at them — never that the inverse law was relaxed.

### Requirement: The normaliser is one total idempotent function, proved

The layer that resolves non-canonical spellings SHALL be a single **total,
idempotent** normaliser absorbing every information-free variation at once, not one
normaliser per spelling class, not a second codec, and not a relaxed law. It SHALL be
shown to reach every canonical form from every spelling, so no input is left without
a reading, and SHALL be shown to be the identity on canonical forms, so the layer
composition is well defined.

Whether a lax spelling is accepted SHALL be a property of this layer, above the
isomorphism. A codec value carrying two laws — one for canonical and one for lax
input — SHALL NOT be constructed, because the second law contradicts the first.

The normaliser's limit SHALL be stated: a spelling differing in _length_ from its
canonical form is not expressible by a trimmer, so the layer absorbs variation in
content, not "anything".

#### Scenario: The normaliser agrees with the isomorphism on canonical input

- **WHEN** the numeric decoder is given a numeral the encoder produced
- **THEN** it returns the value the isomorphism gives, and this agreement is a
  theorem rather than a restatement — the path normalises and then defers.

#### Scenario: Octal and hexadecimal may normalise differently from decimal

- **WHEN** the leading-zero policy for a non-decimal base is chosen
- **THEN** it is decided per base and recorded, because a `0x`/`0o`/`0b` prefix names
  a radix rather than padding a numeral, and in the C-family idiom a leading zero
  changes the base of a literal; one base's policy SHALL NOT be applied to another
  without that decision being made and stated.

#### Scenario: One normaliser absorbs every variation

- **WHEN** leading whitespace and leading zeros are both present (`"   01"`)
- **THEN** a single normalisation pass reaches the canonical numeral, so the layers
  do not have to be applied in a caller-visible order.

#### Scenario: The normaliser reaches every canonical form

- **WHEN** an arbitrary byte sequence is passed through the normaliser
- **THEN** it produces a canonical numeral (a total surjection onto the canonical
  forms), so no input is silently left undecodable for want of a normal form.

#### Scenario: Normalisation does not weaken the inverse law

- **WHEN** the normalising decoder accepts a spelling the encoder never produces
- **THEN** the isomorphism's inverse law is unchanged, because the normalisation is
  composed outside it.
