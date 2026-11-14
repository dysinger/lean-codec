# Spec Delta — `basen`

## ADDED Requirements

### Requirement: A numeral denotes a number

`basen` SHALL provide a radix-generic conversion between a numeral — a sequence of digit
bytes — and the number it denotes, as **one** definition serving all seven radices rather
than a per-base derivation.

The layer SHALL consist of a digit-value function, a fold from a digit sequence to a
`Nat`, and its inverse producing canonical digits. The fold SHALL be the value of the
numeral: `toNat b ds` is `Σ dᵢ · bⁱ` over the digits in most-significant-first order, and
the seven per-base alphabets SHALL be proved-equal specialisations of the single
digit-value function rather than independent copies.

A digit byte that is not in the radix's alphabet SHALL yield `none`, and a sequence
containing one SHALL NOT be convertible. Conversion SHALL be total on valid digit
sequences, including the empty sequence, which denotes zero only if the radix's own
canonical spelling for zero is the empty sequence — that decision SHALL be stated once and
applied uniformly.

#### Scenario: A numeral converts to its value

- **WHEN** the generic fold is applied to a valid digit sequence in a given radix
- **THEN** the result is the number that numeral denotes, so that base-10 `"300"` yields
  `300` and base-2 `"01100001"` yields `97`.

#### Scenario: One digit-value function serves every radix

- **WHEN** any base's own digit-value function is inspected
- **THEN** it is proved equal to the generic function at that radix, so no base carries an
  independent alphabet definition that could disagree with the generic one.

#### Scenario: An out-of-alphabet digit is rejected

- **WHEN** the fold is applied to a sequence containing a byte outside the radix's alphabet
  (the digit `"9"` in radix 8, or `"G"` in radix 16)
- **THEN** the result is `none`, and it is not partially converted.

### Requirement: A number is its canonical numeral modulo information-free variation

`basen` SHALL provide, for each radix, a total bijection between `Nat` and the **quotient**
of the radix's numeral syntax by the information-free variation — leading zeros and leading
whitespace. This SHALL be an ordinary `Iso` whose inverse law holds **unconditionally**;
the equivalence SHALL live in the codomain (the quotient type), never as a weakened law.

The normaliser SHALL be one total, idempotent function, and every lax spelling of a number
SHALL reach the same canonical form through it. A spelling that names no number — the empty
input where the radix has no empty-zero convention, a trailing non-digit, a digit outside
the alphabet — SHALL be rejected rather than normalised.

The canonical digits SHALL be minimal: no leading zeros, and zero itself spelled by the
radix's own single zero digit rather than by the empty sequence or by a padded form.

#### Scenario: Three spellings are one value

- **WHEN** the same number is presented as its canonical numeral (`"7"`), with leading zeros
  (`"007"`), and with leading whitespace (`"  7"`)
- **THEN** all three normalise to the same canonical form and decode through the iso to the
  same `Nat`, because the law is a bijection on the quotient and not a relaxed relation on
  the raw syntax.

#### Scenario: A spelling that names nothing is rejected

- **WHEN** input contains a character that is not in the radix's alphabet, or carries
  trailing data after a valid numeral
- **THEN** normalisation rejects it and no `Nat` is produced — a trimmer is not "accepts
  anything".

#### Scenario: Encoding a number yields minimal digits

- **WHEN** a `Nat` is encoded to digits in a given radix
- **THEN** the result has no leading zeros, and zero encodes to that radix's single zero
  digit.

#### Scenario: A lax spelling does not have its own image

- **WHEN** the iso is stated over raw digit syntax rather than over the quotient
- **THEN** that is a defect: `"007"` and `"7"` would have no common image and the inverse
  law would be false, not merely unproved. The codomain SHALL be the quotient, and a
  three-spelling witness SHALL exist and be mutation-tested.

### Requirement: The block isomorphisms are proved equal to the generic fold

Each existing per-base block isomorphism — which maps a fixed-size group of digit bytes to
one byte or block — SHALL be proved equal to the generic radix fold restricted to that
group. The block isomorphisms SHALL be retained as fast paths rather than deleted, and the
equality SHALL be a theorem, so that the two derivations cannot drift apart.

The generic fold SHALL NOT be applied across the padded bases' terminal-tail layer: base 32
and base 64 carry padding inside their value type, and a numeral has no such notion. The
equality covered by this requirement is over the block layer only.

#### Scenario: A block iso agrees with the fold

- **WHEN** a block of `k` digits is converted by a base's block isomorphism and by the
  generic fold restricted to those `k` digits
- **THEN** the two agree, by a proved theorem, so a change to either is a build failure
  rather than a silent divergence.

#### Scenario: The equality is mutation-tested

- **WHEN** a block isomorphism's digit order is perturbed
- **THEN** the proved-equality theorem fails, demonstrating that it constrains the block
  iso and is not satisfied vacuously.

#### Scenario: Padding is not read as a numeral

- **WHEN** a padded base-32 or base-64 encoding is converted to a number
- **THEN** that composition is out of scope for this requirement; the block-only equality
  does not license folding a terminal-tail spine, and no theorem claims it does.
