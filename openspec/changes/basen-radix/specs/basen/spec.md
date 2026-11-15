# Spec Delta — `basen`

## ADDED Requirements

### Requirement: A numeral denotes a number

`basen` SHALL provide a radix-generic conversion between a numeral — a sequence of digit
bytes — and the number it denotes, as **one** definition serving all seven radices rather
than a per-base derivation.

The layer SHALL consist of a digit-value function, a fold from a digit sequence to a
`Nat`, and its inverse producing canonical digits. The fold SHALL be the value of the
numeral: `toNat b ds` is `Σ dᵢ · bⁱ` over the digits in most-significant-first order, for
**`2 ≤ b ≤ 64`** — a bound the requirement states rather than leaving to a signature,
because `b = 1` is not a positional radix and `ofNat 1` has no canonical finite numeral.

The seven per-base digit-value functions SHALL be proved equal to the single digit-value
function at their radix — the **decode** direction. **The encode direction is not unified**:
radix 2's inverse map (`valToBit`) carries a deliberately non-injective fallback and SHALL NOT
be rewritten. At radices 4 and 8 the inverse maps are `48 + d` and **injective**, so an
agreement law is provable there and is a bonus rather than an obligation. (An earlier draft
said "radices 2, 4 and 8", which is false of 4 and 8.)

A digit byte that is not in the radix's alphabet SHALL yield `none`, and a sequence
containing one SHALL NOT be convertible. The empty sequence SHALL NOT be the canonical
spelling of zero at any radix: `ofNat b 0` is the base's single zero digit, so `toNat b []`
is `none` and `toNat b` of the zero digit is `some 0`.

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
whitespace. This SHALL be an ordinary `Iso` whose inverse law holds **unconditionally on the quotient**;
the equivalence SHALL live in the codomain (the quotient type), never as a weakened law.
The passage from a lax spelling to the quotient is the normaliser's job, and its totality and
idempotence are a **separate** obligation from the `Iso`'s law, not a hypothesis on it.

The normaliser SHALL be one total, idempotent function, and every lax spelling of a number
SHALL reach the same canonical form through it. A spelling that names no number SHALL be rejected rather than normalised: the empty input,
a **trailing blank** (`"7 "`, which is not part of a numeral), a trailing non-digit, and a
digit outside the alphabet. Leading blanks (`"  7"`) and leading zeros (`"007"`) are accepted;
trailing ones are not.

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

#### Scenario: Three spellings reach one quotient element

- **WHEN** `"7"`, `"007"` and `"  7"` are each pushed through the normaliser
- **THEN** the three resulting quotient elements are equal — a theorem, not a comment — so
  the law's `iff` has one image to work with rather than three. Stated as the effect because
  a sentence forbidding the raw-syntax form would be a rule about how to write the code,
  which is not observable behaviour.

### Requirement: The block isomorphisms are tied to the generic fold

Each existing per-base block isomorphism — which maps a fixed-size group of digit bytes to one
byte or block — SHALL be tied to the generic radix fold by a proved theorem. The block
isomorphisms SHALL be retained as fast paths rather than deleted.

The theorem SHALL be a **canonicity-filtered restriction**, not an equality: each block
`apply` accepts only canonical blocks, and two of them also reject a block whose value does
not fit their codomain. So the statement is the implication pair — a fold that yields `n` on
an accepted input agrees with the block's value, and a block result agrees with the fold —
and the proof obligation SHALL include each guard's effect.

**Both directions SHALL be stated at the block's own arity** — its literal digit vector — and
not over an arbitrary `List UInt8`. At the literal arity the arity condition is not
hypotheses to discharge but part of the statement, and an implementation that states it over
an arbitrary list SHALL add the length condition explicitly.

**A block whose digits can exceed its codomain SHALL carry the domain condition as an
explicit hypothesis** on the fold-to-block direction, and its rejection SHALL be stated as a
**separate** law rather than as a disjunct of the agreement theorem. The reason is the
paper's law: `PAPER.md` defines `apply : α → Maybe β` as a **function**, so a statement of the
form `apply = some … ∨ apply = none` is a case analysis on a result, not the law
`Just b → g b = Just a`. A partial isomorphism's domain is what the `Maybe` arrow models, so
the condition belongs in the hypothesis.

**Measured, the bases split two ways and the split is arithmetic, not a judgement call:**
base 2's eight bits, base 4's four quartets and base 16's two nibbles each reach exactly
`255`, so `n ≤ 255` follows from the digit bounds and the strong form holds with no
hypothesis. Base 8's three octal digits reach `511` and base 10's three decimal digits reach
`999`, so `"777"` and `"999"` are numerals the fold accepts (`some 511`, `some 999`) and the
blocks reject (`none`). For those two the domain condition is a hypothesis and the rejection
gets its own law.

The rejection law SHALL state the **complete** characterisation, not merely a sufficient
condition: for bases 8 and 10 a block succeeds **exactly when** its value is at most `255`,
which makes the rejection law an iff about the block's domain rather than one half of it.

**All seven** block isomorphisms SHALL be covered, base 10's included; excluding it from the
power-of-two grouping is a classification, not an omission.

The generic fold SHALL NOT be applied across the padded bases' terminal-tail layer: base 32
and base 64 encode a length class there, and a minimal-width numeral has none. The theorems
covered by this requirement are over the block layer only.

#### Scenario: A block iso agrees with the fold

- **WHEN** a block of `k` digits is converted by a base's block isomorphism and by the
  generic fold restricted to those `k` digits
- **THEN** the two agree on inputs the block iso accepts, by a proved theorem, so a change to
  either is a build failure rather than a silent divergence.

#### Scenario: A canonicity guard is not silently dropped

- **WHEN** a digit string is accepted by the generic fold but rejected by the block
  isomorphism (base 64's re-encode guard, or an octal block denoting `511`)
- **THEN** the theorem states the implication in the direction that holds and does not claim
  the two functions agree on that input — a bare equality would be false here.

#### Scenario: An overflow block is rejected by a named law

- **WHEN** a block's digits denote a value above `255`
- **THEN** the block isomorphism returns `none`, stated as its own theorem, so the rejection
  is proved rather than left as an observed behaviour.

#### Scenario: The tie is stated at the block's arity

- **WHEN** the agreement theorem is written for a base
- **THEN** it names the block's literal digits, so the arity cannot be wrong — and a reader
  porting it to an arbitrary list must supply the length condition themselves.

#### Scenario: The tie is mutation-tested

- **WHEN** a block isomorphism's digit order is perturbed
- **THEN** the proved theorem fails, demonstrating that it constrains the block iso and is not
  satisfied vacuously.

#### Scenario: Padding is not read as a numeral

- **WHEN** a padded base-32 or base-64 encoding is converted to a number
- **THEN** that composition is out of scope for this requirement; the block-only theorem does
  not license folding a terminal-tail spine, and no theorem claims it does.
