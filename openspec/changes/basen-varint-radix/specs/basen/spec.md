# Spec Delta — `basen` (`basen-varint-radix`)

## MODIFIED Requirements

### Requirement: Base16 decoding accepts both cases (RFC 4648 §8)

The Base16 decoder SHALL accept hex digits in **either** case, as a **choice of this
package** rather than an obligation inherited from a standard, and SHALL return the same
value for a block and its case-pre-passed form. The canonical alphabet SHALL remain
uppercase and the encoder SHALL emit only it. Case-insensitivity SHALL be supplied by a
pre-pass applied **outside** the strict `Iso` — never by weakening `Iso.law` — so the
`Codec` value stays a strict uppercase bijection and the widening is confined to decoding.

**The strict uppercase-only decoder is conformant on its own.** RFC 4648 §8 says base 16
encoding "does not require case insensitivity; however, Base 16 decoders **MAY** accept
lowercase letters" — a permission, not a requirement. An earlier revision of this
requirement opened "as RFC 4648 §8 requires" and a 24-theorem folding tier existed to
discharge the obligation that phrase implied; `basen-uppercase-prepass` removed both. A
decoder that rejects `6f` is conformant, so nothing in this requirement makes case
tolerance a conformance duty.

**The tolerant decoder SHALL carry the roundtrip law that makes it a decoder of the
package's format, not merely a case-folding function.** It SHALL be proved that the
pre-pass is the identity on the encoder's output and that the tolerant decoder accepts it,
so that `decodeHexFold` is connected to `encodeHex` by a theorem. A wrapper whose
case-folding behaviour is tested but which no theorem ties to the encoder SHALL NOT be
described as a decoder of this package's format, because a reader comparing the RFC against
the library would find the tolerant reading and no law about it.

Where a package documents a profile as conforming to a specification and the package's
roundtrip, canonicality, injectivity and converse laws are all stated over a _different_,
stricter decoder, the documentation SHALL say which decoder owns which laws, so that no row
of the conformance table claims a theorem the corresponding declaration does not own.

#### Scenario: Both cases decode to the same value

- **WHEN** a byte string and its case-pre-passed form are decoded by the tolerant decoder
- **THEN** both produce the same value — `decodeHexFold_lowercase_eq` relates the two
  inputs `"6f"` and `"6F"`, and the relation holds because `upperBytes` maps the lowercase
  digit onto the uppercase one and fixes every other byte.

#### Scenario: The strict decoder still rejects lowercase

- **WHEN** lowercase input is fed to the strict `Codec`-value decoder
  `decodeFull hexElem hexConsumesByte`
- **THEN** it returns `none` at an input where case is the **only** reason for rejection
  (an even-length input asserting the arithmetic is even, so the arity gate cannot be the
  cause), and this is **not** a conformance divergence because the strict decoder is
  conformant without case tolerance. The earlier "a case-insensitive alphabet would break
  `Unambiguous`" rationale is withdrawn: the constraint is the canonicality of encode.

#### Scenario: The encoder emits a normal form (the layer's obligation)

- **WHEN** the encoder produces a block
- **THEN** that block is already a **fixed point** of the case pre-pass
  (`upperBytes_of_encodeHex`) — the per-instance hypothesis the tolerant decoder requires,
  without which the pre-pass applied before `unapply` could make decoding fail on the
  encoder's own output.

#### Scenario: The fold is upward, and idempotent

- **WHEN** the case pre-pass is applied
- **THEN** it maps `a`–`z` **up** to `A`–`Z` (so the canonical uppercase encoding is a
  fixed point) and is idempotent (`upperByte_idem`, `upperBytes_idem`), which is the
  `Normalizer` law that makes the quotient type well-formed.

#### Scenario: The conforming decoder inverts the encoder

- **WHEN** a byte list is encoded by `encodeHex` and the result decoded by `decodeHexFold`
- **THEN** the decoded value is that byte list — `encodeHex bs = some ⟨n, s⟩ →
decodeHexFold s = some bs` — so the tolerant reading is a decoder of this package's
  format and not only a case-folding function, and the roundtrip family is not owned
  exclusively by the stricter decoder.

### Requirement: A numeral denotes a number

`basen` SHALL provide a radix-generic conversion between a numeral — a sequence of digit
bytes — and the number it denotes, as **one** definition serving every radix whose alphabet
the layer recognises, rather than a per-base derivation.

**The layer SHALL state two distinct claims, and SHALL NOT conflate them.** A radix may be:

- **digit-served** — the digit-value function knows its alphabet; or
- **positional** — the alphabet has a fixed width, so `toNat b ds` is `Σ dᵢ · bⁱ` over the
  digits in most-significant-first order and `ofNat` emits a minimal fixed-radix numeral.

Every positional radix SHALL be digit-served. The converse SHALL NOT be claimed: a radix
whose numeral is **terminator-delimited** rather than fixed-width is digit-served without
being positional, and the positional laws (`ofNat`/`toNat` round-trip, minimality, the
`numeralIso` quotient) SHALL NOT be applied to it.

For every **positional** radix the layer SHALL consist of a digit-value function, a fold
from a digit sequence to a `Nat`, and its inverse producing canonical digits. The fold SHALL
be the value of the numeral: `toNat b ds` is `Σ dᵢ · bⁱ` over the digits in
most-significant-first order.

The positional radices are **`2 ≤ b ≤ 64`**, exactly seven, and the bound SHALL be stated by
the requirement rather than left to a signature, because `b = 1` is not a positional radix
and `ofNat 1` has no canonical finite numeral. The digit-served set additionally includes
**128**, whose alphabet is **total over bytes**: every byte is a digit, its value being that
byte's low seven bits. Radix 128 therefore has no emitter of its own and no positional
structure — its digits are chosen by the data rather than emitted by a canonical encoder,
which is what makes it servable by a run and not by `numeralIso`.

The seven per-base digit-value functions SHALL be proved equal to the single digit-value
function at their radix — the **decode** direction. **The encode direction is not unified**:
radix 2's inverse map (`valToBit`) carries a deliberately non-injective fallback and SHALL NOT
be rewritten. At radices 4 and 8 the inverse maps are `48 + d` and **injective**, so an
agreement law is provable there and is a bonus rather than an obligation.

A radix's alphabet SHALL be either a **proper window** — some bytes are not digits, and a
sequence containing one SHALL yield `none` rather than a partial conversion — or **total
over bytes**, in which case every byte is a digit and the rejection obligation does not
apply. The seven positional radices are the former; radix 128 is the latter, its digit
value being the byte's low seven bits.

The empty sequence is **not** the canonical spelling of zero at any positional radix —
`ofNat b 0` is the base's single zero digit — but the fold's base case is `some 0`, so
**`toNat b [] = some 0`**. That is a by-product of the recursion, not a convention: nothing
in this layer treats `[]` as a numeral. The normaliser rejects it (`trimFor b [] = none`),
`isNumeral b [] = false`, `normF b []` replaces it with the zero numeral, and every `Iso`
path goes through the normaliser. `toNat b` of the zero digit is `some 0` as well, so the
fold — not the layer — admits two spellings of zero, and the quotient of the requirement
below has one element for them.

#### Scenario: A numeral converts to its value

- **WHEN** the generic fold is applied to a valid digit sequence in a given radix
- **THEN** the result is the number that numeral denotes, so that base-10 `"300"` yields
  `300` and base-2 `"01100001"` yields `97`.

#### Scenario: One digit-value function serves every radix

- **WHEN** any base's own digit-value function is inspected
- **THEN** it is proved equal to the generic function at that radix, so no base's
  digit-value function can disagree with the generic one.

  **Scope of that claim.** It is about the seven _digit-value functions_ (`bitVal`,
  `quartetVal`, `octToVal`, `hexToNibble`, `b32ToVal`, `b64ToVal`, `digVal`) and nothing
  else. Base 16 additionally carries a case-pre-pass decoder (`decodeHexFold`) which accepts
  `"6f"` where `digitVal 16 'f'` is `none`; that is a _superset_ of the generic alphabet
  applied after it, and is the requirement above's subject, not this one's.

#### Scenario: An out-of-alphabet digit is rejected

- **WHEN** the fold is applied to a sequence containing a byte outside the radix's alphabet
  (the digit `"9"` in radix 8, or `"G"` in radix 16)
- **THEN** the result is `none`, and it is not partially converted.

#### Scenario: A terminator-delimited radix is served but not positional

- **WHEN** radix 128 is presented to the layer
- **THEN** its digit-value function recognises its alphabet, so the radix is
  **digit-served**, but it is **not** positional: it carries no `ofNat`/`numeralIso`
  round-trip, and passing it where a positional radix is required is a type error rather
  than a silent wrong answer — because the positional predicate has seven constructors and
  radix 128 is not among them.

## ADDED Requirements

### Requirement: A terminator-delimited numeral is served as a run

Where a format's numeral has its width determined by a **byte property** rather than by
position, the package SHALL serve it as a run with a terminator, not as a positional radix.

The run SHALL be expressed with the established repetition layer.

The fold's domain SHALL be the numeral's **members followed by its terminator**, high bits
masked — not the members alone. The package SHALL NOT claim such a numeral's value is its
positional fold at any radix.

#### Scenario: A continuation run terminates on a clear high bit

- **WHEN** a sequence of bytes each with the high bit set is followed by a byte with the
  high bit clear
- **THEN** the run's members are exactly the high-bit-set prefix and the terminator is the
  first clear-high-bit byte, so the numeral's width is a property of the bytes rather than
  of a radix parameter.

### Requirement: A terminated numeral's fold is pinned before it is proved

The shift-fold of a terminator-delimited numeral SHALL be evaluated on the format's own
boundary vectors before any law about it is stated, so that a convention that happens to
agree with the positional fold on a given vector cannot be mistaken for the same function.

The package SHALL record the vector on which the two conventions **disagree**, and SHALL
NOT rely on their agreement at any vector.

#### Scenario: The value is a shifting fold, not a positional one

- **WHEN** the numeral's seven-bit groups — the members **and** the terminator, high bits
  masked — are folded to a number
- **THEN** each group is shifted by seven times its position from the **least** significant
  end, so that `[0x81, 0x01]` gives the groups `[1, 1]` and the value `129`; the value is
  stated by a dedicated fold, not by the positional `toNat` at any radix.

#### Scenario: The terminator's bits are part of the value

- **WHEN** the fold's domain is stated
- **THEN** it includes the terminator, so that `[0x81, 0x01]` and `[0x81, 0x00]` — which
  share their members — take different values, `129` and `1`; folding the members alone
  would lose the final group and make both `1`.

#### Scenario: The folds are shown to differ where they differ

- **WHEN** the record of agreement is stated
- **THEN** it names a vector where the two conventions give different numbers — the
  canonical encoding of `16384` is `[0x80, 0x80, 0x01]`, whose groups `[0, 0, 1]` fold to
  `1` positionally and `16384` as a shift-fold — because the two folds agree whenever the
  group list is palindromic, so an all-equal-group witness would prove the opposite of the
  claim.
