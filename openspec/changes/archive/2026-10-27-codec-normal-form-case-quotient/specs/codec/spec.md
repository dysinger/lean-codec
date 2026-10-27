# Spec Delta

## MODIFIED Requirements

### Requirement: Lossless capture of allowable bytes

Any run of bytes a codec's predicate permits SHALL be captured as part of the
decoded value and re-emitted verbatim on encode; no byte SHALL be silently
discarded. Capture-and-re-emit SHALL be understood as the **identity normalizer**
(the degenerate case of the normal-form layer): the strict inverse law then holds
with no normalisation and no relaxation. A codec MAY instead model
**information-free variation** — presentation that carries no information, such as
the case of a hexadecimal digit — as a normal form, provided: the variation is
carried by a **total, idempotent, length-preserving** normalizer applied **outside**
the partial isomorphism; the encoder is proved to emit a **normal form** (so
decoding its own output still succeeds); and the encoder still emits exactly one
canonical spelling. Formatting is not semantic: an AST SHALL NOT be required to
carry presentation (whitespace-run length, leading zeros, case) in order to satisfy
this requirement.

#### Scenario: Optional bytes are preserved

- **WHEN** a description decodes a maximal run of bytes satisfying predicate `p`
  via repetition over a `subset p byte` step (denotation `relRepeat`, decoders
  `decodeRepeat`/`encodeRepeat`)
- **THEN** that exact run is part of the decoded value and is re-emitted byte-for-
  byte on encode.

#### Scenario: Capture-verbatim is the identity normalizer

- **WHEN** a codec captures a permitted run and re-emits it verbatim
- **THEN** its normalizer is the identity: no normalisation is applied and the
  strict inverse law holds with no relaxation, which is the degenerate case of the
  normal-form layer rather than an argument that no normal form can exist.

#### Scenario: A normalising decoder leaves the `Iso` strict

- **WHEN** a format accepts information-free variant spellings of the same value
  (e.g. case-insensitive hex digits)
- **THEN** the variants are absorbed by a total, idempotent, length-preserving
  `norm` composed before the `Iso`'s `unapply`; the `Iso` and its field-carried
  inverse law are unchanged; the encoder emits the one canonical spelling and is
  proved to emit a normal form; and no byte is discarded by the encoder.

#### Scenario: Presentation is not information

- **WHEN** a format's concrete syntax permits presentation choices that carry no
  information (case of a digit, amount of whitespace, number of leading zeros)
- **THEN** the specification does not require the decoded value to preserve them;
  preserving them is not a conformance obligation, and a codec that normalises them
  away satisfies this requirement provided the encoder's output is canonical and
  re-decodes to the same value.
