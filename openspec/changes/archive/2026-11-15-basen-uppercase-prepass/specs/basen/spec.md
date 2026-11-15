## ADDED Requirements

### Requirement: Case-insensitivity is a pre-pass, not a second isomorphism

Where a base's alphabet contains no lowercase symbols and a decoder is expected to
accept lowercase input, the package SHALL supply case-insensitivity as a **total
idempotent pre-pass** on the input bytes, applied before the existing strict decoder.
The isomorphism SHALL run from normalised text to the value; the pre-pass SHALL NOT be
folded into the isomorphism and the strict inverse law SHALL NOT be relaxed.

The pre-pass SHALL be a single `UInt8 → UInt8` map lifted pointwise to the byte string,
proved idempotent, and composed with the existing decoder via the core package's
`Normal`/`Normalizer` mechanism rather than re-derived per base.

A base SHALL NOT gain a bespoke case-folding tier of its own where the core already
supplies the general mechanism: a decoder of the form
`decodeNormal normalizer strictIso` requires only the normaliser's idempotence proof
and the encoder-emits-a-normal-form obligation.

#### Scenario: Lowercase hex decodes through the pre-pass

- **WHEN** a base16 decoder is given a lowercase numeral (`6f`) and its uppercase form
  (`6F`)
- **THEN** both return the same value, because the lowercase form is uppercased before
  the strict decoder runs.

#### Scenario: The pre-pass is idempotent

- **WHEN** the case pre-pass is applied twice
- **THEN** the second application changes nothing, so the pre-pass is a normaliser in
  the core package's sense and can be used with `decodeNormal`.

#### Scenario: The strict decoder is unchanged

- **WHEN** the strict decoder is given lowercase input
- **THEN** it still rejects it, because the widening lives in the layer above; no
  existing law (`roundtrip`, `decodeFull_canonical`, `decode_encode_inverse`,
  `encode_injective`, the `_char` family) is restated or weakened.

### Requirement: A pre-pass is applied only where case is not data

A case pre-pass SHALL be applied to a base only when that base's alphabet contains no
lowercase symbols. Where lowercase letters are alphabet members in their own right —
each denoting a distinct value — uppercasing SHALL NOT be applied, because it maps a
valid input to a **different valid value** rather than to the same one.

The distinction SHALL be recorded per base with the measurement that settles it, so a
later reader cannot add the pre-pass to a base where it corrupts data.

For Base64 specifically: the alphabet uses all 64 symbols, including 26 lowercase
letters, so a base64 payload's case carries value information. Base64 SHALL retain its
exact alphabet and SHALL NOT gain a case-insensitive decoder.

#### Scenario: Base64 is excluded because its case is data

- **WHEN** the case pre-pass is considered for base64
- **THEN** it is rejected, and the exclusion is backed by a measurement showing that
  uppercasing a base64 payload changes the decoded value (for example `TWFu` decodes
  as `Man` while `twfu`, whose letters are all valid base64 symbols, decodes to a
  different value).

#### Scenario: Bases without letters need no pre-pass

- **WHEN** a base whose alphabet is digits only (2, 4, 8, 10) is considered
- **THEN** no case pre-pass is added, because there is no case to fold.

### Requirement: A stated conformance obligation cites the specification's own wording

Where the package justifies an implemented behaviour by an external specification, the
justification SHALL quote that specification's actual normative wording, and SHALL
distinguish a requirement (`MUST`) from a permission (`MAY`). A behaviour the
specification permits rather than requires SHALL be described as an optional
convenience, not as conformance the package owes.

A conformance claim SHALL NOT rest on an unsourced paraphrase: the package's
documentation of an external standard SHALL be traceable to the standard's text.

#### Scenario: A MAY is not presented as a MUST

- **WHEN** the package documents case-insensitive Base16 decoding
- **THEN** it cites RFC 4648 §8's own wording — that base 16 encoding does not require
  case insensitivity and that decoders may accept lowercase — and describes lowercase
  acceptance as an optional convenience rather than a requirement it is obliged to
  meet.

#### Scenario: The decoder is conformant without the convenience

- **WHEN** the strict uppercase-only decoder is considered against RFC 4648 §8
- **THEN** it is conformant, so removing the case pre-pass would not make the package
  non-conforming; the pre-pass is a feature choice with a stated cost.
