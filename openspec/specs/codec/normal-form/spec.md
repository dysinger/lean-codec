# codec/normal-form Specification

## Purpose

The information-free-variation layer of a binary format: the quotient of a byte
string by the presentation choices that carry no information (case), so a decoder
can accept every legal spelling while the encoder still emits exactly one.

## Requirements

### Requirement: Information-free variation is a quotient, not a weakened law

A codec that accepts more than one concrete spelling of the same value SHALL model
the extra spellings as a **quotient of the concrete side**, given by a normalizer
`norm : S → S` that is **total**, **idempotent** (`norm (norm x) = norm x`) and
**length-preserving**. Those three facts SHALL be carried by the _type_ of the
normalizer (a structure with those fields), not demanded as a proof argument at
each use. The partial isomorphism between the value and the quotient SHALL remain a
**strict** `Iso` whose inverse law is still a field; the law SHALL NOT be weakened
to hold only "modulo equivalence classes", and no second law SHALL be added to the
`Iso`.

#### Scenario: The quotient is a type, not a relaxed arrow

- **WHEN** a normalizer `norm` is total, idempotent and length-preserving
- **THEN** the quotient is represented as the **type** of `norm`'s fixed points
  (the normal forms), so `Iso value (Normal S norm)` is an ordinary `Iso` and every
  existing law, `Unambiguous`, and `Functional` apply to it unchanged.

#### Scenario: `drop ∘ fill = id` follows from idempotence

- **WHEN** a canonical representative `fill : S → Normal S norm` is defined as
  `s ↦ norm s`
- **THEN** `norm` on the quotient is the identity — `norm (fill s) = fill s` is the
  fixed-point witness, definitionally — so the property the paper states informally
  ("modulo equivalence classes") follows from idempotence rather than being an
  additional law to trust.

#### Scenario: Every normal form is reached

- **WHEN** a normal form `f : Normal S norm` is given
- **THEN** `fill f.raw = f`, so the quotient is faithfully represented: no normal
  form is unreachable and the fixed-point subtype is not merely a subset of the
  quotient but a bijective copy of it.

#### Scenario: The asymmetric direction is the only one that holds

- **WHEN** `fill` and `norm` are composed in the other order
- **THEN** `fill ∘ norm = id` does **not** hold in general, and the specification
  SHALL NOT claim it: the content of the layer is exactly that `norm` is
  many-to-one and `fill` picks one representative. Stating the invariant
  symmetrically is the error this requirement corrects.

### Requirement: A normalising decoder is not an `Iso`, and its law is stated

A decoder that accepts several spellings SHALL be expressed as the normalizer
composed **outside** an ordinary `Iso` — `decode s := iso.unapply (fill s)` — and
SHALL NOT be presented as an `Iso`, a combinator, or an inverse of the encoder.
Because `norm` is many-to-one, the wrapper has no inverse, and that SHALL be stated
rather than hidden. The library SHALL additionally state the theorem that makes the
wrapper useful, which requires a **per-instance obligation** on the codec being
wrapped: the encoder emits a normal form.

#### Scenario: Case folding is a decode-only wrapper

- **WHEN** a format's canonical alphabet is one case (e.g. uppercase hex) and its
  standard also requires accepting the other case
- **THEN** the codec value stays the strict canonical `Iso`, and the
  case-insensitive behaviour is a wrapper applying `norm` (fold case) before
  `unapply` — proved total and idempotent, explicitly documented as accepting input
  the `Iso` itself rejects, and explicitly documented as having no inverse.

#### Scenario: Decoding the encoder's own output still succeeds

- **WHEN** the wrapped codec's encoder emits a normal form — `norm (encode x) =
encode x` — which every codec using this layer SHALL prove about itself
- **THEN** the normalising decoder reproduces the value: `decode (encode x) = some
x`. Without that hypothesis the guarantee does **not** hold, since `norm` applied
  before `unapply` can consume input the strict `Iso` would have accepted; the
  hypothesis is therefore an obligation, and the specification SHALL NOT promise
  the roundtrip without it.

#### Scenario: A normalising decoder does not break unambiguity

- **WHEN** a codec is unambiguous — one concrete string yields at most one value
- **THEN** composing `norm` before `unapply` preserves that, because `norm` is a
  _function_ (total and single-valued) and so introduces no alternative results.
  Accepting both `6f` and `6F` for the same value widens the decoder's **domain**;
  the constraint it must respect is the _canonicality_ of encode (one value, one
  spelling), not unambiguity.

#### Scenario: Encoding stays canonical

- **WHEN** a value is encoded
- **THEN** exactly one concrete spelling is emitted — the canonical representative
  (`fill`'s choice) — so the encoder remains a function and no alternative spelling
  is produced nondeterministically.

### Requirement: Only length-preserving variation is in scope

The layer SHALL be specified only for normalizers that preserve length, so that it
acts within a single `Bytes n`. Variation that changes the byte count (collapsing a
whitespace run, dropping leading zeros) SHALL NOT be claimed by this layer: it
cannot be a `Bytes n → Bytes n` map, and supporting it would require a different
carrier rather than a different normalizer.

#### Scenario: Case folding is expressible, whitespace collapsing is not

- **WHEN** a format accepts case-variant spellings of the same fixed-width token
- **THEN** that variation is modelled by a length-preserving `norm` over the same
  `Bytes n`.
- **WHEN** a format's variation changes the byte count (a run of blanks of arbitrary
  length)
- **THEN** the layer does not claim to model it, and the specification records that
  this is a carrier question, not a normalizer question — no length-changing
  normalizer and no second byte-string carrier is introduced here.
