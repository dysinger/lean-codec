# Spec Delta

## ADDED Requirements

### Requirement: Axiom gate is performance-neutral

Performance tuning SHALL NOT change the proof record. Every law — `Rel`,
`decode_spec`, `bidir`, `roundtrip`, `decodeRepeat_spec`, `decodeFull_spec`, the
`Combinators` `_spec`/`_rel` laws, and the `varint` denotation — SHALL remain
what it was before the tuning, and `#print axioms Codec.roundtrip` SHALL report
`[propext, Quot.sound]` (zero `Classical.choice`, zero `sorry`) after every
performance change. Any fast path introduced SHALL be proved equal to the spec
denotation, never asserted, never `unsafe`, and never introduced at the cost of
a law.

#### Scenario: A fast path is law-backed

- **WHEN** a bulk encoder/decoder fast path is introduced to replace a slow
  `Bytes n` loop
- **THEN** there is a theorem equating the fast path to the `Bytes n`
  denotation (a refinement lemma), `#print axioms` on that theorem reports
  `[propext, Quot.sound]`-only, and `lake build` stays zero-`sorry`.

#### Scenario: The roundtrip stays unconditional

- **WHEN** the encode/decode hot loops are re-staged for performance
- **THEN** `roundtrip` (encode-then-decode recovers the value with empty
  remainder) holds unconditionally, with no `NoAlt`/uniqueness gate introduced
  by the optimization.

### Requirement: Scalar indexed read is the hot path

The single-carrier read `s ⟨i,·⟩ : UInt8` for `s : Bytes n` and `i : Fin n`
SHALL remain a scalar indexed load — a structural pointer read with no `List`
cons chasing, no `Array`/`ByteArray` boxing, and no sigma re-packaging — and the
optimized encode/decode loops SHALL make it the only operation on the carrier.
Bounds-check arithmetic (`Nat`/`Fin` index computation) SHALL be hoisted out of
loops so it is paid once, not per element.

#### Scenario: The read stays structural

- **WHEN** the emitted IR for `decode Codec.byte s` is inspected
- **THEN** the substrate operation is a single indexed load; a constant factor
  may remain for the description-level dispatch, but no allocation or dependent
  re-wrapping is in the inner read.

### Requirement: Bulk encode approaches a calibrated baseline

The repetition encoder `encodeRepeat Codec.byte` over a 1 MiB value list SHALL
approach a hand-tuned-C bulk write: within an order of magnitude of a `memcpy`

- or `memset`-speed baseline measured on the same machine (the baseline recorded
  by the bench's own calibration lane), and SHALL scale linearly in the input
  length (constant per-byte cost when the size doubles).

#### Scenario: Linear scaling

- **WHEN** `encodeRepeat Codec.byte xs` is timed at sizes `n` and `2n`
- **THEN** the per-op time at `2n` is ≈ 2× the per-op time at `n` (no hidden
  quadratic term), and the per-byte cost is within an order of magnitude of the
  calibration baseline.

#### Scenario: The value is still verified

- **WHEN** the optimized `encodeRepeat` run is benched
- **THEN** the bench still asserts the encoded _value_ (byte-for-byte against
  the expected `Bytes n`), not merely its length — a wrong fast path fails the
  bench, not just the proof.

### Requirement: Repetition decoders avoid re-parse blowup

The full-consumption repetition decoder `decodeFull` SHALL NOT exhibit the
quadratic re-parse blowup of `decodeRepeat` (the all-prefix enumeration). At a
fixed input length, `decodeFull` SHALL be measurably cheaper per byte than
`decodeRepeat` on the same input, by re-using already-consumed prefixes rather
than re-attaching/re-parsing from scratch at every step.

#### Scenario: decodeFull beats decodeRepeat

- **WHEN** `decodeFull Codec.byte h n s` and `decodeRepeat Codec.byte h n s`
  are timed on the same input
- **THEN** `decodeFull` is faster per byte (it threads one `Option` and does
  not re-traverse), and the bench asserts its result value against the
  `decodeFull_some` law rather than a length-only check.

### Requirement: Bench is a calibrated profiling harness

The §10.5 bench SHALL report, per lane: wall-clock nanoseconds per op **and** a
per-byte throughput figure, against a machine-calibrated baseline (a `memcpy`/
`memset`-speed lane run once at startup), so "is this fast?" is answered
relative to the same machine rather than by absolute ns. It SHALL sweep at
least three sizes (×1/×2/×4) to expose scaling, and SHALL keep the byte-exact
roundtrip and law smoke checks (never reduce a value check to a length check).

#### Scenario: Throughput and baseline are reported

- **WHEN** `./bench` runs
- **THEN** each lane prints both ns/op and bytes/op (or MB/s) against the
  calibration baseline, and the size sweep makes linear vs quadratic scaling
  visible.

#### Scenario: Value checks survive tuning

- **WHEN** a hot loop is re-staged for speed
- **THEN** the corresponding bench lane still asserts the encoded/decoded
  _value_ (byte-for-byte), so a semantically-wrong fast path is caught at run
  time, independent of the proof.
