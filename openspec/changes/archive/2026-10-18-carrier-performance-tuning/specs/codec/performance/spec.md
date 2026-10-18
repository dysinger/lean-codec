# Spec Delta

## ADDED Requirements

### Requirement: Axiom gate is performance-neutral

Performance tuning SHALL NOT change the proof record. Every law — `Rel`,
`decode_spec`, `bidir`, `roundtrip`, `decodeRepeat_spec`, `decodeFull_spec`, the
`Combinators` `_spec`/`_rel` laws, and the `varint` denotation — SHALL remain what it was
before the tuning, and `#print axioms Codec.roundtrip` SHALL report `[propext,
Quot.sound]` (zero `Classical.choice`, zero `sorry`) after every performance change. Any
fast path introduced SHALL be proved equal to the spec denotation, never asserted, never
`unsafe`, never introduced at the cost of a law.

#### Scenario: A fast path is law-backed

- **WHEN** a packed fast path is introduced to replace a slow `Bytes n` loop
- **THEN** there is a theorem equating the fast path to the `Bytes n` denotation (a
  refinement lemma) — `decodeArray_eq`, `decodeFullArray_spec`, `encodeArray_eq`, and
  `encodeByteArrayBytes_eq` are the four such laws — `#print axioms` on each reports
  `[propext, Quot.sound]`-only, and `lake build` stays zero-`sorry`.

#### Scenario: The roundtrip stays unconditional

- **WHEN** the encode/decode hot loops are re-staged for performance
- **THEN** `roundtrip` holds unconditionally, with no `NoAlt`/uniqueness gate introduced
  by the optimization.

### Requirement: The packed decoder preserves backtracking semantics

The re-derived packed (`USize`-cursor) decoder SHALL preserve `decode`'s nondeterministic
semantics exactly: `alt` is the union `++`, `seq` is the `flatMap` cross-product. Its
result is `List (α × USize)` — the `List` is the non-determinism multiplicity; the packed
carrier removes only the per-branch `Suffix`/`Bytes` closure, NOT the `alt`/`seq` result
`List`.

#### Scenario: Backtracking is not silently dropped

- **WHEN** the packed decoder is compared to `decode`
- **THEN** there is a `decodeArray_eq` refinement equating the packed result to `decode`'s
  `List (α × Suffix n)` via the `Suffix`-reconstruction bridge
  `{ remaining := n - c, hle := Nat.sub_le n c, bytes := bdrop c s }` (with a proof
  `c ≤ n`), and a `decodeFullArray_spec` refinement for the full-consumption case; and a
  greedy (single-result) fast path, if shipped at all, is a separate labeled `decodeGreedy`
  documented **sound-not-complete**, never presented as `decode`.

### Requirement: Two proof layers are not conflated

The packed fast path SHALL be delivered as two layers with distinct proof status, and
either may be used, but they SHALL NOT be conflated:

- **Layer 1 (proven, zero trusted C)**: the packed decoder/encoder whose refinement laws
  close `[propext, Quot.sound]`-only, with a proof-only body
  `ByteArray.mk ((a.data.toList.drop i.toNat).toArray)`. Layer 1 SHALL be the only layer
  admitted to the `#print axioms` gate.
- **Layer 2 (named trust seam)**: the `@[extern]` `byteSlice` whose Lean body elaborates
  (so `#print axioms` reports the proof-only body clean) but whose running C is trusted,
  not proven. Layer 2 SHALL be **excluded** from the `#print axioms` acceptance, documented
  as a named trust seam, and wired only onto a packed path.

#### Scenario: The two layers are not conflated

- **WHEN** `byteSlice` (Layer 2) ships alongside the proven packed carrier (Layer 1)
- **THEN** the README/bench state explicitly that Layer 1 is proven-zero-C and Layer 2 is
  trusted-C; "no axiom" is not presented as "no trust"; the `#print axioms` gate accepts
  only Layer 1.

### Requirement: Bench is a calibrated profiling harness

The bench SHALL report, per lane, wall-clock nanoseconds per op and a per-byte throughput
figure, against a machine-calibrated `memcpy`-speed baseline (run once at startup). It
SHALL sweep at least three sizes (×1/×2/×4), SHALL keep byte-exact value checks (never
reduce a value check to a length check), SHALL report the two layers as distinct lanes,
and every numeric figure SHALL be tagged `[measured]`, `[historical]`, or `[target]`, and
SHALL be produced by the current bench (never a hand-typed number from a prior draft).

#### Scenario: Throughput and baseline are reported

- **WHEN** the bench runs
- **THEN** each lane prints ns/op and bytes/op against the calibration baseline, the size
  sweep makes scaling visible, and the two layers are distinct lanes.

#### Scenario: Value checks survive tuning

- **WHEN** a hot loop is re-staged for speed
- **THEN** the bench still asserts the encoded/decoded value byte-for-byte, so a
  semantically-wrong fast path is caught at run time.

## Scope

**In scope**: the packed `USize`-cursor carrier (`decodeArray` / `decodeFullArray` /
`encodeArray`, typed over arbitrary `Codec α`) and its refinement proof against the
unchanged `Bytes n` spec — correctness of a packed result carrier, `[propext,
Quot.sound]`-only, full backtracking preserved.

**Out of scope**: proving or benchmarking that the general interpreter runs near C for
arbitrary `α` on real workloads (JSON/PNG/protobuf), and optimizing the heterogeneous
interpreter's speed beyond the isolated byte-sequence/`byte`-slice lanes. The carrier and
its proof land here; the general near-C performance claim is a separate follow-up.
