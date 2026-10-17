# Proposal

## Why

The single-carrier rewrite (`single-carrier-bytes`) made the codec _provably
correct_ and _axiom-clean_ (`[propext, Quot.sound]`-only, zero `Classical.choice`),
and the carrier read (`s ⟨i,·⟩`) already lowers to a ~20 ns scalar indexed load —
essentially a bare pointer read. But the bench exposes that the _bulk_ paths are
nowhere near hand-tuned C:

- `encodeRepeat Codec.byte` runs at ~30 ns/byte (~33 MB/s) for a 1 MiB list, and
  grows linearly with a constant factor ~40× higher than a `memcpy`-speed bulk
  write;
- `decodeFull` (the "fused" full-consumption `many`) is still ~50 µs/byte at 8k,
  still quadratic despite threading a single `Option`;
- `decodeRepeat` is the paper's inherent Θ(m²) all-prefix enumeration and is
  2.5 s at 8192 bytes.

The aim stated from the start was "as close to hand-tuned C as possible." The
correctness work is done; the performance work is not. The remaining gap is not
semantic — it is a _lowering_/representation problem: the carrier's dependent
type index (`Fin n → UInt8`) is a **pure function**, so the bulk `encodeRepeat`
builds one nested `concat` closure per element (a scalar-indexed-load substrate
for _reads_, but a nested-closure substrate for _writes_).

## What Changes

- **Profile and attribute first** (done §1): a calibrated bench with a
  `memcpy`/`memset` baseline, per-lane ns/op + MiB/s across a ×1/×2/×4 sweep, and
  a representation-isolation lane. This settled the question: the pure `Bytes n`
  carrier cannot be a flat accumulator, and the gap is the nested `concat`
  closures, not bandwidth.
- **Re-stage the bulk encode/decode through a contiguous `ByteArray`/`Array UInt8`
  accumulator** behind the Lean runtime's own `@[extern]` C primops
  (`ByteArray.push`/`copySlice`/`get!`). These are hand-written C in the runtime,
  compiled by the plain `cc`.
- **Prove the fast path equal to the spec** — `fastEncodeRepeat p xs = encodeRepeat p xs`
  (and the decode dual) — _pointwise_ via the carrier's finitary `Bytes.ext` and
  `Array.ofFn`/`GetElem` bridge, never `Array.extract`/`Array.toList` (which leak
  `Classical.choice`). `Bytes n` stays the _specification_ every law is stated over;
  the `ByteArray` accumulator is only a proved-equal _implementation_.
- **Tune the emitted C** with plain clang `-O3`/`-march=native`/LTO/PGO on the
  `*.c` Lean emits, and re-measure.
- **Preserve every semantic law untouched.** This is a performance change only:
  `Rel`, `decode_spec`, `bidir`, `roundtrip`, `decodeRepeat_spec`,
  `decodeFull_spec`, the `Combinators` laws, and the `varint` denotation do not
  change meaning. The axiom gate stays `[propext, Quot.sound]`-only; any new
  fast path must be proved equal to the spec, not asserted.

## Capabilities

### New Capabilities

- `codec/performance`: the §10.5 acceptance criteria, stated as measurable
  throughput/latency targets per lane, the profiling methodology (per-op
  wall-clock plus emitted-IR attribution), and the calibrated-bench-harness
  requirements — used to demonstrate the single-carrier codec approaches
  hand-tuned C.

## Impact

- `Bench.lean`: add a profiling harness (per-op attribution, larger/smaller size
  sweeps, a `memcpy`-speed baseline for calibration) without removing the
  byte-exact roundtrip smoke checks.
- `lakefile.lean`/`flake.nix`/`default.nix`: adjust the plain-clang compile
  flags (`-O3`/LTO/PGO/target-march) for the emitted `*.c`.
- `Codec/*.lean`: lower-level representation of the encode/decode hot loops,
  gated so every law still holds with zero `sorry`, zero `Classical.choice`.
- Axiom record unchanged: `#print axioms Codec.roundtrip` ⇒
  `[propext, Quot.sound]`.
