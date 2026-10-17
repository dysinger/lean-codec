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
type index (`Fin n → UInt8`) pays for `Nat`-index arithmetic, `Fin`-sum concat,
and sigma re-packaging on every step instead of a flat buffer with a bounds-check
hoisted out of the loop. The LLVM build (`lean4-llvm` override in `default.nix`)
is wired for the _deleted_ `Array`/`ByteArray` `@[extern]` fast path, which the
`Bytes n` carrier never touches — so LLVM's `@[extern]` lowering is currently
**unutilized**, not merely under-tuned.

## What Changes

- **A/B the toolchain first.** Build the bench with plain nixpkgs `lean4` and
  with `lean4-llvm` on the same source and record both tables. The LLVM override
  exists only for the deleted `Array`/`ByteArray` `@[extern]` path, which the
  `Bytes n` carrier never touches — so the likely answer is "LLVM is neutral,"
  and the override is dropped as dead weight unless a lane measurably benefits.
- **Add profiling instrumentation** so every lane reports _what dominates_:
  per-op wall-clock, plus emitted-IR inspection of the hot `encode`/`decode`
  loops, to separate "memory bandwidth" from "dependent-type bookkeeping" (the
  `Nat`/`Fin` arithmetic and sigma re-packaging that the bench currently
  confounds).
- **Tune the Lean lowering** on the `Bytes n` carrier without changing its
  denotation: hoist bounds checks out of loops, replace `Nat`-index sigma
  re-concatenation with a single flat accumulator, and make the scalar indexed
  load the _only_ hot operation in the encode fold.
- **Utilize LLVM actively** where the current `lean4-llvm` override is dead on
  the single carrier: either (a) surface an `@[extern]`/`Array`/`ByteArray`
  fast path for the _bulk_ repetition encoder/decoder that is proved equal to
  the `Bytes n` spec (a re-introduced, but this time _law-backed_, transfer seam),
  or (b) drive LLVM's optimizer (clang `-O3`/LTO/PGO/march) on the emitted C of
  the existing `Bytes n` loops, keeping the carrier pure. Decision in design.
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
- `lakefile.lean`/`flake.nix`/`default.nix`: adjust compiler flags (the `leanc`
  `-O3`/LTO/PGO/target-march path), and either wire or remove the dormant
  `lean4-llvm` `@[extern]` plumbing, per the design decision.
- `Codec/*.lean`: lower-level representation of the encode/decode hot loops,
  gated so every law still holds with zero `sorry`, zero `Classical.choice`.
- Axiom record unchanged: `#print axioms Codec.roundtrip` ⇒
  `[propext, Quot.sound]`.
