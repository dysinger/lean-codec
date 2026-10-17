# Design

## Context

`single-carrier-bytes` collapsed the two-tier representation onto one
length-indexed carrier `Bytes n := Fin n → UInt8` and re-proved every law
`[propext, Quot.sound]`-only. The bench (driven by `Bench.lean`) now shows:

| Lane                          | Size     | Current              | Shape                         |
| ----------------------------- | -------- | -------------------- | ----------------------------- |
| scalar-index read `s ⟨i,·⟩`   | 1 MiB    | ~20 ns               | O(1), the carrier's hot read  |
| `decode Codec.byte`           | 1 MiB    | ~47–93 ns            | O(1) peel                     |
| `encodeRepeat Codec.byte`     | 1 MiB    | ~32 ms (~30 ns/byte) | linear but ~40× off memcpy    |
| `decodeRepeat Codec.byte`     | 8 KiB    | ~2.5 s               | Θ(m²) all-prefix (paper §4.4) |
| `decodeFull Codec.byte`       | 8 KiB    | ~404 ms              | still quadratic               |
| `decodeFast Codec.byte`       | 1 MiB    | ~60 ns               | O(1)                          |
| `encodeVarint`/`decodeVarint` | 12345678 | ~230/200 ns          | LEB128                        |

The read path is already there; the bulk paths are not. The bulk
`encodeRepeat` builds nested `concat` closures (a pure `Fin n → UInt8` is a
scalar-read substrate but a nested-closure bulk-write substrate).

## Goals / Non-Goals

**Goals**

- Attribute the `encodeRepeat` cost: memory bandwidth vs `Nat`/`Fin` index
  arithmetic vs sigma re-packaging vs `concat`/cast. (Measure first; do not
  guess.)
- Make the bulk encode approach a calibrated baseline (within ~10× of a
  `memcpy`/`memset`-speed lane measured on the same machine) and scale linearly.
- Make `decodeFull` beat `decodeRepeat` clearly by re-using consumed prefixes
  (no per-step re-attach/re-parse).
- Re-stage the bulk encode/decode through a contiguous `ByteArray`/`Array UInt8`
  accumulator behind the Lean runtime's `@[extern]` C primops, proved equal to the
  `Bytes n` spec, and tune the plain `cc` flags on the emitted C.

**Non-Goals**

- No semantic change: `Rel`, every law, and the `varint` denotation are
  unchanged. Zero `sorry`, zero `Classical.choice` throughout.
- No new carrier without a proof; a fast path is only acceptable if its
  refinement lemma is `[propext, Quot.sound]`-clean.
- No weakening of the bench's value checks to length checks.

## Decisions

### 1. Measure before optimizing (a dedicated profiling lane)

Add a profiling lane to `Bench.lean` that, per `encodeRepeat` run, separates:

- **bandwidth** — time a `memset`/`memcpy` of the same byte count (the
  calibration baseline);
- **representation** — time the same encode with the `concat`/sigma/`Fin`-sum
  arithmetic elided (an `unsafe` scratch accumulator, not part of `Codec`,
  purely to isolate the cost);
- **residual** — whatever is left after those two are subtracted.

This is the _first code-level_ task; the rest of the plan is conditioned on its
finding. The emitted IR (`Bench.c`/`Codec.c` under `.lake/build/ir/`) is read
directly, not assumed.

### 2. The single lever, chosen by the profiling result

- **Pure lowering (no new carrier).** Re-stage `encodeRepeat` from structural
  `concat` to a flat accumulator. §1's measurement ruled this **out**: the pure
  `Fin n → UInt8` function cannot be a flat accumulator while staying denotation-
  identical.
- **Law-backed bulk fast path.** A `ByteArray`/`Array UInt8` accumulator behind
  the Lean runtime's own `@[extern]` primops (`ByteArray.push`/`copySlice`/`get!`,
  hand-written C compiled by the plain `cc`), **with** refinement lemmas proving
  `fastEncodeRepeat p xs = encodeRepeat p xs` (and the decode dual). The prior
  tiers failed because the lemmas leaked `Classical.choice` through
  `Array.extract`; the proof must avoid that (use the carrier's pointwise
  `Bytes.ext`/cast lemmas, not `Array` content lemmas).

**§1's data selected the law-backed fast path.** `Bytes n` stays the specification
substrate for every law; the `ByteArray` accumulator is only a proved-equal
implementation for the bulk shapes.

### 3. Compiler flag tuning on the emitted C

`leanc` (the Lean C shim) compiles emitted C. The only compiler lever is adding
`-O3`/LTO/`-march=native`/PGO to the C compile of the emitted `*.c` and
re-measuring — a `default.nix`/`lakefile` change gated behind the proof gate.
(`@[extern]` primops are runtime C, compiled by the plain `cc`; no codegen-backend
change is involved.)

### 4. Bench stays a value-checked harness

The bench keeps asserting encoded/decoded _values_ (byte-for-byte), and the
`decodeFull` lane asserts against `decodeFull_some` (not `xs.length`). Throughput
is reported as ns/op and bytes/op vs the calibrated baseline, with a ×1/×2/×4
size sweep to expose scaling. No perf work is allowed to silently replace a
value check with a weaker one.

## Risks

- A bulk accumulator may subtly change `concat` cast order; the `concat_eq_splice`
  / `splice_cast_commute` substrate lemmas already prove the reassociation, so
  the risk is proof-shaped, not semantic.
- The fast path risks re-introducing a `Classical.choice` leak exactly where the prior
  tiers leaked it; the gate is `#print axioms` on the new refinement lemmas.
- Compiler-flag changes (`-march=native`) can make the bench non-reproducible
  across machines; the calibration baseline mitigates this by making comparisons
  relative to the same machine.
