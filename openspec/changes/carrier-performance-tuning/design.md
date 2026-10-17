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

The read path is already there; the bulk paths are not. The `lean4-llvm`
override in `default.nix` builds LLVM 19 into Lean but its only purpose (the
`Array`/`ByteArray` `@[extern]` primops) is **dormant** on the single carrier —
`encodeRepeat`/`decodeRepeat`/`decodeFull` never touch `Array`/`ByteArray`, so
LLVM is currently contributing nothing to the hot path beyond whatever `leanc`
does by default.

## Goals / Non-Goals

**Goals**

- Attribute the `encodeRepeat` cost: memory bandwidth vs `Nat`/`Fin` index
  arithmetic vs sigma re-packaging vs `concat`/cast. (Measure first; do not
  guess.)
- Make the bulk encode approach a calibrated baseline (within ~10× of a
  `memcpy`/`memset`-speed lane measured on the same machine) and scale linearly.
- Make `decodeFull` beat `decodeRepeat` clearly by re-using consumed prefixes
  (no per-step re-attach/re-parse).
- Either _utilize_ LLVM on the hot path (a law-backed `@[extern]`/`Array`
  accumulator, or drive `leanc -O3`/LTO/PGO/march on the emitted C) or _remove_
  the dormant override — no dead machinery left either way.

**Non-Goals**

- No semantic change: `Rel`, every law, and the `varint` denotation are
  unchanged. Zero `sorry`, zero `Classical.choice` throughout.
- No new carrier without a proof; a fast path is only acceptable if its
  refinement lemma is `[propext, Quot.sound]`-clean.
- No weakening of the bench's value checks to length checks.

## Decisions

### 1. A/B plain `lean4` vs `lean4-llvm` first (cheap, decisive)

Before touching any loop, build the bench with the plain nixpkgs `lean4` and
with `lean4-llvm` on the same source and record both tables. The override exists
only for the deleted `Array`/`ByteArray` `@[extern]` path, which `Bytes n` never
hits, so the most likely outcome is **LLVM is neutral** — in which case the
override and its clang-19 pin are removed as dead weight (a real win for every
`nix develop`/`nix build`), and "utilize LLVM" becomes nothing unless a later
lever re-introduces a primop seam. If LLVM _does_ help a lane, that lane is
recorded and §4 tunes those flags deliberately. This is measured, not assumed.

### 2. Measure before optimizing (a dedicated profiling lane)

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

### 3. Two candidate levers, chosen by the profiling result

- **Lever A — pure lowering (no new carrier).** Re-stage `encodeRepeat` from
  structural `concat` (which pays `Fin`-sum concat and a cast per `cons`) to a
  single flat accumulator that appends into a pre-sized buffer and does the
  length-cast once at the end. This keeps `Bytes n` as the only carrier, keeps
  every law, and only changes _how_ the encoded result is assembled.
- **Lever B — law-backed fast path (re-introduce the seam, but proved).** If
  Lever A cannot reach the baseline, re-introduce an `Array`/`ByteArray`
  accumulator behind an `@[extern]` (LLVM-primop) surface, **with** refinement
  lemmas proving `fastEncodeRepeat p xs = encodeRepeat p xs` (and the decode
  dual). The prior tiers failed because the lemmas leaked `Classical.choice`
  through `Array.extract`; the proof must avoid that (use the carrier's
  pointwise `Bytes.ext`/cast lemmas, not `Array` content lemmas).

The decision is made by data, not by preference: Lever A is preferred if it
reaches the baseline (subtask, no new carrier); Lever B is only pursued if A
falls short and a clean proof is found.

### 4. LLVM utilization is explicit

`leanc` (the Lean C shim) compiles emitted C with a fixed set of flags. To
"utilize LLVM," either (a) Lever B puts LLVM's `@[extern]` primops on the hot
path, or (b) the bench derivation adds `-O3`/LTO/`-march=native`/PGO to the C
compile of the emitted `*.c` and re-measures. Both are `default.nix`/`lakefile`
changes gated behind the proof gate. The A/B test (Decision 1) sets the baseline
for whether this is even worth pursuing; if plain `lean4` already matches
`lean4-llvm`, the override is removed rather than tuned.

### 5. Bench stays a value-checked harness

The bench keeps asserting encoded/decoded _values_ (byte-for-byte), and the
`decodeFull` lane asserts against `decodeFull_some` (not `xs.length`). Throughput
is reported as ns/op and bytes/op vs the calibrated baseline, with a ×1/×2/×4
size sweep to expose scaling. No perf work is allowed to silently replace a
value check with a weaker one.

## Risks

- A bulk accumulator may subtly change `concat` cast order; the `concat_eq_splice`
  / `splice_cast_commute` substrate lemmas already prove the reassociation, so
  the risk is proof-shaped, not semantic.
- Lever B risks re-introducing a `Classical.choice` leak exactly where the prior
  tiers leaked it; the gate is `#print axioms` on the new refinement lemmas.
- Compiler-flag changes (`-march=native`) can make the bench non-reproducible
  across machines; the calibration baseline mitigates this by making comparisons
  relative to the same machine.
