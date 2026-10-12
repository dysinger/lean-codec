# Design

## Context

The repo already has the full two-tier shape: a spec over `Bytes = List UInt8`,
and a `ByteArray`-carrier run-model proved equal to it. The LLVM toolchain change
made `ByteArray.get`/`size` genuine O(1) `@[extern]` primops. The remaining gap
is on the _speed_ axis, and it is now precisely diagnosed: Lean 4 has a **single
C code generator** (`Lean.Compiler.LCNF.EmitC`) that emits a boxed, GC'd,
reference-counted representation — `Nat` as bignum `lean_object *`, `List UInt8`
as cons cells, higher-order values as `lean_alloc_closure`. There is **no
"unboxed C" target to select**.

F\* solved this with **KaRaMeL**, and the solution is understood and transferable
(see the studied reference: `../fstar` at `v2026.09.20`, pulse C library
`pulse/lib/pulse/c/Pulse.C.Types.*`, and `../karamel` — `DESIGN.md`, `include/krmllib/*`,
`src/AstToCStar.ml`).

This design plans the **separate Lean target** that brings the same idea to Lean:
a _real, additional code-generation backend_ that lowers a proved subset of LCNF
to **GC-less C** (KaRaMeL-mould). It is deliberately **not** a post-pass over the
C that `EmitC` already emits, and **not** a `lake` library in this repo.

## The reference pipeline (KaRaMeL), mapped to Lean

KaRaMeL's `DESIGN.md` pipeline, with the Lean 4.34.1 compiler counterpart for
each stage:

| KaRaMeL stage                                       | KaRaMeL module                     | Lean 4.34.1 counterpart (`src/lean`)             |
| --------------------------------------------------- | ---------------------------------- | ------------------------------------------------ |
| load typed input AST                                | `InputAst.ml` / `InputAstToAst.ml` | LCNF `Decl` (the IR already fed to codegen)      |
| expand abbrevs                                      | `Inlining.ml`                      | LCNF mono/impure phases                          |
| monomorphize data types                             | `DataTypes.ml`                     | `LCNF/MonoTypes.lean`, `LCNF/Specialize.lean`    |
| drop tuples; simplify to structs/enums/conditionals | `DataTypes.ml`                     | `LCNF/Simp/*`                                    |
| expr→statement hoisting, casts, name munging        | `Simplify.ml`                      | `LCNF/InferType`, `LCNF/PullLetDecls`            |
| typed, no-GC C surface                              | `AstToCStar.ml`                    | **NEW: `EmitNoGC`** (parallel to `EmitC`)        |
| C pretty-print                                      | `PrintC.ml`                        | **NEW: emit C directly** (no separate AST stage) |
| minimal runtime                                     | `include/krmllib/*.h`              | **NEW: a minimal no-GC runtime header**          |

(Note: KaRaMeL's `CStar.ml`/`AstToCStar.ml`/`CStarToC.ml` are _file names tied to
F★'s typed AST_ — "C★" is a pun on the F★ language. Lean has no such AST, so
those stage names do **not** carry over; the Lean counterpart is one `EmitNoGC`
emitter that prints C directly from LCNF. Only the _type map_ and the _no-GC
header shape_ are reused, not the `CStar` vocabulary.)

The two _essential_ new pieces (the "no-GC" core) are:

1. **A representation/boxing pass** that performs KaRaMeL's primitive _type
   mapping_. This is the whole game. Today `LCNF/ExplicitBoxing.lean` +
   `ExplicitRC.lean` decide the boxed representation; the new target instead
   maps:
   - `Nat` → `size_t` (loop indices, measures, lengths) — erasing the
     `WellFounded.fix` measure that exists only for Lean's termination proof;
   - `List UInt8` / `Bytes` → the slice `(uint8_t *, size_t)` (the
     `FStar_Bytes_bytes` representation studied in `krmllib`);
   - `ByteArray` → `uint8_t *` + `size_t` (its `LeanScalarArray` data is already
     contiguous);
   - `UInt8`/machine ints → `uint8_t`/`uint32_t`/… (the `size_t`/`uintN_t` map,
     studied in `krmllib`'s `types.h`);
   - no closures: the subset must be first-order, so `WellFounded.fix`'s `ih`
     and `decodeFullByteArrayStep`'s `attach` are _loops_, not `lean_alloc_closure`.
2. **An `EmitNoGC` emitter** that, given a `Decl` satisfying
   the subset, prints the unboxed C: `lean_object` → nothing, RC calls
   (`lean_inc_ref`/`lean_dec_ref`) → nothing, `Nat` arithmetic → `size_t`, list
   construction → destination-buffer writes + `(ptr, len)`.

The "no runtime / no GC" result is then automatic, exactly as in KaRaMeL: the
only runtime is a few headers of macros/`typedef`s (no allocator beyond libc
`malloc`/`free`, no GC, no tracing).

## Goals / Non-Goals

### Goals

- Specify a **real, separate Lean code-generation target** ("GC-less C") as a
  new backend in the Lean compiler toolchain — same proven inputs
  (`decodeByteArray`/`decodeFullByteArray`/`encodeByteArray`), _different_
  emitted C — so per-byte cost drops from ~33 ns toward the `memchr`/`simdjson`
  ballpark (~0.5–1 ns/byte).
- Ship the **memory model** justifying the lowering (`ByteArray = uint8_t * +
size`; slice result `(ptr, len)`), proved where reachable, otherwise a
  **named trust seam** (the F\* stance toward KaRaMeL; the Pulse C primitives'
  stance toward `read0`/`emplace`).
- **Exercise it**: `Bench.lean` tier lane driving the _new target's output_ on
  the same inputs, recording per-byte before/after against `List`, boxed
  `ByteArray`, and a `memchr` baseline. Acceptance: raw-byte path within ~2× of
  `memchr`, no regression on existing interpreter lanes.

### Non-Goals

- **Not** a general Lean→C _verified_ compiler (Hydropus/CompCert-scale). We
  author a _trusted_ backend for this one run-model's hot path.
- **Not** a post-processing rewrite of `EmitC`'s `.c` output — this is a
  **separate target**, a new emitter, not a text transform of the existing one.
- **Not** changing codec semantics, the `Bytes` substrate, or any law. The codec
  stays `[propext, Quot.sound]`-only.
- **Not** proof-carrying the backend itself in this change; the backend is a
  named, isolated trust seam (recorded), exactly as F\* trusts KaRaMeL.

## Decisions

1. **This is a separate target, not a source rewrite and not a C post-pass.**
   The lowering operates on LCNF `Decl`s (the IR `EmitC` already consumes), via a
   _new_ `EmitNoGC` module, selected by a new driver flag. The
   existing `EmitC`/LLVM path is untouched.

2. **This is a separate project (the KaRaMeL relationship).** The backend has
   its own dependency surface (it consumes Lean's emitted IR or is built into a
   patched `lean` binary; it emits C; it links its own no-GC runtime) and its own
   proof story (a trusted seam, not a `[propext, Quot.sound]` library law). It
   is to `lean-codec` what KaRaMeL is to F\*/HACL\*: a downstream tool consuming
   a proved library, versioned independently.

3. **Result is a slice `(uint8_t *, size_t)`, not a `List`.** The single biggest
   cost is `List UInt8` cons-cell allocation. The tier routes output into a
   pre-sized destination buffer and returns a slice; the `Bytes` list remains the
   _spec_, materialized only at the boundary (and, for full-consumption, returned
   as a zero-copy slice).

4. **The byte loop lowers to a bounds-checked `while`/`for`, `Nat` erased to
   `size_t`.** `decodeFullByteArray` is a `WellFounded.fix` on `a.size - i`; under
   the tier the recursion becomes an index-incrementing loop with one `i < size`
   check (vectorizable). The `Nat` measure is erased — it exists only to justify
   termination in Lean.

5. **Memory model: prove `ByteArray` read/writes = `uint8_t *` ops, or name-trust
   them.** Ideally a lemma `ByteArray.get a i = uint8_read (data_ptr a) i` closes
   `decodeByteArray_eq` against the spec. If the C memory model is too heavy,
   name it a trust seam (like F\* trusts KaRaMeL) and record it; the codec laws
   stay `[propext, Quot.sound]`, the seam isolated at the buffer edge.

6. **`skip_specs: true`.** The codec's denotation is unchanged; this is a
   performance backend.

7. **The benchmark is the acceptance gate.** "Fast" is a measured number.

## The source subset (the Low\* analog)

KaRaMeL produces no-GC C only because Low\* restricts the input: first-order,
non-recursive data types, no closures, explicit machine-int wording. The Lean
equivalent subset for the new target is:

- **first-order** — no `lean_alloc_closure`; `WellFounded.fix` recursion must be
  lowered to `while`/`for` (the measure erased), which means the emitter
  recognizes the specific `decodeFullByteArrayStep`/`attach` shape and emits a
  loop;
- **monomorphic** — `Nat → size_t`, `UInt8 → uint8_t`, `List UInt8 → (uint8_t *,
size_t)`, `ByteArray → uint8_t * + size_t`; no polymorphic `Codec` recursion
  over arbitrary `α` (the _hot path_ is specialized to `UInt8`/`Nat` reads);
- **no GC boxes** — nothing allocates a `lean_object` in the hot path; RC is
  erased.

Declarations outside this subset fall back to the existing `EmitC` (boxed) path
— the new target is selected per-declaration (or per-module), exactly as KaRaMeL
drops non-Low\* modules.

## Wiring: how the new target gets into Lean from this repo

Lean's codegen is compiled into the `lean`/`leanir` binary: `LCNF` `Decl`s flow
through `PassManager.run` (`Lean.Compiler.LCNF.Main`) into `IR.toIR`/`IR.compile`.
The **C** backend is `LCNF/EmitC.lean` (emits `lean_object` C); the **LLVM**
backend is `IR/EmitLLVM.lean`. A new target plugs in at the same seam. Two
concrete wiring options, in order of fidelity to "a real separate target":

- **A. Patch the Lean compiler toolchain** (what "a real target" means): add
  `EmitNoGC` + the representation/boxing pass + a driver flag
  (`lean --target=nogc` or a `leanc`-variant) to the pinned `lean4` (as the
  `llvm-lean4-toolchain` change already rebuilds `lean4` with `LLVM=ON`). The
  backend lives in the compiler, selected per-decl/module; this is the
  KaRaMeL-fidelity path but requires building/maintaining a patched `lean`.
- **B. A separate `leanir`-driven tool** consuming LCNF export: a standalone
  executable (like KaRaMeL consumes F\*'s typed AST) that reads Lean's emitted
  IR for the chosen defs and emits unboxed C. Lower fidelity to "inside the
  compiler", but keeps the toolchain stock and the backend in its own repo.

**Recommended:** **A** for the target itself (it is the only thing that is
honestly "a separate Lean target"); the backend repo is wired into this repo's
`flake.nix` as a _new Nix derivation_ (e.g. `packages.nogc` / a `backend` input)
whose build runs the patched `lean --target=nogc` over
`decodeByteArray`/`decodeFullByteArray`/`encodeByteArray`, emits `*.c`, links
against the minimal no-GC runtime header (no `lean_rt`), and installs a `bench`
lane alongside the existing §10.5 bench.

## Risks / Trade-offs

- _[The `Nat → size_t` erasure is unsound for arbitrary code]_ → the subset
  restricts `Nat` to a bounded, measure-only role in the recognized hot path;
  anything else falls back to boxed `EmitC`. Overflow/width is made explicit on
  the `size_t` boundary (KaRaMeL's `KRML_CHECK_SIZE`).
- _[`WellFounded.fix` → loop lowering is shape-specific]_ → the emitter matches
  the known `decodeFullByteArrayStep`/`attach` pattern; a general
  `WellFounded.fix`-to-loop pass is out of scope (documented).
- _[A slice result may dangle if the buffer is freed]_ → document "slice valid
  while the source `ByteArray` lives"; Rust/Lean-side ownership is out of scope
  (same caveat KaRaMeL's `FStar_Bytes_bytes` carries).
- _[Building a patched `lean` is heavy / slow]_ → bounded by the existing
  `llvm-lean4-toolchain` experience (already rebuilds `lean4` with LLVM); the
  new emitter is additive Lean code plus a flag, built once via Nix.
- _[Authoring any back end is a real compiler]_ → acknowledged; scoped to one
  hot path; growth toward a general backend is a separate follow-up.

## Migration Plan

1. Stand up the separate backend project (new repo) with the `EmitNoGC`
   naming, the representation/boxing pass, the minimal no-GC runtime header, and
   the driver flag — wired into this repo's `flake.nix` as a Nix derivation.
2. Lower `decodeByteArray`'s `byte` case and `decodeFullByteArray`'s
   `WellFounded.fix` recursion to unboxed C under the new target; `encodeByteArray`
   to buffer appends.
3. Add the `Bench.lean` tier lane against `memchr`; run it; record before/after.
4. Verify the proof gate (`lake build` zero `sorry`, `[propext, Quot.sound]`) and
   `nix build .#bench` green; update `AGENTS.md` handoff + README.
5. Rollback = remove the backend derivation + bench lane (no change to existing
   proven core).

## Open Questions

- Whether the memory model can be _proved_ in-Lean (`ByteArray.get = uint8_read`)
  or must be a named trust seam — decided by how far `ByteArray.data` reduces
  against the C primops.
- Whether "separate target" means a full patched `lean` (A) or a `leanir`-driven
  tool (B); A is recommended for fidelity, B for toolchain-stability.
- The exact per-byte acceptance threshold (within 2× of `memchr`) — resolved from
  the first measured tier output.
