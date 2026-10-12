# Tasks

> The compiler tier is now the **active plan**; earlier "deferred" notes are
> superseded (not rewritten — they remain accurate history). The primary
> deliverable of this change is the _plan_ for a real, separate, GC-less C
> extraction target (the KaRaMeL-to-F\* relationship), plus its first
> scaffolding and benchmark gate.

## 0. Plan-of-record gate (this change's first deliverable)

- [ ] 0.1 Record the superseding decision: the compiler tier is now active; the
      FFI/compiler-tier work is a **separate target** (a new Lean code-generation
      backend), **not** a C post-pass and **not** a `lake` library. Keep archived
      "deferred" notes intact as history.
- [ ] 0.2 Fix the prior `compiler-tier-extraction` proposal/design/tasks (which
      had conflated "author a lowering" with "non-goal: no full compiler") to the
      plan above.

## 1. The separate backend target (its own repo, KaRaMeL-shaped)

- [ ] 1.1 Stand up the backend project: module layout mirroring KaRaMeL's stages
      — `EmitNoGC`/`EmitCStar` (parallel to `Lean.Compiler.LCNF.EmitC`), a
      representation/boxing pass (parallel to `ExplicitBoxing`/`ExplicitRC`/
      `MonoTypes`), a `PrintCStar`/`CStarToC` last stage, and a minimal no-GC
      runtime header (`krmllib.h`-shaped: `target.h`, `types.h`,
      `lowstar_endianness.h`, `fstar_int.h`).
- [ ] 1.2 Specify and implement the **primitive type mapping** (the no-GC core):
      `Nat → size_t`, `UInt8 → uint8_t`, `List UInt8`/`Bytes → (uint8_t *, size_t)`
      (KaRaMeL's `FStar_Bytes_bytes`), `ByteArray → uint8_t * + size_t`; no
      `lean_object`, no RC in the hot path.
- [ ] 1.3 Specify the **source subset** (the Low\* analog): first-order, no
      closures, monomorphic over the hot path; `WellFounded.fix` recursion
      recognized and lowered to `while`/`for` (measure erased); out-of-subset
      declarations fall back to the existing `EmitC`.

## 2. Lower the run-model hot path under the new target

- [ ] 2.1 Lower `decodeByteArray`'s `byte` case to a `uint8_t *` read + index
      increment (no `List` cell, no `Nat`-measure recomputation).
- [ ] 2.2 Lower `decodeFullByteArray`'s `WellFounded.fix` recursion to a
      bounds-checked `while`/`for` over the buffer, producing the slice result
      (`Nat` measure erased — it exists only for Lean's termination proof).
- [ ] 2.3 (encode) Lower `encodeByteArray`'s accumulation to appends into a
      pre-sized `uint8_t *` buffer (amortized O(n), no per-byte box).

## 3. Wire the target into Lean from this repo, and exercise it

- [ ] 3.1 Wire the backend into the toolchain: a patched `lean --target=nogc`
      (option A) or a standalone `leanir`-driven tool (option B), surfaced as a
      new Nix derivation in this repo's `flake.nix` (per `default.nix`'s existing
      `lean4` override pattern from `llvm-lean4-toolchain`).
- [ ] 3.2 Add a `Bench.lean` **tier lane** driving the _new target's output_ (not
      the interpreter) on `decodeByteArray byte` / `decodeFullByteArray byte` /
      `encodeByteArray byte`, plus a `memchr` (or equivalent hand-tuned C)
      baseline for the head-to-head.
- [ ] 3.3 Run it; record per-byte figures vs the `List` spec, the boxed
      `ByteArray`, and the `memchr` baseline. Acceptance: raw-byte path within
      ~2× of `memchr`; no regression on the existing interpreter lanes.

## 4. Integration gate + documentation

- [ ] 4.1 `lake build` (zero `sorry`/warnings), `#print axioms Codec.roundtrip` ⇒
      `[propext, Quot.sound]`, and `nix build .#checks.<system>.lean` + `nix build
.#bench` green.
- [ ] 4.2 Record the measured numbers and the **prove-vs-trust seam decision**
      (named-trust, as F\* trusts KaRaMeL, unless a per-function refinement proof
      is reachable) in the README (`Representations — two byte types, two jobs`
      gains a "compiler tier" note) and the `AGENTS.md` handoff /
      `invertible-binary-core/tasks.md` ledger.
- [ ] 4.3 The **lighter-weight `@[extern]` C fast-path stopgap** is now its own
      change: **`extern-c-fast-path`** (landing first, before this full backend).
      This change stays the end goal; `extern-c-fast-path` de-risks the `memchr`
      baseline and `(ptr, len)` slice representation up front.
