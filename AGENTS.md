# AGENTS.md

Guidance for AI coding agents working in this repository.

## Project

`codec` — a verified, byte-exact, bidirectional codec library in Lean 4
(repo directory `lean-codec`). Takes Rendel & Ostermann's _Invertible Syntax
Descriptions_ (2010) and makes it dependently typed, provable, and binary.

Stdlib-only (no mathlib). Build with `lake build`; the proof gate is the same
build with zero `sorry`.

## Toolchain / environment: read first

**This is a Nix flake project. Every tool is in the flake `devShells.default`, not
on the host PATH.** Before doing anything, enter the dev shell:

```bash
nix develop
```

That shell provides the pinned `lean`/`lake` (Lean 4.34.1), `elan`, and the
**`openspec` CLI** (spec-driven workflow tool) — none of which are guaranteed to be
on the host. Then run the same commands (e.g. `openspec list --json`,
`openspec status --change … --json`, `lake build`, `nix build '.#bench'`).

Do **not**:

- search the host filesystem to locate tools (e.g. `find / -name openspec …`) —
  they live in the Nix store, reached via `nix develop`;
- assume `openspec`/`lake`/`lean` are already on PATH — check with `nix develop`
  first;
- fall back to hand-editing `openspec/` artifacts when `openspec` is unavailable
  on the host — get it from `nix develop`.

**Long builds (HARD RULE):** never run a long `nix build` (toolchain, bench, or
proof gate) in the foreground of a tool call, and never set a huge tool timeout
(`600000`/`900000` seconds = days-to-weeks — absurd and forbidden). Long-running
Nix builds cost real calendar time:

- launch them detached with `nohup … > /tmp/<name>.log 2>&1 &` and **poll** the
  log with short `bash` calls (seconds, not minutes) to check progress;
- keep the `bash` tool `timeout` small (≤ ~120s) for polling; keep blocking work
  tiny. If a command will exceed that, it must go detached;
- never `sleep` for minutes inside a single foreground call to "wait out" a
  build.

(For Nix usage details see the `nix` skill; this note is the project-specific
reminder that the toolchain is _flake-scoped_, not host-global.)

Source of truth:

- Task ledger: `openspec/changes/invertible-binary-core/tasks.md`.
- Reference paper: `PAPER.md`.
- Design rationale: `openspec/changes/invertible-binary-core/{proposal,design}.md` and `README.md`.

## Next session — handoff

> What's done, what's open, and the decisions to resolve before coding. Read first.

**Done** (compiles clean: zero sorries, zero warnings; `#print axioms Codec.roundtrip` ⇒ `[propext, Quot.sound]`):

- `Codec/Iso.lean` — `Iso` + folded combinators: `foldl` (§5.3), `foldr` (the
  right-fold dual, a _fresh_ well-founded recursion with step `Iso (β × α) α`,
  **not** `inverse ∘ foldl ∘ inverse` which is type-incoherent), `optionSome`,
  plus the structural isos (`nil`/`cons`/`unit`/`commute`/`associate`/`element`/
  `subset`/`inverse`). `[propext, Quot.sound]` only.
- `Codec/Codec.lean` (+`Rel`, `relRepeat`, `Productive`), `Codec/Decode.lean`
  (`decode`, `decodeRepeat`, `ConsumesByte`, `byteRepeat`), `Codec/Encode.lean`
  (`encode`, `encodeRepeat`), `Codec/Sound.lean` (the **unconditional** laws:
  `decode_spec`, `bidir`, `encode_rel`, `decode_encode`, `roundtrip`,
  `productive_iff_consumesByte`, `decodeRepeat_spec`, `encodeRepeat_rel`).
- `Codec/Combinators.lean` — §6.1/§6.2 derived combinators. **§9 resolved:**
  `partial def many` is **deleted** (its `Rel` was irreducibly opaque). Unbounded
  repetition is semantic, not a `Codec` value: `relRepeat` (denotation),
  `decodeRepeat p h` (decoder), `encodeRepeat p` (encoder). The `many`-shaped
  list combinators are re-derived over these three — `sepBy`/`sepBy1` as
  `relSepBy`/`decodeSepBy`/`encodeSepBy`, and `chainl1`/`chainr1` as
  `relChain*`/`decodeChain*`/`encodeChain*` (folds via the unchanged
  `Iso.foldl`/`Iso.foldr`, decoders taking `hsep : ConsumesByte …`), each with an
  unconditional `_spec`/`_rel` law. Finite combinators unchanged: `seqRight`/
  `seqLeft`/`between`, `optional`/`maybe`, `choice`, `count`/`manyUpTo`.
- `Codec/Codec.lean` also defines `abbrev Bytes := List UInt8` (the provable
  substrate, used everywhere the core wrote `List UInt8`; _reducible_, so every
  `List` lemma applies unchanged).
- `Codec/Buffer.lean` — the packed, `ByteArray`-backed **transport surface** (§10.4):
  `Buffer` (newtype over `ByteArray`), `toBytes`/`ofBytes` (routed through
  `ByteArray.data`, the reducible `Array`, _not_ the opaque `ByteArray.toList`),
  and the transported interpreters `decodeBuffer`/`encodeBuffer` with the
  bar-transferred laws `decodeBuffer_eq`/`encodeBuffer_eq`/`decodeBuffer_spec`/
  `roundtripBuffer`.
- `Codec/Sound.lean` also gained `relFunctional`/`relUnambiguous` (relation-level
  forms) and `encodeRepeat_ne_none`; `Codec/Combinators.lean` gained the six chain
  converse laws (§10.3a): `encodeChainl1_ne_none`/`encodeChainr1_ne_none`,
  `encodeChainl1_of_decode`/`encodeChainr1_of_decode` (under `relFunctional`),
  `encodeChainl1_injective_of_unambiguous`/`encodeChainr1_injective_of_unambiguous`
  (under `relUnambiguous`).

**Decisions already made** (read before continuing):

1. `Bytes` (= `List UInt8`) for the provable core; `Buffer` (a `ByteArray`-backed
   newtype) is the separate, later executable transport surface — _not_ the proof
   substrate.
1. **`|` is the paper's backtracking union, not committed choice** (restored;
   `NonNull`/`Disjoint`/`PrefixDisjoint` deleted). Do not reintroduce a
   deterministic/committed decoder.
1. `foldl`/`foldr` are done and proved; `chainl1`/`chainr1` are re-derived as
   semantic decoders/encoders over `decodeRepeat`/`encodeRepeat` (not `Codec` values).
1. `Codec` is an inductive description AST, not the paper's §3.4 typeclass.
1. `iterate` (paper §5.3) is deliberately omitted (no field law; forward/backward
   fixpoints can differ).
1. **Unbounded `many`/`some`/`sepBy`/`chainl1` are _semantic_, not `Codec`.** An
   infinite AST cannot be a finite `Codec`, and a `partial def` is proof-opaque;
   repetition lives as `relRepeat`/`decodeRepeat`/`encodeRepeat` (cf. §9).

**Open, in order** (full detail in `tasks.md` §11):

1. _*Efficiency — the F*-style carrier refinement (Paper §4.4, "work faster")._*
   **Tier A done** (`efficient-backtracking-decoder`, archived): `decodeFull`/
   `decodeRepeatFull`/`decodeFast` proved denotationally equal, `[propext, Quot.sound]`,
   ~20,000× on the full-consumption ask. **Tier B (buffer carrier) done** — the
   OpenSpec change **`openspec/changes/buffer-carrier-decoders/`** is implemented: the
   F* two-tier move (spec over `List`, run-model over `Array UInt8` + index,
   proved-equal) _without_ FFI or a compiler. Shipped: `Codec/DecodeArray.lean`
   (`decodeArray d a i : List (α × Nat)`, the relative-consumed internal `decodeArrayRel`,
   `decodeArray_eq`/`decodeArrayRel_eq`, the `decodeFull`-composed `decodeFullArray` +
   `decodeFullArray_spec`, helpers `decode_suffix`/`drop_add_length_of_append`/
   `flatMap_congr`), `Codec/EncodeArray.lean` (`encodeArray d x : Option (Array UInt8)`,
   `encodeArray_eq`), and three transfer laws in `Codec/Sound.lean` (`decodeArray_spec`,
   `encodeArray_rel`, `roundtripArray`) — all `[propext, Quot.sound]`-only. **Lesson 1:**
   `Array` is the reducible `List`-backed structure (`a.toList`, not `a.data`); the
   membership-form refinement `(x,j) ∈ decodeArray d a i ↔ (x, drop j) ∈ decode d (drop i)`
   is **wrong** for non-consuming `pure` (and empty remainders), because `drop` discards the
   index — use the function-level form `decodeArray d a i = (decode d (drop i)).map
(fun (x,r) => (x, i + (drop i).length - r.length))`, which is correct for every `d`.
   **Lesson 2:** the measured carrier win on the _non-LLVM_ toolchain is _not_ the
   design's hoped ~5–20× — stdlib `Array.size = a.toList.length` is structural O(n)
   (no cached length) when LLVM is compiled out, so `decodeArray`'s `i < a.size` guard
   walked the list each call. **Resolved by the `llvm-lean4-toolchain` change** (below):
   with LLVM enabled, `a.size` lowers to the `@[extern]` `lean_array_get_size` (O(1))
   and `a[i]` to `lean_array_fget_borrowed` (O(1)).
   The FFI/`@[extern]`/compiler tier stays a _separate, deferred_ change
   (authoring new `@[extern]` FFI and a custom compiler is still out of scope).
   **No FFI, no codegen, no `HashMap`, no chart parser in this change.**

> Resolved this session: §10.1 (namespace — no type rename; `Rel`/`relRepeat`/`Productive`
> now live at `Codec.*`), §10.1a/10.1b/10.1c (organization/naming/docs), §10.2
> (README/CHANGELOG/LICENSE), §10.3a (chain converse laws), §10.4 (`Buffer` transport),
> §10.5 (extraction + benchmark, see below). The `Codec` type was **not** renamed —
> Lean lets the type `Codec` and namespace `Codec` coexist; the fix was to restore the
> uniform `namespace Codec` in `Codec/Codec.lean`. New substrate/transport naming:
> `Bytes` = `abbrev Bytes := List UInt8` (proof substrate, reducible), `Buffer` = packed
> `ByteArray` newtype (`Codec.Buffer`, transport via `ByteArray.data`).

> **Extraction + benchmark (§10.5, task 1.6) — DONE this session.** Tooling decision:
> the pinned `lean4` 4.34.1 reports `--features []` and `-b` (LLVM) asserts
> `-DLLVM=ON`, so extraction is the **C backend** (`lake env lean -c`, and lake's own
> `lean_exe` link emitting `.c`/`.c.o` under `.lake/build/ir/`) — no LLVM toolchain
> provisioned. Deliverable: `Bench.lean`, a top-level `lean_exe` (root-level `main`) that
> drives `decode`/`encodeRepeat`/`decodeRepeat`/`Buffer.ofBytes`/`Buffer.toBytes` on a
> synthetic `byte`/`many` description; wired as `default.nix#bench` (installs `bin/bench`,
> `meta.mainProgram = "bench"`) and `flake.nix#packages.<system>.bench`. **Measured
> (arm64, reps=20):** `encodeRepeat`/`Buffer.ofBytes`/`Buffer.toBytes` scale linearly
> (64 ms / 8 ms / 14 ms at 2 MiB); `decode byte` is O(1) (~100 ns); the backtracking
> `decodeRepeat byte [16384]` ≈ 13.8 s (quadratic, paper §4.4 — the §10.6 target).
> Hot-path audit clean: `decode` uses `match` (no `getElem`-with-proof leak),
> `Buffer.toBytes` uses `ByteArray.data` (reducible `Array`), not the opaque
> `ByteArray.toList`. `lake build` (proof gate) stays `defaultTargets = ["codec"]`;
> the `bench` exe is built only via `lake build bench` / the Nix `bench` derivation.

> **Efficiency (Tier A) — DONE this session** (`efficient-backtracking-decoder`).
> `decodeFull`/`decodeRepeatFull` (`Codec/Decode.lean`, `Option (List α)` full-consumption
> "many", `WellFounded.fix` on `s.length`, no `partial`) and `decodeFast` (list-fused
> `decode`, `map` replacing `flatMap`-over-singleton in `seq`) are proved
> denotationally equal (`decodeFull_spec` under a full-consumption-uniqueness
> hypothesis `huniq`; `decodeFast_eq` via `List.map_eq_flatMap`; transfer laws
> `decodeFast_spec`/`bidir_decodeFast`/`roundtrip_decodeFast`/`decodeRepeatFull_spec`
> in `Sound.lean`), all `[propext, Quot.sound]`-only. `Bench.lean` gained
> `decodeFull`/`decodeRepeatFull`/`decodeFast` legs; measured **~20,000× faster**
> (`decodeFull byte [16384]` = 545 µs vs `decodeRepeat` = 11.2 s). **Tier B
> (memoizing chart) is a separate, deferred change.**

> **LLVM toolchain (Tier B carrier speedup) — DONE this session**
> (`llvm-lean4-toolchain`). The `buffer-carrier-decoders` run-model was _correct but
> slow_ because the pinned `lean4` was built **without LLVM**, so `Array`/`ByteArray`
> fell back to pure-`List` (`Array.size = List.length` O(n), no `@[extern]` C++
> primops), and `lake build bench` even failed to link (`ld: library 'c++' not found`).
> **Fix (no FFI, no compiler authored — a stock build-configuration change):**
> build `lean4` with `LLVM=ON` and the _consistent_ LLVM 19 toolchain
> (`llvmPackages_19.stdenv` — clang 19.1.7 + libc++ 19.1.7 + llvm 19.1.7), wiring it
> into every path (`default.nix`'s `lean4` input, `flake.nix`'s dev shell + packages).
> Two non-obvious findings (see `openspec/changes/llvm-lean4-toolchain/design.md`):
>
> - `-DLLVM=ON` must be a **raw** string flag (`:BOOL=` typing makes it a `BOOL` cache
>   var that Lean's top-level `CMakeLists.txt` does not forward to the stage0/stage1
>   `ExternalProject` sub-builds, silently disabling LLVM in every stage).
> - The **whole toolchain** must be LLVM 19, not just `llvm` libs: upstream
>   `lean_llvm_parse_bitcode` aborts on cross-major bitcode (`Unknown attribute kind
(102) (Producer: 'LLVM21.1.8' Reader: 'LLVM 19.1.7')`), so mixing the host stdenv's
>   clang 21 with `llvmPackages_19.llvm` fails at stage1 stdlib build.
>   **Result:** `lean --features` ⇒ `[LLVM]`; `lake build bench` links (libc++ present);
>   the extracted `decodeArray byte` lowers to `lean_array_get_size`/`lean_array_fget_borrowed`
>   (O(1), confirmed flat ~73–188 ns over a 1024× size range) vs the O(n) `List.length`
>   baseline. Proof gate green, axiom record unchanged (`[propext, Quot.sound]`).
>   The author-FFI/compiler tier remains deferred; this is only the standard Lean build
>   configuration flipped on.

> **Documentation conventions (this session):** the README is the **full
> architecture statement** — _about the project and the paper only_. It carries the
> complete `[D1]`–`[D8]`/`[S1]`–`[S6]` departures/strengthenings (each with a layman
> "why"), and a short getting-started at the bottom. It has **no** status/issues
> section and **no** process/history narrative (the project is greenfield/unreleased;
> "we used to / reverted / formerly" belongs to `openspec/`'s task ledger, never the
> README). Engineering state = `openspec/` + this file; user-facing docs = README +
> `CHANGELOG.md` + `LICENSE.md`. When adding code, keep every departure/
> strengthening cross-referenced to a `[D#]`/`[S#]` anchor in the README table, and
> keep the axiom record consistent (`[propext, Quot.sound]`, never the stale
> `Classical.choice`).

## Openspec workflow

This repo uses OpenSpec (spec-driven). Changes live under
`openspec/changes/`. Planning artifacts (proposal / spec delta / design / tasks)
are created before implementation; see `.pi/prompts/opsx-*.md`.

## Git conventions

- Commit **individual files**, never `git add -A` or broad globs. Print the exact
  staged set before committing.
- `lake-manifest.json` and `flake.lock`: `lake-manifest.json` is gitignored
  (library shouldn't pin deps); `flake.lock` (Nix) _is_ tracked for reproducibility.

## Skills

- Global Lean theorem-proving skill: `lean4` (official).
- Our supplement (project-layout, proving-over-primitives, `partial`/coinduction
  lessons): global skill `lean`. Keep it generic — no project-specific details.
- Lean PR/convention/proof/MWE skills: `lean-pr`, `lean-bisect`, `lean-proof`,
  `lean-mwe`, `mathlib-build`, `mathlib-pr`, `mathlib-review`, `nightly-testing`,
  `lean4-setup` (all under the `leanprover` skill family).
- Nix tooling: **multiple Nix skills exist** — the repo is a Nix flake
  (`flake.nix`/`default.nix`); use `devenv` / `devenv-migration` only when actually
  migrating to devenv, never for this flake's own `devShells.default` (which is
  plain `pkgs.mkShellNoCC`).
