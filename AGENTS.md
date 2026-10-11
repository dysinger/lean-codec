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
   ~20,000× on the full-consumption ask. **Next step is the buffer-carrier tier** — the
   new OpenSpec change **`openspec/changes/buffer-carrier-decoders/`** (proposal/design/
   tasks, `skip_specs: true`). It is the F* two-tier move (spec over `List`, run-model
   over `Array UInt8` + index, proved-equal) _without_ FFI or a compiler: `decodeArray d a i
: List (α × Nat)` / `encodeArray d x : Option (Array UInt8)` native on the array, plus
   `decodeArray_eq`/`encodeArray_eq` (the single refinement lemma) and transferred laws.
   **Read `design.md` before coding; the next session starts there.** The sequencing is
   deliberate: see it work → work faster (this change) → later, after real use, work
   the fastest possible (FFI/`@[extern]`/compiler — explicitly a _separate, deferred_
   change, not part of this one). **No FFI, no codegen, no `HashMap`, no chart parser
   in this change.**

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
