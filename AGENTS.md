# AGENTS.md

Guidance for AI coding agents working in this repository.

## Project

`codec` — a verified, byte-exact, bidirectional codec library in Lean 4
(repo directory `lean-codec`). Takes Rendel & Ostermann's *Invertible Syntax
Descriptions* (2010) and makes it dependently typed, provable, and binary.

Stdlib-only (no mathlib). Build with `lake build`; the proof gate is the same
build with zero `sorry`.

Source of truth:
- Task ledger: `openspec/changes/invertible-binary-core/tasks.md`.
- Reference paper: `PAPER.md`.
- Design rationale: `openspec/changes/invertible-binary-core/{proposal,design}.md` and `README.md`.

## Next session — handoff

> What's done, what's open, and the decisions to resolve before coding. Read first.

**Done** (compiles clean: zero sorries, zero warnings; `#print axioms
Codec.roundtrip` ⇒ `[propext, Quot.sound]`):
- `Codec/Iso.lean` — `Iso` + folded combinators: `foldl` (§5.3), `foldr` (the
  right-fold dual, a *fresh* well-founded recursion with step `Iso (β × α) α`,
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
  substrate, used everywhere the core wrote `List UInt8`; *reducible*, so every
  `List` lemma applies unchanged).
- `Codec/Buffer.lean` — the packed, `ByteArray`-backed **transport surface** (§10.4):
  `Buffer` (newtype over `ByteArray`), `toBytes`/`ofBytes` (routed through
  `ByteArray.data`, the reducible `Array`, *not* the opaque `ByteArray.toList`),
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
   newtype) is the separate, later executable transport surface — *not* the proof
   substrate.
2. **`|` is the paper's backtracking union, not committed choice** (restored;
   `NonNull`/`Disjoint`/`PrefixDisjoint` deleted). Do not reintroduce a
   deterministic/committed decoder.
3. `foldl`/`foldr` are done and proved; `chainl1`/`chainr1` are re-derived as
   semantic decoders/encoders over `decodeRepeat`/`encodeRepeat` (not `Codec` values).
4. `Codec` is an inductive description AST, not the paper's §3.4 typeclass.
5. `iterate` (paper §5.3) is deliberately omitted (no field law; forward/backward
   fixpoints can differ).
6. **Unbounded `many`/`some`/`sepBy`/`chainl1` are *semantic*, not `Codec`.** An
   infinite AST cannot be a finite `Codec`, and a `partial def` is proof-opaque;
   repetition lives as `relRepeat`/`decodeRepeat`/`encodeRepeat` (cf. §9).

**Open, in order** (full detail in `tasks.md` §11):

1. **Extraction + benchmark** (task §10.5) — extract the `decode`/`encode` hot
   path (and `decodeRepeat`/`encodeRepeat`) to C/LLVM, benchmark a multi-MB
   roundtrip (`byte`/`many`) proving **linear time, no per-byte boxing**, and
   audit `get!`/remaining-bytes/`Buffer.data` for `getElem`-with-proof leaks.
   **Decision first (blocking):** the pinned `lean4` 4.34.1 Nix build reports
   `--features []` (no LLVM/C backend provisioned). Either use `lake env lean
   file.lean -c file.c` (the C backend the build already exercises) or provision
   an LLVM toolchain via the flake. Benchmark home is downstream `lean-binary`.
   Covers task 1.6.
2. **Efficiency (paper §4.4 open problem)** — **last**, a **separate**
   `efficient-backtracking-decoder` change (memoization/DP over the *same*
   denotation; never changes semantics).

> Resolved this session: §10.1 (namespace — no type rename; `Rel`/`relRepeat`/`Productive`
> now live at `Codec.*`), §10.1a/10.1b/10.1c (organization/naming/docs), §10.2
> (README/CHANGELOG/LICENSE), §10.3a (chain converse laws), §10.4 (`Buffer` transport).
> The `Codec` type was **not** renamed — Lean lets the type `Codec` and namespace
> `Codec` coexist; the fix was to restore the uniform `namespace Codec` in
> `Codec/Codec.lean`. New substrate/transport naming: `Bytes` = `abbrev Bytes :=
> List UInt8` (proof substrate, reducible), `Buffer` = packed `ByteArray` newtype
> (`Codec.Buffer`, transport via `ByteArray.data`).

> **Documentation conventions (this session):** the README is the **full
> architecture statement** — *about the project and the paper only*. It carries the
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
  (library shouldn't pin deps); `flake.lock` (Nix) *is* tracked for reproducibility.

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
