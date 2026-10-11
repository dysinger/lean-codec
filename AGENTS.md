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

**Decisions already made** (read before continuing):
1. `List UInt8`, not `ByteArray`, for the provable core.
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

**Open, in order** (full detail in `tasks.md` §10):

1. **Code organization, naming, documentation** (tasks §10.1a/10.1b/10.1c) — re-lay
   out each `Codec/*.lean` file first-principles (bottom-up: `Iso` → `Codec`/`Rel` →
   `Decode`/`Encode` → `Sound` → `Combinators`), constructor-order/alphabetize sibling
   groups, name to mathlib convention, delete dead `app`/`unapp`, reconcile `comp`/`trans`
   and the `foldrApply'` prime, and document **every** public declaration to standard
   (one-line `/-` what+why, `/-!` section outlines, paper § and README `[D#]`/`[S#]`
   cross-refs).
2. **`Codec` type-vs-module rename** (task §10.1) — decide `Desc`/`Syntax` vs. keeping
   `Codec` with a single namespace; move `Rel`/`relRepeat` into the same namespace as the
   interpreters. Do **before** README/downstream hard-code names.
3. **README rewrite** (task §10.2) — after the rename; the `[D#]`/`[S#]` canonical table
   and "Why these choices?" layman section are already written, only names need re-check.
4. **Chain-combinator decode→encode/injectivity companions** (task §10.3a) — the one
   remaining *theorem* gap (`Functional`/`Unambiguous`-parameterized chain converse).
5. **`ByteArray` wrapper + extraction + benchmark** (tasks §10.4/§10.5).
6. **Efficiency (paper §4.4 open problem)** — **last**, a separate `efficient-` change.

> **Documentation record (this session):** the README now carries a canonical,
> anchored departure/strengthening table `[D1]`–`[D8]`/`[S1]`–`[S6]` plus a layered
> layman's "Why these choices?" section; `proposal.md`/`design.md`/`spec.md`/`tasks.md`
> are reconciled to it. When adding code, keep every departure/strengthening cross-referenced
> to a `[D#]`/`[S#]` anchor, and keep the axiom record consistent (`[propext, Quot.sound]`,
> never the stale `Classical.choice`).

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
