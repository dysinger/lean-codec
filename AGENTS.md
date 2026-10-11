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
- `Codec/Codec.lean` (+`Rel`), `Codec/Decode.lean`, `Codec/Encode.lean`,
  `Codec/Sound.lean` — the backtracking-union list decoder and the
  **unconditional** laws (`decode_spec`, `bidir`, `encode_rel`, `decode_encode`,
  `roundtrip`).
- `Codec/Combinators.lean` — §6.1/§6.2 derived combinators, **all done**: `many`
  (still `partial def`), `*>`,`<*`, `between`, `chainl1` (on `foldl`), `chainr1`
  (on `foldr`, step `Iso ((α × β) × α) α`), `some`/`many1`, `sepBy`/`sepBy1`,
  `optional`/`maybe`, `choice` (right-assoc), `count n p`/`manyUpTo n p`
  (bounded, total, `#eval`-able), plus soundness lemmas `Rel_some`,
  `Rel_optional_some`, `Rel_choice` (`[propext]` only).

**Decisions already made** (read before continuing):
1. `List UInt8`, not `ByteArray`, for the provable core.
2. **`|` is the paper's backtracking union, not committed choice** (restored;
   `NonNull`/`Disjoint`/`PrefixDisjoint` deleted). Do not reintroduce a
   deterministic/committed decoder.
3. `foldl`/`chainl1` and `foldr`/`chainr1` are done and proved.
4. `Codec` is an inductive description AST, not the paper's §3.4 typeclass.
5. `iterate` (paper §5.3) is deliberately omitted (no field law; forward/backward
   fixpoints can differ).

**Open, in order:**

1. **Total, correct repetition decoder** — **DONE** (change
   `openspec/changes/total-backtracking-decoder/`, Option 1). `decode`'s
   repetition is now **well-founded recursion on `s.length`** (`decodeRepeat`,
   `Codec/Decode.lean`), with no fuel, no `Productive`/`AllProductive` predicate,
   no `Codec.many` constructor. The denotation is the total least fixpoint
   `relRepeat (Rel p)` (`Codec/Codec.lean`), and the laws are:
   `productive_iff_consumesByte` (totality iff productive), `decodeRepeat_spec`
   (the `many`-case bidirectional law), `relRepeat_unbounded_of_empty` +
   `not_productive_pure` (the empty-matching contrapositive). `Rel` is unchanged;
   laws stay unconditional; `[propext, Quot.sound]`, zero `sorry`/warnings.
   `#eval byteRepeat [1,2,3]` = `[([],[1,2,3]),([1],[2,3]),([1,2],[3]),([1,2,3],[])]`.

   **Next step (planned in the existing ledger, §9 of
   `openspec/changes/invertible-binary-core/tasks.md`):** `many` is still a
   `partial def Codec` (the *infinite* AST), so `Rel (many p)` is *opaque* — the
   `Rel_many` equality `Rel (many p) xs s ↔ relRepeat (Rel p) xs s` is
   **unprovable** with the current `partial def`. The honest reading of the
   design's "`many` is a total `def` in denotational reading" is: `relRepeat`
   *is* `many`'s denotation, and the list combinators (`some`/`sepBy`/`sepBy1`/
   `chainl1`/`chainr1`, which embed `many p` as a `Codec` value) must be
   re-derived over `relRepeat`/`decodeRepeat` directly. **Do this as §9 of the
   `invertible-binary-core` change — no new change.**
2. **Efficiency (the paper's §4.4 open problem)** — memoization/DP over the same
   denotation, separate from correctness. (This also subsumes the future
   "lazy-stream carrier" migration if a *total* `decode (many (pure ()))` is ever
   required — see the design's "single genuine fork".)
3. **`ByteArray` wrapper + extraction + benchmark** (tasks 7.1–7.3).
4. **README rewrite** (task 7.4) — update the combinator table + downstream split.
5. **Housekeeping** — `Codec/Codec.lean` type-vs-module collision.

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
