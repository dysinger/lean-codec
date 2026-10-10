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

**Done** (compiles clean: 9 targets, zero sorries, zero warnings; `#print axioms
Codec.roundtrip` ⇒ `[propext, Quot.sound]`):
- `Codec/Iso.lean`, `Codec/Codec.lean` (+`Rel`), `Codec/Decode.lean`,
  `Codec/Encode.lean`, `Codec/Sound.lean` (`roundtrip`/`decode_encode` for the
  `alt`-free `NoAlt` fragment), `Codec/Combinators.lean` (`many`, `*>`, `<*`, `between`).
- **`Iso.foldl`** (paper §5.3) — a *proved* partial isomorphism, built by
  well-founded recursion on a `measure : α → Nat` witness (`Iso.MeasureDecreases`);
  both directions proven (`foldUnapply_sound`, `foldUnapply_of_foldApply`), law as a
  field, unconditionally. Depends only on `[propext, Quot.sound]` — **no
  `Classical.choice`** (constructive well-founded recursion).
- **`Codec.chainl1`** (paper §6.1) — built on `Iso.foldl`; its soundness rides on
  `foldl`'s proved law, no separate proof, no `sorry`.
- **§5.2 bidirectional law** — `decode_spec`/`bidir` (`Rel d x s ↔ decode d s =
  .ok (x, [])` over `NoAlt`).

**Decisions already made this session** (read before continuing):
1. `List UInt8`, not `ByteArray`, for the provable core — `ByteArray` ops are
   FFI-backed and don't reduce under `simp` (the design's own "List model" fallback).
2. `ByteArray` becomes the executable wrapper later (§7.1–7.3), not the proof model.
3. Roundtrip is **not** unconditional over `alt`; committed `|` needs a gate (currently `NoAlt`).
4. `foldl`/`chainl1` are **done and proved** (see above).
5. `Codec` is an **inductive description AST**, *not* the paper's §3.4 typeclass
   — needed so `Rel`/`decode`/`encode` are ordinary functions over one
   description value (see `Codec/Codec.lean` docstring).
6. **`iterate` (paper §5.3) is deliberately omitted.** Its forward-iteration
   fixpoint `b` (`apply b = none`) and backward-iteration fixpoint `a`
   (`unapply a = none`) need **not coincide**: `apply a = some b ↔ unapply b = some a`
   does not force `apply a = none ↔ unapply a = none`. So it has no *field* law without
   a per-element "chain-isolated in both directions" precondition — exactly the
   "modulo equivalence classes" weakening this library rejects. `foldl` (proved
   directly, no `iterate`) is what `chainl1` needs; `iterate` is omitted rather than
   shipped unsound. See the comment at the bottom of `Codec/Iso.lean`.

**Open, in order:**

1. **`alt` prefix-disjointness (blocking — this is now concrete combinator work, not
   an abstract design question).** See README departure #5 and `tasks.md` §8. The path:
   (a) define a structural `NonNull : Codec α → Prop`; (b) prove the prefix-disjointness
   lemma (`NonNull d₁` ⇒ no `Rel d₁`-string is a proper prefix of a `Rel d₂`-string);
   (c) extend `decode_spec`/`roundtrip`/`bidir` past `NoAlt`; (d) implement
   `some`/`many1`, `sepBy`/`sepBy1`, `optional`/`maybe`/`choice`, `chainr1`, and
   multi-operator `chainl1` — each proven under `NonNull`. These are the combinators
   every real format needs; they are currently missing or outside `NoAlt`.
   **Decision already made: stay cursor-free — no backtracking, no peeking.**
   Prefix-disjointness is a denotational `Prop` provable by well-founded induction
   (same style as `foldl`), strictly better than an operational cursor. Ambiguous
   formats (e.g. `if | if_then_else`) must be left-factored — the standard LL(1)
   restriction, surfaced as a witness. Do not reopen this.
2. **`ByteArray` wrapper + extraction + benchmark** (tasks 7.1–7.3).
3. **README rewrite** (task 7.4) — largely done; check the combinator table +
   downstream split are current, and record `foldl`/`chainl1` done + `iterate` omitted.
4. **Housekeeping** — `Codec/Codec.lean` type-vs-module collision (`Codec.Codec` declaring `Codec`).

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
