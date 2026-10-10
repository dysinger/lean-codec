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

**Decisions already made this session** (read before continuing):
1. `List UInt8`, not `ByteArray`, for the provable core — `ByteArray` ops are
   FFI-backed and don't reduce under `simp` (the design's own "List model" fallback).
2. `ByteArray` becomes the executable wrapper later (§7.1–7.3), not the proof model.
3. Roundtrip is **not** unconditional over `alt`; committed `|` needs a gate (currently `NoAlt`).
4. `iterate`/`foldl`/`chainl1` are deferred — coinductive at the `Iso` level.

**Open, in order:**

1. **`alt` soundness / coinductive combinators (one deferred item, blocking only
   for `alt`-and-above).** Committed `|` cannot be proven sound over the
   backtracking `Rel` without a **prefix-disjointness** condition on the
   branches (paper §4.4). That condition's compositional proof has the *same
   coinductive core* as `iterate`/`foldl`. Decided this session: **keep the
   `NoAlt` gate** (do not try to strengthen `Unambiguous`); amend spec §5.3 to
   be `NoAlt`-conditional; record prefix-disjointness as a *named future*
   condition. `iterate`/`foldl`/`chainl1` stay deferred with it.
2. **Finish §5.2 (bidirectional law).** Now stated as
   `NoAlt d → (Rel d x s ↔ decode d s = .ok (x, []))`; needs proving.
3. **`ByteArray` wrapper + extraction + benchmark** (tasks 7.1–7.3).
4. **README rewrite** (task 7.4) — stale; record `List UInt8` core, `NoAlt` gate, downstream split.
5. **Housekeeping** — `Codec/Codec.lean` type-vs-module collision (`Codec.Codec` declaring `Codec`).

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
