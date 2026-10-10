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

**Done** (compiles clean: 8 modules, zero sorries, zero warnings; `#print axioms
Codec.roundtrip` ⇒ `[propext, Quot.sound]`):
- `Codec/Iso.lean`, `Codec/Codec.lean` (+`Rel`), `Codec/Decode.lean`,
  `Codec/Encode.lean`, `Codec/Sound.lean`, `Codec/Combinators.lean` (`many`,
  `*>`, `<*`, `between`).
- **The decoder is now the paper's nondeterministic (backtracking) list decoder.**
  `decode : Codec α → List UInt8 → List (α × List UInt8)`, with `|` as list
  concatenation (`decode (d₁ | d₂) s = decode d₁ s ++ decode d₂ s`). This
  **reverses** the earlier committed-`|` departure (#2/#3): see the next
  section for the full decision.
- **`Iso.foldl`** (paper §5.3) — a *proved* partial isomorphism, well-founded
  recursion on a `measure : α → Nat` witness; both directions proven; law as a
  field. `[propext, Quot.sound]` only — **no `Classical.choice`**.
- **`Codec.chainl1`** (paper §6.1) — built on `Iso.foldl`; soundness rides on
  `foldl`'s proved law.
- **The laws are now *unconditional*** (no `NoAlt`, no `Disjoint`, no
  prefix-disjointness): `decode_spec` (`(x,r) ∈ decode d s ↔ ∃ s₀, s = s₀++r ∧
  Rel d x s₀`), `bidir` (`Rel d x s ↔ (x,[]) ∈ decode d s`), `encode_rel`,
  `decode_encode`, `roundtrip`. All in `Codec/Sound.lean`.

**Decisions already made** (read before continuing):
1. `List UInt8`, not `ByteArray`, for the provable core — `ByteArray` ops are
   FFI-backed and don't reduce under `simp`; `ByteArray` becomes the executable
   wrapper later (§7).
2. **`|` is the paper's backtracking union, not committed choice.** We tried a
   deterministic single-result decoder + committed `|` for speed; it is
   *fundamentally incompatible* with the paper's `|` and `many` (the empty
   branch always wins — `decode (nil $ pure ()) s` always succeeds; and `nil`
   vs `cons` are never prefix-disjoint because `[]` is a proper prefix of every
   non-empty string — proved as `ProperPrefix [] s ↔ s ≠ []`). The fix was to
   **restore the paper's semantics** (full backtracking union, `Rel (d₁|d₂) =
   Rel d₁ ∨ Rel d₂` matches `decode` by construction). The laws became
   unconditional; the whole `NonNull`/`PrefixDisjoint`/`Disjoint`/
   `Unambiguous` machinery was **deleted** (`Codec/NonNull.lean` removed). Do
   **not** reintroduce a deterministic/committed decoder. Efficiency is future
   work (§7), not a reason to change semantics.
3. `foldl`/`chainl1` are done and proved.
4. `Codec` is an **inductive description AST**, not the paper's §3.4 typeclass
   — so `Rel`/`decode`/`encode` are ordinary functions over one description
   value (see `Codec/Codec.lean` docstring).
5. **`iterate` (paper §5.3) is deliberately omitted** — its forward/backward
   fixpoints need not coincide, so no field law without a per-element
   "chain-isolated in both directions" precondition. `foldl` (proved directly)
   is what `chainl1` needs. See the bottom of `Codec/Iso.lean`.

**Open, in order:**

1. **§6.2 derived repetition/sum combinators — now unblocked.** Implement
   `some`/`many1`, `sepBy`/`sepBy1`, `optional`/`maybe`/`choice`, `chainr1`
   (the dual of `chainl1`, needs an `Iso.foldr` right-fold dual of `foldl`).
   These are ordinary definitions over the backtracking `|`; their soundness
   falls out of the unconditional laws — no gate. **Caveat:** `many` is a
   `partial` description (an infinite AST), so it is *provable* but not
   `#eval`-able in its current recursive form; making repetition evaluable is
   part of this work.
2. **Efficiency (the paper's §4.4 open problem).** The backtracking decoder is
   exponential/space-leaky in the naive form; re-implement the *same* semantics
   efficiently (memoization/dynamic programming over the relation), keeping the
   unconditional laws. This is a future spike, separate from correctness.
3. **`ByteArray` wrapper + extraction + benchmark** (tasks 7.1–7.3).
4. **README rewrite** (task 7.4) — largely done after the reversal; check the
   combinator table + downstream split are current.
5. **Housekeeping** — `Codec/Codec.lean` type-vs-module collision
   (`Codec.Codec` declaring `Codec`).

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
