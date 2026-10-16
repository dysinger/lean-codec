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

## Map of the repo

- **Reference paper:** `PAPER.md`.
- **Architecture statement (complete `[D#]`/`[S#]` departures/strengthenings, each
  with a layman "why"):** `README.md`.
- **Engineering state & task ledger (spec-driven):** `openspec/`. Every change
  lives under `openspec/changes/` as proposal / spec delta / design / tasks. The
  **active change is `single-carrier-bytes`** — consult
  `openspec/changes/single-carrier-bytes/tasks.md` for the current task status and
  next steps. History ("we used to / reverted / this session") belongs in that
  ledger, **never** in this file or the README.
- **Library source (module `Codec`):** `Codec/`.
  - `Iso.lean` — partial isomorphisms + folded combinators (`foldl`/`foldr`).
  - `Codec.lean` — the description AST, the length-indexed substrate `Bytes n`,
    `Rel`/`relRepeat`, and the substrate/cast-commutation lemma library.
  - `Decode.lean` / `Encode.lean` — the backtracking decoder and partial encoder.
  - `Sound.lean` — the bidirectional + roundtrip laws (unconditional).
  - `Combinators.lean`, `VarBinary.lean` — derived combinators and LEB128 varint.
- **Executable/bench:** `Bench.lean`, wired through `lakefile.lean` and Nix
  `default.nix`/`flake.nix`.

## Active work (single carrier)

The core (`Codec`/`Decode`/`Encode`/`Sound`) is **re-derived over the single
length-indexed substrate `Bytes n := Fin n → UInt8`**, `[propext, Quot.sound]`-only
(no `Classical.choice`, zero `sorry`). `Codec/Combinators.lean`, `Codec/VarBinary.lean`
and the old transfer-tier modules (`DecodeArray`/`EncodeArray`/`DecodeByteArray`/
`EncodeByteArray`/`DecodeByteArraySlice`/`EncodeByteArraySlice`/`ExternFastPath`/
`Buffer`) are still on the old `List UInt8` substrate and do not build against the
new core — the tree is **intentionally in an atomic-change intermediate state** until
the transfer tier is deleted. The ordered remaining work is tracked in
`openspec/changes/single-carrier-bytes/tasks.md` (task 3.3 onward).

Axiom discipline: every law must stay `[propext, Quot.sound]`-only. `#print axioms
Codec.roundtrip` is the check.

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
