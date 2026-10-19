# Design

## Context

See `proposal.md` — Why. The template is derived from `lean-codec`: a Nix flake
(`flake.nix` pins nixpkgs + flake-utils + treefmt-nix and passes plain nixpkgs
`lean4` into `default.nix`), a `default.nix` that runs `lake build` per target,
and a `lakefile.lean` declaring the `lean_lib` (proof gate) and `cli` exe. The
cleanup removes every codec-specific artifact so a fresh package starts from a
compiling, proof-gated shell rather than the library.

## Goals / Non-Goals

**Goals:**

- A single, verified, reusable starting point for every `lean-*` package.
- Preserve the exact build shape `lean-codec` proved out — `native`/`check`/
  `cli` targets, zero-`sorry` gate, `lean4`-only toolchain.

**Non-Goals:**

- No `codec` core (`Codec.*`, `Bytes n`, laws) ships in the template.
- No Layer-2 C seam (`@[extern]` + `buildLeanO`) in the template — that is the
  shape a package adds back only if it needs bulk byte-movement seams.
- No `openspec/` tree, `AGENTS.md`, or `PAPER.md` in the template (it is a
  starting point, not a finished library).

## Decisions

### D1 — Placeholder is `demo`/`Example` because `example` is a keyword

`package example` fails to parse ("unexpected token", and `example` is a Lean
reserved word). The template uses `package demo` / `lean_lib demo` with module
namespace `Example` (capitalized, so not a keyword), and documents the rename.
This was discovered and fixed during the build of the template this session.

### D2 — The module set mirrors the F* template: `Types`/`Majority`/`CLI`

The example is the Boyer–Moore majority-vote library, ported module-for-module
from `fstar-nix-flake-template` _minus the Pulse leaf_: `Example.Majority.Types`
(pure spec: `elem`/`count`/`majority` + `lemma_count_empty`), `Example.Majority`
(pure algorithm: `candidateStep`/`bmScan`/`findCandidate`/`verify` + the
verification-pass correspondence lemma), and `Example.Majority.CLI` (the `cli`
executable's `main : IO UInt32` over a fixed `[2, 2, 1, 2, 1, 2]` table).
`Example.Majority.Pulse` is intentionally absent — Pulse/`#lang-pulse` is an
F*-specific mutable-heap construct with no Lean counterpart; its extractable-leaf
role is played by the `cli` C-extraction seam, and the README states this.

_Alternative considered:_ keep `Example.Arith` (a trivial `add` module) —
rejected, because the user asked for the _same example modules as the F_
_template_, which is the majority-vote example, not a made-up arithmetic one.

### D3 — Three build layers, matching `fstar-nix-flake-template`

`flake.nix` (inputs/outputs + `devShell`), `default.nix` (all targets, flake-free
via `nix-build`/`import`), `lakefile.lean` (Lake roots + exes). Each has a
documented "works without flakes?" column in the README, matching the F* template.

### D4 — Dependency injection documented, not wired

The template ships _no_ `require` (its `lake-manifest.json` is gitignored and the
package is standalone). The README's "Depending on another lean-* package"
section documents the flake-input + `require from git` convention that
`port-fstar-stack-to-lean` turns into concrete wiring per package.

## Risks / Trade-offs

- **[`example` vs `demo` confusion]** → the README and this design both state the
  reason (`example` is a reserved word); `demo` is the single placeholder.
- **[A downstream package forgetting to rename]** → `lake build` on a fresh init
  still passes (it's a valid standalone package), so rename is a docs-driven step,
  not enforced by a failing build.
- **[Treefmt has no `lean` program]** → `lake fmt` handles `.lean`; `treefmt`
  handles nix/markdown. Documented in `treefmt.nix`.

## Migration Plan

1. `git init` at `../lean-nix-flake-template` (already created this session).
2. Verify the four gates (already verified): `lake build`, `lake build cli`,
   `nix build .#native .#cli`, `nix flake check`.
3. Push to `github:dysinger/lean-nix-flake-template`; downstream packages
   `nix flake init -t github:dysinger/lean-nix-flake-template`.

## Open Questions

None — the template is built and verified; only the push/publish step remains.
