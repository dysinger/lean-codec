# Tasks

## 1. Duplicate and clean lean-codec into the template

- [x] 1.1 Copy `lean-codec` to `../lean-nix-flake-template` and strip all
      codec-specific content (`Codec/`, `Codec.lean`, `Bench.lean`, `PAPER.md`,
      `AGENTS.md`, `.pi/`, `openspec/`, `.git`, `.lake`, `result*`); verify the
      remaining tree is the flake skeleton only
- [x] 1.2 Rebuild the source as the Boyer–Moore module set (matching the F*
      template minus Pulse): `Example/Majority/Types.lean` + `Example/Majority.lean`
  - `Example/Majority/CLI.lean` (+ the `Example.lean` root), and rewrite
    `lakefile.lean` (`package demo` / `lean_lib demo` / `lean_exe cli` rooted at
    `Example.Majority.CLI`), `default.nix`, `flake.nix`, `README.md`,
    `CHANGELOG.md`, `treefmt.nix`, `.gitignore`
- [x] 1.3 Confirm the placeholder is `demo`/`Example` (not `example`, a Lean
      keyword) and that the README "Renaming" section documents renaming to
      `vbin`/`Vbin` and generalizing the `lean-` prefix drop
- [x] 1.4 Add the `templates.default` output to `flake.nix` so
      `nix flake init -t` works (the reviewer's Critical), and omit
      `Example.Majority.Pulse` with the README stating why (Pulse is F*-specific)

## 2. Verify the template's four gates

- [x] 2.1 Verify `nix develop -c 'lake build'` succeeds with zero `sorry`/warning
- [x] 2.2 Verify `lake build cli` succeeds and the `cli` binary prints
      `findCandidate [2, 2, 1, 2, 1, 2] = some 2` and exits `0`
- [x] 2.3 Verify `nix build .#native .#cli` succeeds
- [x] 2.4 Verify `nix flake check` is green (the `lean` proof check + the
      formatting check)

## 3. Publish

- [x] 3.1 `git init` + commit the clean tree at `../lean-nix-flake-template` and
      push to `github:dysinger/lean-nix-flake-template`
- [x] 3.2 Verify a downstream init works end to end: `nix flake init -t
github:dysinger/lean-nix-flake-template` in a scratch dir → `nix build` green
