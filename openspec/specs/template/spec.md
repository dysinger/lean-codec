# template Specification

## Purpose

Defines the contract the reusable Lean package skeleton satisfies: a minimal,
verified Lean 4 library with a Nix flake exposing a `native`/`check`/`cli`
target split, a zero-`sorry` build gate, and the `demo`/`Example` placeholder
naming convention every downstream package inherits.

## Requirements

### Requirement: The skeleton builds and verifies with zero sorry

The template SHALL provide a `lean_lib` that `lake build` verifies with zero
`sorry`, plus a `cli` executable that successfully builds and runs. The Nix
flake SHALL expose `native`, `check` (the zero-`sorry` proof gate), and `cli`
targets such that `nix build .#native .#cli` and `nix flake check` all succeed.

#### Scenario: The proof gate passes on a fresh copy

- **WHEN** a downstream package initializes from the template and runs
  `lake build` and `nix build .#native .#cli`
- **THEN** every build succeeds with no `sorry`/warning, and `nix flake check`
  (the `lean` + `formatting` checks) reports green.

#### Scenario: The cli executable runs

- **WHEN** a consumer runs `nix run .#cli` (or the built `cli` binary)
- **THEN** it prints the Boyer–Moore majority-vote result
  (`findCandidate [2, 2, 1, 2, 1, 2] = some 2`) and exits `0`, proving the
  C-extraction + link pipeline end to end.

### Requirement: The example is the Boyer–Moore majority-vote module set

The template SHALL ship the Boyer–Moore majority-vote example from the
`fstar-nix-flake-template`, ported to Lean as three modules: `Example.Majority.Types`
(pure spec), `Example.Majority` (pure two-pass algorithm), and `Example.Majority.CLI`
(the `cli` executable's `main`). The F* `Example.Majority.Pulse` leaf SHALL be
omitted, because Pulse is an F*-specific mutable-heap construct with no Lean
counterpart; the README SHALL state this omission and identify the `cli`
C-extraction seam as its role's replacement.

#### Scenario: The module set mirrors the F* template minus Pulse

- **WHEN** a consumer reads the template's `Example/` sources
- **THEN** they find `Example/Majority/Types.lean`, `Example/Majority.lean`, and
  `Example/Majority/CLI.lean` (matching the F* `Types`/`Majority`/`CLI` modules),
  and no `Example.Majority.Pulse` (documented as omitted).

#### Scenario: The cli target is the CLI module

- **WHEN** the `cli` executable is built
- **THEN** its root is `Example.Majority.CLI` with a `main : IO UInt32` that runs
  `findCandidate` over a fixed vote table and returns exit status `0`/`1`.

### Requirement: The placeholder name is demo, not example

The template SHALL use **`demo`** as the Lean `package`/`lean_lib` identifier and
**`Example`** as the module namespace, because `example` is a reserved word in
Lean and cannot be a `package` name. The README "Renaming" section SHALL document
renaming `demo`/`Example` to the target package (e.g. `vbin`/`Vbin`).

#### Scenario: The reserved word is not used as the package name

- **WHEN** the template's `lakefile.lean` and `default.nix` declare the package
  and derivation names
- **THEN** they use `demo` (and `pname = "demo"`), never `example` as a Lean
  `package`/`lean_lib` identifier.

#### Scenario: Renaming is documented

- **WHEN** a consumer reads the README "Renaming" section
- **THEN** it lists the exact renames (module files, `module`/`namespace`
  headers, `lakefile.lean` package name + roots, `default.nix`/`flake.nix`
  `pname`/`description`) needed to reach a real package such as `vbin`.

### Requirement: The template documents the dependency-injection convention

The template SHALL document how a downstream package depends on another
`lean-*` package: by pulling the dependency's source + pre-built `.olean`
artifacts as flake inputs (handed to `default.nix` by named argument) for the
flake build, and via Lake `require … from git` for the no-flakes dev loop.

#### Scenario: A consumer can wire a codec dependency

- **WHEN** a consumer follows the template's "Depending on another lean-*
  package" guidance
- **THEN** they add a flake input exposing the dependency's source + `native`
  package (e.g. `codec-src` / `codec-lib`), and a `require codec from git` line,
  without vendoring or re-proving the dependency.
