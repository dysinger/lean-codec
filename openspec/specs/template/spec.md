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

The zero-`sorry` gate SHALL be **enforced**, not observed: the library SHALL
compile with the compiler's `sorry` warning promoted to an error, so an
unproved declaration fails the build instead of emitting a warning a reader has
to notice. The template's documentation SHALL describe the gate as enforced only
where that promotion exists, because a project scaffolded from a template with an
observational gate inherits a claim its build does not check.

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

#### Scenario: A stubbed theorem fails the fresh build

- **WHEN** a theorem in a package scaffolded from the template is replaced by
  `sorry`
- **THEN** `lake build` (and therefore `nix build .#native` / `nix flake check`)
  fails non-zero naming the declaration, so the inherited gate cannot go green
  with an incomplete proof.

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

Every branch, tag, or revision the documentation names SHALL be one the named
dependency actually has. A dependency's default branch SHALL be recorded from
that repository rather than assumed from a sibling project's convention, because a
consumer copying the example gets a fetch failure that reads as a broken
dependency rather than a stale instruction.

The template's own operating instructions SHALL describe **this** repository. Where
the conventions are shared with a scaffolded project that has more machinery — a
bench lane, an axiom gate, a dependency input — the instruction SHALL either be
limited to what the template actually ships, or name the project it was taken from,
so that a fork does not look for a file, a package or a flag the template does not
contain. An instruction that describes another repository's derivation is the same
defect the documentation rules exist to prevent, committed by the document that
states the rules.

A claim about what the build sees SHALL be scoped to the build path it holds for.
Where the template offers two paths — a flake build and a bare `nix-build` /
`import` of `default.nix` — a statement that only git-tracked files are visible SHALL
be attributed to the path where that is true, because the other path takes the whole
directory and the unqualified sentence is false for it.

A proof-gate flag SHALL be attached to **every** compilation of a module the gate is
claimed to cover, so that the claim does not depend on one target happening to import
another. Where a module is both a library root and an executable root, both SHALL
carry the flag, so that dropping either edge leaves the gate intact.

#### Scenario: A consumer can wire a codec dependency

- **WHEN** a consumer follows the template's "Depending on another lean-*
  package" guidance
- **THEN** they add a flake input exposing the dependency's source + `native`
  package (e.g. `codec-src` / `codec-lib`), and a `require codec from git` line,
  without vendoring or re-proving the dependency.

#### Scenario: The named branch exists

- **WHEN** a consumer copies the documented `require … from git "@ <branch>"`
  line verbatim
- **THEN** the branch resolves in the named dependency, so the example works as
  written rather than failing as a broken import.

#### Scenario: The instructions describe this repository

- **WHEN** the template's operating instructions describe a derivation target,
  package, or flag
- **THEN** that target exists in the template's own `flake.nix` / `default.nix`, or
  the instruction names the project it was taken from, so a fork does not search for
  machinery the template does not ship.

#### Scenario: A build-path claim is scoped to its path

- **WHEN** the documentation states which files a build can see
- **THEN** the statement is scoped to the build path it holds for — the flake's
  git-tree snapshot, or the bare `nix-build` that copies the directory — so it is
  not false for the path the same document advertises.

#### Scenario: The proof-gate flag covers both roots

- **WHEN** a module is compiled as both a library root and an executable root
- **THEN** both targets carry the `warningAsError` flag, so the gate does not depend
  on one target importing the other.
