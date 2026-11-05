# template Specification (delta)

## MODIFIED Requirements

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
