## MODIFIED Requirements

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
