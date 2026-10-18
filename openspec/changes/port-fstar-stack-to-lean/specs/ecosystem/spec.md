# Spec Delta

## Purpose

Defines the cross-package conventions the Lean port follows: how each verified
protocol/format package is named, how it depends on lower packages, and the two
proof invariants every package inherits from the `codec` core.

## ADDED Requirements

### Requirement: Package naming drops the lean- prefix internally

Each package in the ecosystem SHALL live in its own git repository whose name is
`lean-<name>`, but the package, module namespace, and derivation name inside it
MUST drop the prefix and use `<name>` directly. The variable-length binary
package SHALL be named **`vbin`** (git repo `lean-vbin`) — never `varbinary`
or `varbin`.

#### Scenario: A package's internal name drops the prefix

- **WHEN** a downstream package (e.g. `lean-basen`) declares its Lake package or
  Nix `pname`
- **THEN** the name is `basen`, not `lean-basen`; the module namespace is `Basen`,
  not `LeanBasen`.

#### Scenario: The variable-length binary package is named vbin

- **WHEN** the LEB128/varint package is created
- **THEN** its git repo is `lean-vbin` and its internal name is `vbin`; the
  names `varbinary` and `varbin` MUST NOT be used.

### Requirement: A package only depends on packages lower in the fixed ordering

A downstream package SHALL depend only on packages strictly lower than it in the
dependency ordering, and SHALL obtain their source and pre-built library by
injection (flake inputs exposing the dependency's source dir + `.olean`
artifacts, or `require … from git` in the no-flakes dev loop) rather than by
vendoring or re-proving the dependency.

#### Scenario: Dependency injection, not vendoring

- **WHEN** `lean-uri` needs `Basen`, `Ip`, `Dns`, and `Text`
- **THEN** it declares those as flake inputs (source + `.olean` artifacts) and
  passes them into its own `default.nix`; it does not copy their sources into its
  tree or restate their lemmas.

#### Scenario: The ordering is acyclic and http comes last

- **WHEN** the full stack is laid out
- **THEN** the ordering is `codec` → `vbin`/`basen`/`text` → `proto`/`ip`/`dns`
  → `uri` → (`image`/`stm`/`xml`/`uuid`/`mime`) → `http` → `tls`, with `dns`
  ordered before `uri`, `uri` before `http`, and `http` before `tls`.

### Requirement: The single-substrate and axiom-discipline invariants are inherited

Every downstream package SHALL keep the `Bytes n` length-indexed byte string as its
single spec substrate — a Layer-2 C fast path is a runtime contract proved (or
definitionally) equal to `Bytes n`, never a second substrate, and never presented as
`decode`/`encode` themselves. Every law in every downstream package SHALL be provable
with only `propext` and `Quot.sound`, gated by `#print axioms` reporting no other
axioms.

#### Scenario: A fast path does not displace the substrate

- **WHEN** a package adds a `@[extern]`/`ByteArray`/`Array UInt8` fast path
- **THEN** it is a distinct-named transport surface proved equal to `Bytes n`; the
  package's spec and laws remain stated over `Bytes n`.

#### Scenario: Every law is propext/Quot.sound-only

- **WHEN** any downstream package's roundtrip or refinement law is checked
- **THEN** `#print axioms` reports only `[propext, Quot.sound]` (no `Classical.choice`,
  no `sorry`).

### Requirement: Text parsing and variable-length binary are separate packages

UTF-8/text codec support SHALL live in its own package (`lean-text`, internal name
`text`), and LEB128 variable-length binary support SHALL live in its own package
(`lean-vbin`, internal name `vbin`); neither SHALL be added back to the `codec`
core.

#### Scenario: text is not folded into codec

- **WHEN** RFC 3629 UTF-8 codecs are needed
- **THEN** they are provided by the `text` package, and `codec` core is unchanged.

#### Scenario: varint is not folded into codec

- **WHEN** LEB128 varint decoding/encoding is needed
- **THEN** it is provided by the `vbin` package, and `codec` core is unchanged
  (the earlier removal of `VarBinary` from core stands).
