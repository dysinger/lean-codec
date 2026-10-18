# Proposal

## Why

The F* stack is already built out as a layered set of verified packages
(`codec` → `basen`/`text`/`ip`/`dns`/`uri`/… → `http`/`tls`), and the Lean core
(`codec`) is done — a verified, byte-exact, bidirectional description framework
over the length-indexed `Bytes n` substrate with `[propext, Quot.sound]`-only
laws. We now want to recreate that stack in Lean, one package at a time, so the
fruits of the verified-codec core compound into real protocols (protobuf, URI,
HTTP, TLS) rather than stopping at a combinator library.

## What Changes

- Establish the **layering convention** the Lean ecosystem will follow: each
  verified protocol/format is its own package in its own git repo, names drop the
  `lean-` prefix internally (git repo `lean-vbin`, package/module name `vbin`;
  `lean-basen` → `basen`; `lean-text` → `text`; `lean-proto` → `proto`; …).
- Fix the **variable-length binary** (LEB128 varint) primitives as their own
  package **`vbin`** (the short name, not `varbinary`), pulling the `VarBinary` work that was
  deliberately removed from `codec` core into a downstream package.
- Split **text parsing** (RFC 3629 UTF-8 codecs) into its own package **`text`**
  (not folded into `codec`).
- Fix the **dependency ordering** the Lean stack follows: `codec` →
  `vbin`/`basen`/`text` → `proto`/`ip`/`dns` → `uri` → (`image`/`stm`/`xml`/
  `uuid`/`mime`) → `http` → `tls`, mirroring the F*/xeno ordering (`dns` before
  `uri`, `http` last, crypto/TLS FFI'd not re-proved).
- Establish the **dependency-injection convention**: a package consumes its
  dependencies' _source_ + _pre-built library_ as flake inputs (source dir +
  `.olean` artifacts), and via `require … from git` for the no-flakes dev loop —
  never vendoring or re-proving a dependency.
- Re-affirm the two invariants every downstream package inherits from `codec`:
  (a) the `Bytes n` spec substrate stays the single substrate (Layer-2 C seams are
  runtime contracts, never a second substrate, never folded into a law); (b) every
  law is `[propext, Quot.sound]`-only, gated by `#print axioms`.

## Capabilities

### New Capabilities

- `ecosystem`: the cross-package conventions the Lean port follows — package
  naming (`vbin`, prefix-dropping), the single-substrate + axiom-discipline
  invariants, the dependency-ordering rule, and the dependency-injection
  convention. This is the spec-level contract every downstream `lean-*` package
  must satisfy; per-package protocol detail lives in design.md/tasks.md, not in a
  spec requirement.

### Modified Capabilities

<!-- None: the `codec` capability and its byte-string/partial-remainder
     sub-capabilities are not changing. This change introduces new packages,
     it does not alter the proven `codec` core's requirements. -->

## Impact

- **New git repos** (one per package), each initialized from
  `lean-nix-flake-template`: `lean-vbin`, `lean-basen`, `lean-text`,
  `lean-proto`, `lean-ip`, `lean-dns`, `lean-uri`, and — following the F* set —
  `lean-image`, `lean-stm`, `lean-xml`, `lean-uuid`, `lean-mime`, then
  `lean-http`, `lean-tls`.
- **`codec` core is untouched**: no change to `Codec.*`, `Bytes n`, the laws, or
  the `[propext, Quot.sound]` gate. The `VarBinary` removal stands (that work
  moves to `vbin`).
- **Dependencies**: each package depends only on packages _lower_ in the fixed
  ordering, via the flake-input injection convention.
- **No per-format C, no re-proving crypto**: the "all codecs pure-Lean, C only
  for generic bulk byte-movement seams, TLS crypto FFI'd" decision stands.
