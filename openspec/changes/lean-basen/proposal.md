# Proposal

## Why

The `codec` core is proven and the reusable `lean-nix-flake-template` is done,
but the ecosystem has no _format_ packages yet — nothing turns bytes into
base-`N` text or back. Base-`N` is the first leaf off `codec` in the ordering
and is a prerequisite for `ip` (IPv6 hex) and for a wide class of wire formats,
so it is the natural second package to port. It also has a proven F* reference
(`fstar-basen`) to port from, which de-risks the proofs.

## What Changes

- Introduce **`lean-basen`** (git repo `lean-basen`, package/module namespace
  `BaseN`), the first downstream package in the ecosystem, depending only on
  `codec`.
- Port the four F* base encodings (Base08/Base16/Base32/Base64, all RFC 4648)
  and **add Base2, Base4, and Base10** (not in `fstar-basen`), for a single
  package covering **Base2/4/8/10/16/32/64**.
- Express all seven bases as `codec` `Codec` values over `satisfy`/`count`/`iso`
  plus the productive repetition layer (no bespoke `encode`/`decode`), with the
  inherited roundtrip law proved for each base, `[propext, Quot.sound]`-only.

> **Surface note:** an earlier phase of this change introduced bespoke
> `encode : List UInt8 → List UInt8` / `decode : List UInt8 → Option (List UInt8)`
> functions; that surface was **superseded** by `basen-uniform-leaf-api`
> (archived), which re-expressed every base as a `Codec` value. The final
> surface is the `Codec`-value run triple; this proposal records that final state.

## Capabilities

### New Capabilities

- `basen`: the base-`N` encoding/decoding contract — one package, seven bases
  (2/4/8/10/16/32/64), each a `codec` `Codec` value over `satisfy`/`count`/`iso`
  plus the repetition run triple, with an inherited roundtrip law, RFC 4648
  alphabets, and the `codec`-inherited invariants (single `Bytes n` substrate,
  `[propext, Quot.sound]`-only laws).

### Modified Capabilities

<!-- None: `codec` and `ecosystem` are unchanged. `basen` is a new leaf. -->

## Impact

- **New repo** `lean-basen` (sibling to `lean-codec`), initialized from
  `lean-nix-flake-template` with `require codec from git`.
- **Dependencies**: `basen` → `codec` only (no `vbin`, no `text`).
- **Downstream**: `lean-ip` (IPv6 hex via Base16) and future format packages can
  consume `basen` by flake-input injection; nothing in `codec` changes.
- **New proofs**: Base2/4/10 are new semantics (bit/octal/decimal digit math),
  defined in this package's spec before implementation.
