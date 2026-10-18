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
- State the encoders/decoders over the `codec` `Bytes n` substrate, with the
  roundtrip law (decode(encode(x)) = x) proved for each base, `[propext,
Quot.sound]`-only.

## Capabilities

### New Capabilities

- `basen`: the base-`N` encoding/decoding contract — one package, seven bases
  (2/4/8/10/16/32/64), each with a byte-list encoder + decoder, a roundtrip law,
  UTF-8/ASCII alphabets per RFC 4648, and the `codec`-inherited invariants
  (single `Bytes n` substrate, `[propext, Quot.sound]`-only laws).

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
