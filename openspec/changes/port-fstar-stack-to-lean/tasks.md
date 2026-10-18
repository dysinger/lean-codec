# Tasks

## 0. Prerequisite: the template (tracked separately)

The reusable `lean-nix-flake-template` is its own change
(`openspec/changes/lean-nix-flake-template/`, built and verified this session).
Every package below is initialized from it via `nix flake init -t`; group 1 of the
earlier draft is peeled out here and lives in that change's task list.

## 1. lean-vbin — LEB128 variable-length binary (unblocks proto)

- [ ] 1.1 `git init` `lean-vbin` from the template, `require codec from git`,
      rename to package `vbin` / module `Vbin`, and verify `lake build` on the
      empty rename passes
- [ ] 1.2 Port the removed `VarBinary` LEB128 module into `Vbin` (spec
      substrate `Bytes n`, no per-format C) and prove `varint_decode`/`varint_encode`
      byte-exact against `#eval` vectors (`0→[0]`, `128→[0x80,0x01]`, `300→[0xAC,0x02]`,
      `624485→[0xE5,0x8E,0x26]`, overlong encodings rejected)
- [ ] 1.3 Prove every `vbin` law `[propext, Quot.sound]`-only and verify
      `#print axioms` on `Vbin` reports nothing but `[propext, Quot.sound]`
- [ ] 1.4 Add the `vbin` bench lane and `CHANGELOG.md`/`README.md` (name
      `vbin` (never the longer `varbinary` spelling) and verify `nix flake check` green

## 2. lean-basen — Base2/4/8/10/16/32/64

- [ ] 2.1 `git init` `lean-basen` from the template, `require codec from git`,
      rename to `basen`/`Basen`, verify `lake build`
- [ ] 2.2 Port `Data.BaseN` (Base08/16/32/64) from `fstar-basen` to Lean and
      prove roundtrip byte-exact against RFC 4648 vectors
- [ ] 2.3 Add Base2/4/10 (not in F*): define bit-order + padding + digit math in
      the package spec, implement, and prove byte-exact against hand vectors
- [ ] 2.4 Prove all `basen` laws `[propext, Quot.sound]`-only and verify
      `#print axioms`; add bench lane + CHANGELOG/README and verify `nix flake check`

## 3. lean-text — RFC 3629 UTF-8 text parsing

- [ ] 3.1 `git init` `lean-text` from the template, `require codec from git`,
      rename to `text`/`Text`, verify `lake build`
- [ ] 3.2 Port `fstar-text` (`Data.Text.Codec.{Chars,UTF8,UTF8String,Delims,Zero}`)
      to Lean over the `Bytes n` substrate and prove roundtrip + whole-input byte-exact
      against UTF-8 known vectors
- [ ] 3.3 Prove all `text` laws `[propext, Quot.sound]`-only and verify
      `#print axioms`; add bench lane + CHANGELOG/README and verify `nix flake check`

## 4. lean-proto — protobuf wire format (sits on vbin)

- [ ] 4.1 `git init` `lean-proto` from the template, `require codec + vbin`,
      rename to `proto`/`Proto`, verify `lake build`
- [ ] 4.2 Implement protobuf tag + LEB128 varint + length-delimited field codecs
      reusing `Vbin` (never a private varint copy) and prove roundtrip on
      known protobuf byte vectors
- [ ] 4.3 Prove all `proto` laws `[propext, Quot.sound]`-only and verify
      `#print axioms`; add bench lane + CHANGELOG/README and verify `nix flake check`

## 5. lean-ip → lean-dns → lean-uri (the network trio, in xeno order)

- [ ] 5.1 `git init` `lean-ip` (`require codec + basen`), port `fstar-ip`
      IPv4/IPv6 (Base16), prove `[propext, Quot.sound]`-only, gate + bench + docs
- [ ] 5.2 `git init` `lean-dns` (`require codec + text`), port `fstar-dns`
      RFC 1034/1035 variable-length domain names, prove `[propext, Quot.sound]`-only,
      gate + bench + docs
- [ ] 5.3 `git init` `lean-uri` (`require codec + text + basen + ip + dns`), port
      `fstar-uri` RFC 3986, prove `[propext, Quot.sound]`-only, gate + bench + docs

## 6. The formatter/data siblings (image, xml, uuid, mime, stm) as in F*

- [ ] 6.1 `git init` `lean-image` (`require codec`), port `fstar-image` PNG/QR
      (CRC/Deflate/GF256/ReedSolomon), prove `[propext, Quot.sound]`-only
- [ ] 6.2 `git init` `lean-xml` (`require codec + text`), port `fstar-xml`
- [ ] 6.3 `git init` `lean-uuid` (`require codec`), port `fstar-uuid` RFC 9562
- [ ] 6.4 `git init` `lean-mime` (`require codec`), port `fstar-mime` RFC 2045
- [ ] 6.5 `git init` `lean-stm` (self-contained), port `fstar-stm` state machines

## 7. lean-http (last of the protocol stack)

- [ ] 7.1 `git init` `lean-http` (`require codec + image + stm + text + uri + dns
  - ip`), port the HTTP stack, prove `[propext, Quot.sound]`-only, gate + bench
  - docs

## 8. lean-tls (crypto FFI'd, header parsing pure-Lean)

- [ ] 8.1 `git init` `lean-tls` (`require codec + stm` + FFI crypto), keep header
      parsing pure-Lean, FFI OpenSSL/hacl for crypto, prove the pure-Lean parts
      `[propext, Quot.sound]`-only
