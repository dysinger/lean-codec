# Proposal

## Why

`buffer-carrier-decoders` (done) produced the correct F\*-style two-tier structure: a
native, indexed `Array UInt8`-carrier run-model proved equal to the `List` spec
(`decodeArray_eq`/`encodeArray_eq`, all `[propext, Quot.sound]`-only). But it delivers
**no speedup** — and on the `byte`/`size` hot path it is _slower_ — because the pinned
`lean4` derivation is built **without LLVM**, so `Array`/`ByteArray` are not the
contiguous O(1) buffers that extraction should turn them into. In this build they fall
back to pure-`List` definitions (`Array.push = List.concat`, `Array.get = List.get`,
`Array.size = List.length`), and `lake build bench` even fails to link (`ld: library
'c++' not found`). The F\* original described in `PAPER.md` used a **buffer + cursor**
and reached Nginx-adjacent TLS-server throughput; that is exactly the stock-Lean
`ByteArray` + `Nat`-index model, and it is reachable _without_ authoring FFI or a
compiler — the blocker is the toolchain, not the algorithm.

## What Changes

- Introduce a **LLVM-enabled `lean4` override** in the Nix flake, built with
  `LLVM=ON` and `llvm` (LLVM 19, the exact major the Lean 4.34.1 cmake requires) in its
  build inputs, so `lean --features` reports LLVM and `Array`/`ByteArray` primops
  (`get`/`push`/`size`/`get!`) are the fast `@[extern]` O(1) C++ implementations.
- Wire that override into `default.nix`'s `lean4` input and the `flake.nix`
  `devShells.default`/`packages` so **every** nix path (proof gate, `bench`, dev shell)
  uses the same LLVM-backed toolchain; keep the pinned `4.34.1` release tag (it is
  already the current upstream release — this is a _build-configuration_ change, not a
  version bump).
- Keep the **proof substrate** unchanged (`Bytes = List UInt8` stays the only spec
  carrier). No codec behavior changes; no new capabilities.

## Capabilities

### New Capabilities

_(None — this is a toolchain/build-infrastructure change; the codec's observable
behavior is unchanged. `skip_specs: true`.)_

### Modified Capabilities

_(None.)_

## Impact

- `default.nix` gains the LLVM-enabled `lean4` (an `override`/`overrideAttrs` on
  `pkgs.lean4` that adds `llvmPackages_19.llvm` to `buildInputs` and `-DLLVM=ON` to
  `cmakeFlags`), replacing the plain `lean4` passed to `native`/`check`/`bench`.
- `flake.nix`'s `devShells.default.packages` and the `_pkg` import switch to the
  overridden toolchain, so `lake build bench` links against `libc++` and the extracted
  C uses flat buffers.
- `flake.lock` may need a nixpkgs bump if a newer `nixpkgs#lean4` (already 4.34.1 with
  LLVM-support plumbing) is cleaner than a local override; assess during implementation.
- `Bench.lean` and the `buffer-carrier-decoders` run-model (`decodeArray`/`encodeArray`/
  `decodeFullArray`) are _unchanged in denotation_; only their extracted behavior
  becomes O(1)-indexed. The already-proved `decodeArray_eq`/`encodeArray_eq` refinement
  laws remain valid and carrier-agnostic.
- Non-goals (unchanged): no FFI authored here, no compiler authored here, no codec
  semantics change, no `Classical`, no new proof axioms.
