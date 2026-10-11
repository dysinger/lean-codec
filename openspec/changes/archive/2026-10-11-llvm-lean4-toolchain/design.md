# Design

## Context

The proof substrate is `Bytes = List UInt8` and stays that way (every `List` lemma
transfers; the entire proven core is `Bytes`-level). The `buffer-carrier-decoders`
change added the `Array UInt8` + `Nat`-index run-model with `decodeArray_eq`/
`encodeArray_eq` refinements — but in the pinned toolchain those `Array`/`ByteArray`
ops are compiled to pure `List` code because the toolchain has no LLVM.

Concrete facts established this session (all verified against the pinned `lean4`
4.34.1 and the upstream `leanprover/lean4` `v4.34.1` tag):

- `lean --features` ⇒ `[]` (no LLVM).
- `Array.push = { toList := a.toList.concat v }`, `Array.getInternal = a.toList.get`,
  `Array.size = a.toList.length`, `ByteArray.data = self.1` — i.e. `Array`/`ByteArray`
  are `List` wearing a `structure` jacket; `push` is `List.concat` (O(n)), `get` is
  `List.get` (O(i)), `size` is `List.length` (O(n)).
- `lake build bench` fails at the final `cc` link with `ld: library 'c++' not found`
  — the C++ runtime that backs the fast `@[extern]` primops isn't available.
- The nixpkgs `lean4` derivation's `buildInputs = [ gmp libuv openssl ]` and
  `cmakeFlags` contain **no `llvm`** and **no `-DLLVM=ON`**; upstream Lean's
  `src/CMakeLists.txt` gates all LLVM support behind `option(LLVM "LLVM" OFF)` and
  hard-requires **LLVM major 19** (`FATAL_ERROR "Unable to find llvm-config version 19"`).
- The pinned version **is already the current release** (`v4.34.1`); this is a
  _build-configuration_ change, not a version bump.

## Goals / Non-Goals

**Goals:**

- Turn `Array`/`ByteArray` into genuine O(1) contiguous buffers in the _extracted_ C
  by building the pinned `lean4` with `LLVM=ON` + LLVM 19, so `lake build bench` links
  and the `buffer-carrier-decoders` run-model's extracted code is O(1)-indexed.
- Keep one source of truth for the toolchain: every nix path (proof gate, `bench`,
  dev shell) uses the same LLVM-enabled `lean4`.

**Non-Goals:**

- No FFI authored by us, no compiler authored by us — this only flips the _standard_
  Lean build configuration.
- No change to `Bytes = List UInt8` or to any proven theorem; the refinement laws are
  carrier-agnostic and remain valid.
- No proof is re-proved; optionally re-measure `decodeArray`/`decodeFullArray` in
  `Bench.lean` to confirm O(1), but no new semantics.

## Decisions

1. **Override nixpkgs `lean4` rather than vendor a new derivation.** `pkgs.lean4`
   already points at `v4.34.1` (current release). Add `llvmPackages_19.llvm` to
   `buildInputs` and `lib.cmakeBool "LLVM" true` to `cmakeFlags` via `overrideAttrs`
   (or `.override`, depending on how the nixpkgs derivation is parameterized). This is
   a small, reviewable delta; full re-vendor of the ~10k-line Lean build would be
   wasteful. _Alternative considered:_ moving to the elan-released binary — rejected
   as primary because the flake is already `pkgs`-scoped and override keeps everything
   reproducible through the same `flake.lock`; kept as fallback if the override hits
   an undocumented flag interaction.

2. **LLVM major 19, exactly.** Upstream `src/CMakeLists.txt` fatals unless
   `llvm-config` reports major `19`. Use `pkgs.llvmPackages_19.llvm` (verified present
   at `19.1.7`). Any other major will fail the build. _Alternative:_ a newer LLVM —
   rejected, the check is a hard `STREQUAL "19"`.

3. **Fix the `libc++` link gap as part of the override, not separately.** The
   `ld: library 'c++' not found` is downstream of the non-LLVM build; enabling LLVM
   brings `libc++` into the link closure. If it persists, propagate `libcxx` to
   consumers. Do not treat it as an independent task.

4. **Keep `defaultTargets = ["codec"]` and the `lean_exe bench` as-is.** The proof
   gate stays `lake build` (zero sorries); `bench` remains the extraction/link
   vehicle. Only the `lean4` input changes.

## Risks / Trade-offs

- _[The override may not compose with nixpkgs' `lean4` (it uses `__structuredAttrs`
  and a `finalAttrs` self-reference)]_ → fall back to a local copy of the
  `package.nix` with the two edits, pinned via the same `fetchFromGitHub` tag; or
  switch to the elan binary.
- _[A full LLVM build is slow / heavy; first build may be minutes]_ → acceptable for a
  one-time pin; the derivation is cached in the Nix store thereafter.
- _[LLVM 19 vs. the `lean4` 4.34.1 tag's expectations could drift]_ → the tag already
  hard-codes major 19, so no drift within this pin.
- _[The speedup may still under-deliver if the `Array`→C extraction doesn't lower
  `get`/`size` to O(1) as expected]_ → verify with a micro-leg before re-plumbing; the
  override is cheap to revert (revert = drop the two-line override).

## Migration Plan

1. Implement the `lean4` override in `default.nix`/`flake.nix`.
2. `nix build '.#checks.<system>.lean'` and `nix build '.#bench'` green; `nix fmt`
   clean.
3. Run `./result/bin/bench` and record `decodeArray`/`decodeFullArray` numbers,
   confirming O(1) index access (vs. the O(n) `size` baseline measured this session).
4. Update `AGENTS.md` handoff + the `invertible-binary-core/tasks.md` ledger with the
   new numbers and the "toolchain was the blocker, not the algorithm" finding.
5. Rollback = revert the override (no codec source changes to roll back).

## Open Questions

- Whether `pkgs.lean4.override` (callPackage-style) or `overrideAttrs` is the right
  mechanism given the derivation's `__structuredAttrs`/`finalAttrs` shape — resolved
  during implementation by trying `override` first; documented in tasks.
- Whether a nixpkgs bump (to a rev where `lean4` already has an `enableLLVM` toggle)
  is simpler than a local override — assessed as a fallback, not a requirement.

## Resolved during implementation

Two findings refined the design (the original decisions were close but incomplete):

1. **`-DLLVM=ON` must be a _raw_ string flag, not `lib.cmakeBool`.** Lean's top-level
   `CMakeLists.txt` forwards cache vars to the stage0/stage1 `ExternalProject`
   sub-builds only when their cache TYPE is `UNINITIALIZED` (or via a `STAGE0_*`
   prefix). `lib.cmakeBool "LLVM" true` emits `-DLLVM:BOOL=TRUE` — a `BOOL`-typed var
   that is **not** forwarded, so every stage silently `Disabling LLVM support`. The fix
   is the raw `"-DLLVM=ON"` (untyped, `UNINITIALIZED`), which matches the `LLVM*`
   forwarding rule and reaches every stage.
2. **The _whole toolchain_ must be LLVM 19, not just the `llvm` libraries.** Adding
   `llvmPackages_19.llvm` to a clang-21 stdenv builds a `lean` binary whose LLVM reader
   is 19 but whose bitcode producer is 21; upstream `lean_llvm_parse_bitcode` aborts on
   the cross-major bitcode (`Unknown attribute kind (102) (Producer: 'LLVM21.1.8'
Reader: 'LLVM 19.1.7')`) during the stage1 stdlib build. The fix is
   `lean4.override { stdenv = llvmPackages_19.stdenv; }` (clang 19.1.7 + libc++ 19.1.7
   - llvm 19.1.7 consistently), plus `llvmPackages_19.llvm` in `nativeBuildInputs` (so
     `llvm-config` is on PATH for the configure phase) and `buildInputs` (the `-lLLVM-19`
     link libs).
