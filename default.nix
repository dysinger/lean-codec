# Copyright 2026 Department of Code LLC.
# SPDX-License-Identifier: AGPL-3.0-or-later

# codec — a dependent, provable, byte-exact binary codec library in Lean 4.
#
# Takes the Lean 4 toolchain (the `lean4` derivation) as a concrete input — no
# `pkgs` blob, no overlay assumption — and returns:
#   - `native` — the `lake build` library (`.olean` artifacts + `libcodec.a`),
#   - `check`  — the Lean proof-validation gate (`lake build` with no `sorry`),
#   - `bench`  — the §10.5 extraction + benchmark executable (`lake build bench`).
#
# `native`/`check` are the SAME `lake build`; `check` is the proof gate,
# `native` is the installable library, `bench` is the extraction vehicle.

{
  lean4,
  llvmPackages_19,
  lib,
  stdenv,
}:

let
  inherit (stdenv) mkDerivation;

  # The LLVM-enabled `lean4` override: builds the pinned `lean4` with LLVM 19
  # enabled so the `Array`/`ByteArray` primops (`get`/`push`/`size`/`get!`)
  # lower to the `@[extern]` O(1) C++ implementations rather than pure-`List`
  # fallbacks. See `openspec/changes/llvm-lean4-toolchain/`.
  #
  # Two things are required, and both are necessary:
  #
  #  1. `stdenv = llvmPackages_19.stdenv` — the *whole toolchain* must be LLVM 19
  #     (clang 19.1.7 + libc++ 19.1.7 + llvm 19.1.7). Upstream's `lean_llvm_parse_bitcode`
  #     refuses to read bitcode produced by a *different* LLVM major (`Unknown attribute
  #     kind (102) (Producer: 'LLVM21.1.8' Reader: 'LLVM 19.1.7')`); mixing the host
  #     stdenv's clang 21 with `llvmPackages_19.llvm` libs reproduces exactly that.
  #     The consistent `llvmPackages_19.stdenv` also puts llvm 19's `llvm-config` on PATH
  #     and `libc++` in the closure.
  #
  #  2. `-DLLVM=ON` as a *raw* string (no `:BOOL=` type annotation): Lean's top-level
  #     `CMakeLists.txt` only forwards cache vars to the stage0/stage1/stage2 sub-builds
  #     when their type is `UNINITIALIZED` (or via a `STAGE0_*` prefix). `lib.cmakeBool`
  #     emits `-DLLVM:BOOL=TRUE`, a `BOOL`-typed cache var that is *not* forwarded, so every
  #     stage silently disables LLVM.
  lean4-llvm =
    (lean4.override {
      inherit (llvmPackages_19) stdenv;
    }).overrideAttrs
      (old: {
        # `llvm` in `nativeBuildInputs` puts `llvm-config` (dev output) on PATH for
        # the CMake configure phase (with the derivation's `strictDeps = true`,
        # `buildInputs` bins are not on PATH). It also provides the LLVM static
        # libs (`-lLLVM-19`) for the link.
        nativeBuildInputs = (old.nativeBuildInputs or [ ]) ++ [
          llvmPackages_19.llvm
        ];
        buildInputs = (old.buildInputs or [ ]) ++ [
          llvmPackages_19.llvm
        ];
        cmakeFlags = (old.cmakeFlags or [ ]) ++ [ "-DLLVM=ON" ];
      });

  pname = "codec";

  meta = {
    description = "A dependent, provable, byte-exact binary codec library in Lean 4";
    license = lib.licenses.agpl3Plus;
    maintainers = [
      {
        name = "Tim Dysinger";
        email = "tim@dysinger.net";
      }
    ];
    platforms = lib.platforms.all;
  };

  # One build action: `lake build <targets>` (empty targets = the library +
  # proof-verify, no `sorry`). `targets` selects the explicit build target(s).
  mkLakeBuild =
    {
      name,
      description,
      install,
      targets ? "",
      mainProgram ? null,
    }:
    mkDerivation {
      pname = "${pname}-${name}";
      version = "0.1.0";
      src = ./.;
      nativeBuildInputs = [ lean4-llvm ];
      meta =
        meta
        // {
          inherit description;
        }
        // lib.optionalAttrs (mainProgram != null) {
          inherit mainProgram;
        };
      buildPhase = ''
        runHook preBuild
        lake build ${targets}
        runHook postBuild
      '';
      installPhase = install;
    };

in
{
  # The LLVM-enabled toolchain shared by every path (dev shell, proof gate,
  # bench): one source of truth for the `lean4` build configuration.
  lean4 = lean4-llvm;

  # `native` — the installable library artifact.
  native = mkLakeBuild {
    name = "native";
    description = "${meta.description} (native library)";
    install = ''
      runHook preInstall
      mkdir -p "$out/lib/lean" "$out/lib"
      cp -r .lake/build/lib/* "$out/lib/lean/" 2>/dev/null || true
      # The library archive (if any) is the loadable `lib${pname}.a`.
      if [ -e ".lake/build/lib/${pname}.a" ]; then
        cp ".lake/build/lib/${pname}.a" "$out/lib/lib${pname}.a"
      fi
      runHook postInstall
    '';
  };

  # `check` — the Lean proof-validation gate (the same `lake build`, zero `sorry`).
  check = mkLakeBuild {
    name = "check";
    description = "${meta.description} (proof-validation gate)";
    install = ''
      runHook preInstall
      # The check is the build itself (zero `sorry`); produce an (empty) `$out`
      # so the derivation satisfies Nix's output requirement.
      mkdir -p "$out"
      runHook postInstall
    '';
  };

  # `bench` — the §10.5 extraction + benchmark executable. Builds the `bench`
  # lean_exe (extracting the `decode`/`encode`/`decodeRepeat`/`encodeRepeat`
  # hot path to C, then linking against the Lean runtime) and installs it.
  bench = mkLakeBuild {
    name = "bench";
    description = "${meta.description} (extraction + benchmark executable)";
    targets = "bench";
    mainProgram = "bench";
    install = ''
      runHook preInstall
      mkdir -p "$out/bin"
      if [ -e ".lake/build/bin/bench" ]; then
        cp ".lake/build/bin/bench" "$out/bin/bench"
      fi
      runHook postInstall
    '';
  };
}
