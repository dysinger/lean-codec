# Copyright 2026 Department of Code LLC.
# SPDX-License-Identifier: AGPL-3.0-or-later

# codec — a dependent, provable, byte-exact binary codec library in Lean 4.
#
# Takes the Lean 4 toolchain (the `lean4` derivation) as a concrete input — no
# `pkgs` blob, no overlay assumption — and returns:
#   - `native` — the `lake build` library (`.olean` artifacts + `libcodec.a`),
#   - `check`  — the Lean proof-validation gate (`lake build`, fails on `sorry`),
#   - `bench`  — the §10.5 extraction + benchmark executable (`lake build bench`).
#
# `native`/`check` are the SAME `lake build`; `check` is the proof gate,
# `native` is the installable library, `bench` is the extraction vehicle.
#
# Plain nixpkgs `lean4`. The bulk fast path uses the Lean runtime's own
# `@[extern]` C primops (`ByteArray.push`/`copySlice`), compiled by the plain
# `cc`.

{
  lean4,
  lib,
  stdenv,
}:

let
  inherit (stdenv) mkDerivation;

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
      nativeBuildInputs = [ lean4 ];
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
  # The `lean4` toolchain shared by every path (dev shell, proof gate, bench):
  # one source of truth for the `lean4` build configuration.
  inherit lean4;

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

  # `check` — the Lean proof-validation gate (`lake build`, which FAILS on
  # `sorry`: `lakefile.lean` sets `-DwarningAsError=true` on the library, so the
  # compiler's `declaration uses 'sorry'` warning is an error).
  check = mkLakeBuild {
    name = "check";
    description = "${meta.description} (proof-validation gate)";
    install = ''
      runHook preInstall
      # The check is the build itself: `lake build` with `-DwarningAsError=true`
      # (from `lakefile.lean`), so a `sorry` fails here rather than warning.
      # Produce an (empty) `$out` so the derivation satisfies Nix's output
      # requirement.
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
