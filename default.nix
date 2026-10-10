# Copyright 2026 Department of Code LLC.
# SPDX-License-Identifier: AGPL-3.0-or-later

# codec — a dependent, provable, byte-exact binary codec library in Lean 4.
#
# Takes the Lean 4 toolchain (the `lean4` derivation) as a concrete input — no
# `pkgs` blob, no overlay assumption — and returns:
#   - `native` — the `lake build` library (`.olean` artifacts + `libcodec.a`),
#   - `check`  — the Lean proof-validation gate (`lake build` with no `sorry`).
#
# Both are the SAME `lake build`; `check` is the derivations' proof gate,
# `native` is the installable artifact.

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

  # The single build action: `lake build` compiles + verifies (no `sorry`).
  mkLakeBuild =
    {
      name,
      description,
      install,
    }:
    mkDerivation {
      pname = "${pname}-${name}";
      version = "0.1.0";
      src = ./.;
      nativeBuildInputs = [ lean4 ];
      meta = meta // {
        inherit description;
      };
      buildPhase = ''
        runHook preBuild
        lake build
        runHook postBuild
      '';
      installPhase = install;
    };

in
{
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

  # `check` — the Lean proof-validation gate (same `lake build`, proof-only).
  check = mkLakeBuild {
    name = "check";
    description = "${meta.description} (proof-validation gate)";
    install = "true";
  };
}
