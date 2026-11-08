# Copyright 2026 Department of Code LLC.
# SPDX-License-Identifier: AGPL-3.0-or-later

{
  description = "codec — a dependent, provable, byte-exact binary codec library in Lean 4";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    treefmt-nix.url = "github:numtide/treefmt-nix";
  };

  outputs =
    {
      self,
      nixpkgs,
      flake-utils,
      treefmt-nix,
      ...
    }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = import nixpkgs { inherit system; };

        # Lean package: the `default.nix` native derivation + proof check.
        _pkg = import ./default.nix {
          inherit (pkgs) lean4;
          inherit (pkgs) lib;
          inherit (pkgs) stdenv;
        };

        treefmtModule = treefmt-nix.lib.evalModule pkgs ./treefmt.nix;

        # OpenSpec validation as a flake check: run `openspec validate --all`
        # over the repository's `openspec/` root.
        openspec-check =
          pkgs.runCommand "openspec-validate"
            {
              nativeBuildInputs = [
                pkgs.openspec
                pkgs.git
              ];
            }
            ''
              runHook preBuild
              cd ${self}
              openspec validate --all --no-interactive
              touch "$out"
              runHook postBuild
            '';
        # The benchmark lane, **built and run**, with its value-check lines required.
        #
        # `codec-audit-round-nine` §1.9. Until this existed, `Bench.lean` was outside
        # every gate: `flake.nix` had `checks.{lean,openspec,formatting}` and nothing
        # for the bench, so the `example`s and the runtime value checks in it **could
        # not fail CI** — a green `nix flake check` said nothing about the bench. Two
        # halves are needed, and only one of them is a build:
        #
        # * the `example`s are value-checked at COMPILE time (they are `rfl`), so
        #   `lake build bench` already covers them — and since §1.8 the exe root
        #   carries `-DwarningAsError`, so a `sorry` there is an error too;
        # * the *runtime* checks (the seam boundary/aliasing checks, the C-reference
        #   cross-check, the `benchBurst` non-invariance assertions) run only when the
        #   binary runs. Those are the ones this check makes reachable.
        #
        # The check **fails if the binary exits non-zero** (a `throw` in any value
        # check or any invariance assertion) and if any of the print lines whose
        # absence would mean a check silently stopped running is missing. It is a
        # `checks` entry and not merely `packages.bench` because a value check that
        # cannot fail the gate is not a check — the distinction `../lean-basen` draws
        # in the other direction (its bench is a package *because* its checks are
        # build-time `example`s and it has no runtime checks).
        #
        # It is slow (it runs the whole bench lane, ~15 s here and much longer in the
        # sandbox), which is why the dev loop is still `lake build bench` + running
        # the binary by hand.
        bench-check =
          pkgs.runCommand "codec-bench-check"
            {
              nativeBuildInputs = [ pkgs.git ];
            }
            ''
              runHook preBuild
              cd ${self}
              lake build bench
              ./.lake/build/bin/bench > bench.out 2>&1 || {
                echo "bench exited non-zero — a value check or an invariance assertion failed:"
                cat bench.out
                exit 1
              }
              cat bench.out
              # Every line here is a check whose *silence* would be indistinguishable
              # from a check that was deleted, and that is the defect class this round
              # is about. Pinning them makes the deletion a build failure.
              grep -q 'seam boundaries OK' bench.out
              grep -q 'seam aliasing OK' bench.out
              grep -q 'count step \[n=1\]: round trip OK' bench.out
              grep -q 'count step \[n=3\]: round trip OK' bench.out
              grep -q 'decodeFullFast root \[4096\]: value + bridge OK' bench.out
              grep -q 'decodeFullArray root \[4096\]: value + bridge OK' bench.out
              grep -q 'decodeWhole \[4096\]: value + decodeWhole_eq OK' bench.out
              grep -q 'decodeWholeBytes \[4096\]: agrees with decodeWhole' bench.out
              grep -q 'C reference value check: 6 of 6 inputs agree' bench.out
              grep -q '^done$' bench.out
              # A `benchBurst` row that printed nothing is a row that did not run.
              test "$(grep -c 'steps/burst' bench.out)" -ge 16
              touch "$out"
              runHook postBuild
            '';
      in
      {
        # The default target builds the native library (`lake build` → `.olean`).
        packages.default = _pkg.native;
        packages.native = _pkg.native;
        # The benchmark executable (a plain `lean_exe` that also links the
        # Layer-2 C seam object — not a C-extraction step).
        packages.bench = _pkg.bench;

        # Lean proof validation: the same `lake build`, no `sorry` (the gate).
        checks.lean = _pkg.check;
        # OpenSpec planning validation.
        checks.openspec = openspec-check;
        # The benchmark lane, built **and run**, with its value-check lines pinned
        # (§1.9) — see the `bench-check` definition for why it is a check and not a
        # package.
        checks.bench = bench-check;
        # Formatting check (treefmt).
        checks.formatting = treefmtModule.config.build.check self;

        formatter = treefmtModule.config.build.wrapper;

        devShells.default = pkgs.mkShellNoCC {
          name = "codec";
          packages = [
            _pkg.lean4 # lean, lake, leanc, and the Lean 4 LSP (lean --server)
            pkgs.stdenv.cc # the Nix clang wrapper (provides cc/clang/c++ with libc++)
            pkgs.elan # toolchain manager (matches ../workflow)
            pkgs.openspec # spec-driven development CLI
            pkgs.git
          ];
          shellHook = ''
            echo "codec dev shell — lean $(lean --version | head -1 | awk '{print $2}')"
            echo "openspec $(openspec --version)"
            # Activate the repo's pre-commit hook (runs `nix fmt` and fails if
            # staged files would be reformatted). Stored under .githooks/.
            git config core.hooksPath "$PWD/.githooks"
          '';
        };
      }
    );
}
