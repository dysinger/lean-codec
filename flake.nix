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
          inherit (pkgs) lean4 llvmPackages_19;
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
      in
      {
        # The default target builds the native library (`lake build` → `.olean`).
        packages.default = _pkg.native;
        packages.native = _pkg.native;
        # The §10.5 extraction + benchmark executable.
        packages.bench = _pkg.bench;

        # Lean proof validation: the same `lake build`, no `sorry` (the gate).
        checks.lean = _pkg.check;
        # OpenSpec planning validation.
        checks.openspec = openspec-check;
        # Formatting check (treefmt).
        checks.formatting = treefmtModule.config.build.check self;

        formatter = treefmtModule.config.build.wrapper;

        devShells.default = pkgs.mkShellNoCC {
          name = "codec";
          packages = [
            _pkg.lean4 # lean, lake, leanc, and the Lean 4 LSP (lean --server)
            pkgs.llvmPackages_19.clang # cc/clang with libc++, so `leanc`'s `-lc++` links
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
