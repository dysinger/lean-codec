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
        # **The build inputs are `lean4` and a C compiler, and the first version of this
        # check declared neither** (`codec-audit-round-nine` review P1-NB4). It ran
        # `lake build bench` with `nativeBuildInputs = [ pkgs.git ]`, so the sandbox
        # failed with `lake: command not found` (exit 127) — the check was **red from the
        # day it was written** and was never built, only `nix eval`'d for its drvPath.
        # That is the round's own defect class in its purest form: a check nobody ran,
        # described in three comments and two documents as one that cannot be skipped.
        # ```
        # $ nix build .#checks.aarch64-darwin.bench
        # codec-bench-check> line 3: lake: command not found
        # error: builder failed with exit code 127
        # ```
        # `lean4` supplies `lake`/`lean`; `stdenv.cc` is what Lean's C backend needs to
        # compile the exe and what links `byteSliceO`/`cRefO`.
        bench-check =
          pkgs.runCommand "codec-bench-check"
            {
              nativeBuildInputs = [
                _pkg.lean4
                pkgs.stdenv.cc
                pkgs.git
              ];
            }
            ''
              # **`set -euo pipefail` is load-bearing, and its absence was the third
              # defect found in this check** (`codec-audit-round-nine` review P1-NB4 and its
              # follow-ups). Two of the three defects in this derivation were invisible
              # for the same reason — nobody built it — and this one would have stayed
              # invisible after fixing the other two: `runCommand`'s builder does not run
              # its body under `set -e`, so a failing `grep -q`, which is the *entire
              # point* of the check, printed nothing and the build still exited 0.
              #
              # Mutation-tested after the fix: replacing the `^done$` assertion with a
              # grep for a line that never appears makes the build fail
              # (`exit=1, builder failed with exit code 1`); before it, the same mutation
              # exited 0 on a freshly built, freshly timed run. Every assertion below is
              # now a failure rather than a log line.
              set -euo pipefail
              runHook preBuild
              # **Build in a writable copy.** `${self}` is a read-only store path, so
              # `lake build` cannot create `.lake/` there — the second defect the review
              # found in this check (`permission denied ... /nix/store/…-source/.lake`).
              # Copying is also what makes the check hermetic: it compiles the tree the
              # flake pins rather than whatever is in the working directory.
              cp -r ${self} work
              chmod -R u+w work
              cd work
              # A `.lake` carried over from the copy is read-only and stale; start clean
              # rather than inherit a build directory this sandbox did not produce.
              rm -rf .lake
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
        # **The mirror check** (`codec-audit-round-nine` review P3-M4).
        #
        # `gen-axioms.lean` cannot import `Axioms.lean` (bootstrap cycle), so its copies
        # of the classifier's name lists can drift — and `AGENTS.md` records that drift
        # un-pinning `Codec.Suffix.hle` for a whole round. `lake build` **cannot** catch
        # an *undercounting* drift: the generator writes its smaller set into the
        # generated `gatedNames` region, so `partition`/`gateCoverage` then read that list
        # and agree with it by construction. `headerNumbers`' `expectedGated` is only a
        # speed bump, because the same regenerating session bumps it.
        #
        # The check that works is this one: **run the generator and diff.** A drifted
        # mirror produces a different `Axioms.lean`, and a diff needs no parsing of Lean
        # literals — which is the fragility that made a first attempt at this check report
        # vacuous agreement (two lists that both failed to parse compared equal).
        mirror-check =
          pkgs.runCommand "codec-mirror-check"
            {
              nativeBuildInputs = [
                _pkg.lean4
                pkgs.stdenv.cc
                pkgs.git
              ];
            }
            ''
              set -euo pipefail
              runHook preBuild
              cp -r ${self} work
              chmod -R u+w work
              cd work
              rm -rf .lake
              lake build Codec > /dev/null
              cp Axioms.lean Axioms.before
              lake env lean scripts/gen-axioms.lean
              if ! diff -q Axioms.before Axioms.lean > /dev/null; then
                echo "gen-axioms.lean's mirrors disagree with the committed Axioms.lean:"
                diff -u Axioms.before Axioms.lean | head -80
                echo ""
                echo "A mirror has drifted. Fix the mirror in scripts/gen-axioms.lean, NOT the"
                echo "committed file: an undercounting mirror rewrites Axioms.lean with its"
                echo "smaller set and the gate then agrees with it by construction. That is the"
                echo "Codec.Suffix.hle regression."
                exit 1
              fi
              echo "mirror check: the generator is idempotent against the committed Axioms.lean"
              touch "$out"
              runHook postBuild
            '';
        reviews-check =
          pkgs.runCommand "codec-review-ids"
            {
              nativeBuildInputs = [ pkgs.python3 ];
            }
            ''
              set -euo pipefail
              runHook preBuild
              cd ${self}
              python3 - <<'PY'
              import re, sys, glob
              files = ["README.md", "Axioms.lean", "flake.nix", "Bench.lean",
                       "scripts/gen-axioms.lean"] + sorted(glob.glob("Codec/*.lean"))
              cited = set()
              for f in files:
                  cited |= set(re.findall(r"review (P[0-9]-[A-Z]+[0-9]+[a-z]?)", open(f).read()))
              # The archived path: round nine landed 2026-11-13. This line is the
              # SECOND thing that broke when the change moved (the first was this
              # check itself going red), and it is worth stating: `checks.reviews`
              # resolves every `review P<pass>-<axis><n>` citation from the source to
              # one file, so moving that file silently breaks the reconciliation in
              # the direction it exists to catch. A future archive that moves a
              # cited review file must update this path in the same commit.
              doc = "openspec/changes/archive/2026-11-13-codec-audit-round-nine/reviews/round-ten.md"
              tabled = set(re.findall(r"^\| `(P[0-9]-[A-Z]+[0-9]+[a-z]?)`", open(doc).read(), re.M))
              bad = []
              for c in sorted(cited - tabled):
                  bad.append(f"{c}: cited in the source but has no row in {doc}")
              for t in sorted(tabled - cited):
                  bad.append(f"{t}: listed in {doc} but cited nowhere in the source")
              if bad:
                  print("reviewer ids do not reconcile:")
                  for b in bad: print("  " + b)
                  sys.exit(1)
              print(f"reviewer ids reconcile: {len(cited)} cited, {len(tabled)} tabled, zero orphans")
              PY
              touch "$out"
              runHook postBuild
            '';
        # **The gate-lines check** (`codec-drift-closure` §2.2, design D2 mechanism (b)).
        #
        # The README quotes the `axiom gate:` lines `lake build` prints. That quotation
        # is a *figure* — a quotation of an assertable output — so per the spec it must
        # be generated by the run it quotes. This check regenerates it and diffs, the
        # same mechanism `checks.mirror` uses, chosen over a marked region because it
        # needs no new convention inside a markdown file (D2's stated preference).
        #
        # **Measured at `codec-drift-closure`'s start: 3 of the 14 committed lines were
        # stale at HEAD** (`constant kinds`, `stated footprints`, `recursion-principle
        # promotion`) while the prose above them said "pasted verbatim from a green
        # build". That is the defect this check closes, and it is not hypothetical.
        #
        # The check builds in a writable copy for the reasons `bench-check` documents:
        # `${self}` is a read-only store path, so `lake build` cannot create `.lake/`
        # there.
        gate-lines-check =
          pkgs.runCommand "codec-gate-lines-check"
            {
              nativeBuildInputs = [
                _pkg.lean4
                pkgs.stdenv.cc
                pkgs.git
                pkgs.python3
              ];
            }
            ''
              set -euo pipefail
              runHook preBuild
              cp -r ${self} work
              chmod -R u+w work
              cd work
              rm -rf .lake
              lake build Codec > /dev/null
              # The generator asserts its own denominator (14 gate lines) and fails if
              # the gate did not run, so a zero-line block cannot match vacuously.
              bash scripts/gen-readme-gate.sh --write
              if ! diff -q ${self}/README.md README.md > /dev/null; then
                echo "README's quoted gate block disagrees with a fresh build:"
                diff -u ${self}/README.md README.md | head -60
                echo ""
                echo "Regenerate it: nix develop --command scripts/gen-readme-gate.sh --write"
                echo "The BUILD is canonical. Do not edit the block by hand -- a hand-written"
                echo "quotation of an asserted output is what went 3-of-14 stale."
                exit 1
              fi
              echo "gate-lines check: README's quoted gate block matches a fresh build"
              touch "$out"
              runHook postBuild
            '';
        # **The documentation-count check** (`codec-drift-closure` §2.3,
        # `docs-conformance`: "A count in documentation is derivable by a command").
        #
        # `README.md` states two counts a porter is told to reproduce: [S1]'s "19
        # `Iso`-valued definitions" (`13 + 4 + 2`) and [S3]'s "7 constructors + 8
        # bounded values = 15", with four further counterexample witnesses. Both were
        # hand-derived paragraphs with no command behind them — the shape the spec
        # calls "a completeness claim that fails silently: it is not wrong-looking, it
        # is merely short".
        #
        # `scripts/count-values.lean` walks the environment, prints both lists, and
        # **asserts** the totals against `expectedIsoValues` / `expectedCodecValues`.
        # The predicate is in that file, including its removals (the compiler
        # auxiliaries `_f`, `_sunfold`, `_unsafe_rec`, `_flat_ctor`, counted so the
        # removal is visible).
        values-check =
          pkgs.runCommand "codec-values-check"
            {
              nativeBuildInputs = [
                _pkg.lean4
                pkgs.stdenv.cc
                pkgs.git
              ];
            }
            ''
              set -euo pipefail
              runHook preBuild
              cp -r ${self} work
              chmod -R u+w work
              cd work
              rm -rf .lake
              lake build Codec > /dev/null
              # `lean` exits non-zero on the `throwError` in the script, so the
              # assertion is a build failure, not a log line.
              lake env lean scripts/count-values.lean
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
        checks.mirror = mirror-check;
        checks.reviews = reviews-check;
        # The README's quoted gate block, regenerated and diffed (§2.2).
        checks.gate-lines = gate-lines-check;
        # The README's two stated value counts ([S1]'s 19, [S3]'s 12), re-derived by
        # an environment walk (§2.3). A count in documentation with no command behind
        # it is the defect class this change closes.
        checks.values = values-check;

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
