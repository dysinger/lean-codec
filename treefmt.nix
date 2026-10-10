# Copyright 2026 Department of Code LLC.
# SPDX-License-Identifier: AGPL-3.0-or-later

# treefmt formatting config (evaluated by treefmt-nix `evalModule`).
#
# Formats nix (`*.nix`) and markdown (`*.md` and prose).  Lints nix for dead
# code (deadnix) and style (statix).
#
# Lean sources (`*.lean`) are NOT formatted here: treefmt-nix has no `lean`
# program, and Lean's own formatter is `lake fmt` (which reformats `.lean` files
# according to the Lean 4 style).  Run `lake fmt` for Lean; `treefmt` handles
# everything else.  Matches the sibling `fstar-codec` convention of excluding
# the source language from treefmt when no reliable treefmt program exists.

_: {
  projectRootFile = "flake.nix";

  programs.nixfmt.enable = true;
  programs.deadnix.enable = true; # scan .nix files for dead code
  programs.statix.enable = true; # lint .nix files

  programs.mdformat.enable = true; # format markdown

  settings.excludes = [
    ".git/**"
    ".lake/**"
    "build/**"
    "*.olean"
    "*.ilean"
    "docs/*.pdf"
    "flake.lock"
  ];

  settings.includeExcludes = true;
}
