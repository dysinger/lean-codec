# Proposal

## Why

Every package in the Lean ecosystem (`vbin`, `basen`, `text`, `proto`, `ip`,
`dns`, `uri`, … `http`/`tls`) needs the same starting point: a minimal, proven
Lean 4 library skeleton with a Nix flake, a Lake build split into a `lean_lib`
proof gate and a `cli` executable (the Boyer–Moore majority-vote example ported
from `fstar-nix-flake-template`), and a documented dependency-injection
convention. Rather than hand-rolling each from `lean-codec` (whose `Codec/`
core, `Paper.md`, and openspec history are a liability for a fresh package),
we factor the common skeleton into its own reusable repository.

## What Changes

- Introduce **`lean-nix-flake-template`**, a cleaned-down copy of `lean-codec`
  with all codec-specific content removed (`Codec/`, `PAPER.md`, layer-2 C
  seams, openspec history, `AGENTS.md`), exposing a `native`/`check`/`cli`
  target split and a `lean4`-scoped dev shell.
- Establish the placeholder convention: Lean package id `demo` (since `example`
  is a reserved word in Lean) with module namespace `Example`, documented in the
  README "Renaming" section.
- Document the **three build layers** (`flake.nix` / `default.nix` /
  `lakefile.lean`) and the **dependency-injection** sketch a downstream package
  fills in (`require … from git` + flake inputs exposing a dependency's source +
  `.olean` artifacts).

## Capabilities

### New Capabilities

- `template`: the contract the reusable Lean package skeleton satisfies — the
  target split (`native`/`check`/`cli`), the zero-`sorry` build gate, the
  Boyer–Moore majority-vote example module set (`Types`/`Majority`/`CLI`, with
  the F* `Pulse` leaf omitted as F*-specific), the `demo`/`Example` placeholder
  naming (since `example` is a Lean keyword), and the dependency-injection
  convention it documents.

### Modified Capabilities

<!-- None. The template is a new, standalone deliverable; it does not alter
     `codec` or the new `ecosystem` capability. -->

## Impact

- **New repo**: `lean-nix-flake-template` (sibling to `lean-codec`, initialized
  at the `../lean-nix-flake-template` path during this session and already
  verified).
- **No change to `lean-codec`** source; the template is a _distinct_ repo, not a
  branch or refactor of the library.
- **Downstream consumers**: every `lean-vbin`/`lean-basen`/… package in the
  `port-fstar-stack-to-lean` plan is initialized from this template via
  `nix flake init -t`.
