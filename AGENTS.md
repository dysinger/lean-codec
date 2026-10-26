# AGENTS.md

Guidance for AI coding agents working in this repository.

**This file is forward-looking operating instructions, not a session diary.**
History — what landed when, what was reverted, what a past session measured —
belongs in `openspec/` (the task ledger) and `CHANGELOG.md`. Do not append
"session status" sections here; that practice is what made this file 536 lines
of mutually-contradicting snapshots. Keep it short and true.

## Project

`codec` — a verified, byte-exact, bidirectional codec library in Lean 4
(repo directory `lean-codec`). Takes Rendel & Ostermann's _Invertible Syntax
Descriptions_ (2010) and makes it dependently typed, provable, and binary.

Stdlib-only (no mathlib). Build with `lake build`; the proof gate is the same
build with zero `sorry`.

- **Reference paper:** `PAPER.md`.
- **Architecture statement** (complete `[D1]`–`[D8]` departures / `[S1]`–`[S6]`
  strengthenings, each with a layman "why"): `README.md`. Stable anchors — cite
  them, don't restate them here.

## Toolchain / environment: read first

**This is a Nix flake project. Every tool is in the flake `devShells.default`, not
on the host PATH.** Before doing anything, enter the dev shell:

```bash
nix develop
```

That shell provides the pinned `lean`/`lake` (Lean 4.34.1), `elan`, and the
**`openspec` CLI** — none of which are guaranteed to be on the host. Then run the
same commands (e.g. `openspec list --json`, `openspec status --change … --json`,
`lake build`, `nix build '.#bench'`).

Do **not**:

- search the host filesystem to locate tools (e.g. `find / -name openspec …`) —
  they live in the Nix store, reached via `nix develop`;
- assume `openspec`/`lake`/`lean` are already on PATH — check with `nix develop`
  first;
- fall back to hand-editing `openspec/` artifacts when `openspec` is unavailable
  on the host — get it from `nix develop`.

**Long builds (HARD RULE):** never run a long `nix build` (toolchain, bench, or
proof gate) in the foreground of a tool call, and never set a huge tool timeout
(`600000`/`900000` seconds = days-to-weeks — absurd and forbidden):

- launch them detached with `nohup … > /tmp/<name>.log 2>&1 &` and **poll** the
  log with short `bash` calls (seconds, not minutes);
- keep the `bash` tool `timeout` small (≤ ~120s) for polling; keep blocking work
  tiny. If a command will exceed that, it must go detached;
- never `sleep` for minutes inside a single foreground call to "wait out" a build.

The dev shell is `pkgs.mkShellNoCC` **plus `pkgs.stdenv.cc`**, so `cc`/`clang`/
`c++` resolve to a `libc++`-aware toolchain and `lake build bench` links, matching
the `nix build .#bench` sandbox. (For general Nix usage see the `nix` skill; use
`devenv`/`devenv-migration` only when actually migrating to devenv, never for
this flake.)

## Where the truth lives

**One source of truth per concern.** When two files disagree, the left column wins:

| Question                                        | Authoritative file                      |
| ----------------------------------------------- | --------------------------------------- |
| What is this library, why each design choice    | `README.md` (`[D#]`/`[S#]`), `PAPER.md` |
| What work is open, and how done is done         | `openspec/changes/<name>/tasks.md`      |
| What a change is _allowed_ to change            | `openspec/changes/<name>/proposal.md`   |
| The behavioural contract                        | `openspec/specs/**/spec.md`             |
| How this environment is set up and how to build | this file                               |

**Anything else is a summary.** If a summary and an `openspec/` artifact differ,
the artifact is correct and the summary is stale — fix the summary.

## Current state

Run `openspec list --json` for the live answer; do not trust a snapshot here for
longer than the commit that wrote it. As of this writing:

- **`lean-codec` (this repo) core is complete.** `Codec/Iso.lean`, `Codec.lean`,
  `Decode.lean`, `Encode.lean`, `Sound.lean`, `Combinators.lean`, plus the proved
  packed layer (`Codec/Packed.lean`, `Codec/DecodeOne.lean`) and the Layer-2 trust
  seam (`Codec/ByteSlice.lean` + `.c`). Every law is `[propext, Quot.sound]`-only,
  zero `sorry`. `@[default_target] lean_lib codec` is the proof gate;
  `lean_exe bench` is the benchmark.
- **No open change in this repo.** The RFC-conformance work streams from
  `../lean-basen`, not from here.
- **The active downstream is `../lean-basen`** (sibling repo — package `basen`,
  module `BaseN`; base-2/4/8/10/16/32/64). All seven bases are landed and proven
  as `Codec` values; the facade dispatches `BaseN.roundtrip` over `B2..B64`;
  `Bench.lean` value-checks them byte-for-byte. **Work there, in its own
  `nix develop`, not this repo's.**

### `../lean-basen` — the two open changes

`openspec/changes/basen-rfc-conformance-theorems/` is **30/31**. Only **7.3** remains.

- **7.1 (DONE)** — `decodeFull_B{2,4,8,10,16}_char` join `decodeFullB{64,32}_char`, so all
  seven bases state the in-image converse. Pure assembly over each base's already-proved
  `decode_encode_inverse` (→) and `roundtrip` (←).
- **7.2 (DONE)** — the task posed a false dichotomy ("prove a type-level `B64`/`B32`" vs
  "keep the withdrawal"). `B64`/`B32` already _are_ that type (terminal tails, no
  continuation) and the bijection was already proved; what was missing was any theorem
  _connecting_ the type to the decoder. Now proved: `decodeFullB{64,32}_char_via_type`
  (decoder image = image of `encodeB ∘ b*BytesOf`), `decodeFullB{64,32}_spine`, and
  `b{64,32}BytesOf_tail1_eq` (terminality is `rfl`, **no axioms**). The withdrawal is
  **reversed** in all three spec sites, kept textually identical for archive safety.
- **7.3 (TODO — the only open task, in this change).** Base16 case-insensitive decoding
  (RFC 4648 §8 "MUST accept both cases"). This is a **design decision before a proof**:
  `design.md` D6 currently keeps `hexElem` strict uppercase, and case-folding breaks
  `Unambiguous`, so a documented relaxation must land first. Do not start proving until
  the relaxation is decided.
- **`lean-basen` shows 18/25** but is complete except **seven mechanical polish items**
  (5.2, 5.3, 5.4, 5.8, 5.9, 5.12, 5.13), listed in
  `openspec/changes/lean-basen/tasks.md` under "Still open — mechanical polish".
  Read them there; they are doc/tidy items, not proofs.

**Archive ordering.** Both changes MODIFY the requirement "The `basen` bases are
`Codec` values", and archiving keeps only one version. The two MODIFIED/synced
texts were deliberately made identical (task 6.11), so either order is now _safe_ —
but archive **`lean-basen` first**, then `basen-rfc-conformance-theorems`, running
`openspec validate --all` after **each**.

Severity-tagged evidence behind every §6 task:
`../lean-basen/REVIEW-basen-rfc-conformance.md`.

## Downstream ecosystem

Each verified format/protocol is its own git repo, initialized from
`lean-nix-flake-template`, prefix-dropped internally (`lean-basen` → `basen`/
`BaseN`; `lean-vbin` → `vbin`; …), depending on `codec` **by flake input + `require
codec from git` injection — never vendored**, and inheriting the single-`Bytes n`-
substrate and `[propext, Quot.sound]`-only discipline.

In `../lean-basen`, `codec` is a flake input threaded into `default.nix`, which
rewrites `require codec from git …` → a local `require codec from "./codec-src"`
path dependency, so the sandboxed `lake build` needs no network. (`lean-codec` is
public, so the `github:` input fetches anonymously — no token, no `--impure`.)

## Verification recipe

The proof gate is the build. In `../lean-basen`, from **its own** `nix develop`:

```bash
nix develop --command lake build         # library + Axioms.lean: zero sorry/warnings
nix develop --command lake build bench   # the bench lane
```

`Axioms.lean` is a `@[default_target]` lib, so `lake build` runs the `#guard_msgs`
gates; a `Classical.choice` regression fails the build. To check one law by hand:

```bash
printf 'import BaseN\n#print axioms BaseN.Base64.decodeFullB64_reject_arity\n' > /tmp/c.lean
nix develop --command lake env lean /tmp/c.lean    # expect [propext, Quot.sound]
```

After any spec-delta edit, `openspec validate --all` from `../lean-codec`.
`nix flake check` is a **long** build — detached with `nohup … &`, then poll;

- **Axiom discipline.** Every law stays `[propext, Quot.sound]`-only, zero
  `Classical.choice`, zero `sorry`. `#print axioms Codec.roundtrip` is the check;
  `../lean-basen`'s `Axioms.lean` is a `@[default_target]` lib so `lake build`
  enforces its `#guard_msgs` gates.
- **The `Bytes n` spec substrate is single.** `Bytes n := Fin n → UInt8` is both
  the proof substrate and its own scalar-read run-model. The packed (`Array UInt8`)
  and byte-slice (`ByteArray`) carriers are proved-equal or trust-seam
  _implementations on top of it_ — the laws never leave `Bytes n`.
- **Two proof layers are never conflated.** Layer 1 (packed carrier + refinement
  theorems) is proven and is the only layer in the axiom gate. Layer 2
  (`byteSlice`/`blitBytes`/`findByte`/`commitRemainder`, `@[extern]` into
  `Codec/ByteSlice.c`) is a **named runtime trust contract, excluded from the gate**.
  `#print axioms <seam>` reporting "no axioms" is **by construction** and says
  **nothing about the C** — `@[extern]` swaps only emitted C; the kernel sees the
  Lean body. "No axiom" is never "no trust."
- **All codecs are pure Lean.** C is only generic bulk byte movement
  (`memcpy`/`memchr` shapes). **No per-format C, no C that parses digits, numbers,
  fields, or format structure.** That is a hard design rule.
- **Pure-Lean parsing has a ~20–40×-off-C ceiling, and that is accepted.** Lean
  4.34.1's C backend boxes `Nat`/`UInt8`/`UInt64` arithmetic; `USize` is an unboxed
  `size_t` only as an `@[extern]` argument and re-boxes once stored in a
  `Prod`/`Option`. Rewriting a parser to thread a `USize` cursor made it _slower_.
  Do not re-attempt pure-Lean micro-optimization to close the gap.
- **The packed cursor is `Nat`, not `USize`.** A `System.Platform.numBits = 64`
  premise would break the `[propext, Quot.sound]`-only gate. `commitRemainder` is
  `USize`-indexed (matching `byteSlice`) so there is no `Nat ↔ USize` roundtrip;
  the conversion is the caller's, once.
- **No unbounded `many` `Codec` value.** It is derived, not a constructor — verified
  un-implementable: the definition-order cycle `Codec → Productive → Rel → Codec`, and
  the mutual-inductive escape fails the universe check. Unbounded repetition is the
  already-proved `relRepeat`/`decodeRepeat`/`encodeRepeat` triple, exposed as a **run
  value**. See `basen-rfc-conformance-theorems`'s `design.md` §D0/D7.

## Lean proof ergonomics (learned the hard way)

- **`Classical.choice` trap.** A _dependent_ `cases`/`match` on a list whose
  **equation** sits in context (`bs.length = 1 ∨ bs.length = 2`, `ds.length = k`)
  leaks `Classical.choice` even when every cited lemma is `[propext]`-clean.
  Restate the hypothesis numerically (`1 ≤ bs.length`, `bs.length ≤ 2`) or derive
  the index from the term (`count ds.length …`) so the match stays non-dependent.
  Bisect by shrinking the body to `⟨_, rfl⟩`: if it still leaks, it is the match,
  not the arithmetic.
- **`omega` does not reason modulo.** It cannot derive `n % 4 = 0` from
  `n = 4 * k`. Convert to the equational form and `rw [hn, Nat.mul_mod_right]`.
- **Never `git stash` / `git reset` / `git checkout -- <file>` to "start clean"** —
  it has destroyed verified work here. If a proof will not compile, stub **that one
  theorem** to `sorry`, get the build green, and iterate in `/tmp/probe.lean`
  against the built library. Commit per law-family so a revert is never tempting.

## OpenSpec workflow

This repo uses OpenSpec (spec-driven). Changes live under `openspec/changes/`;
planning artifacts (proposal / spec delta / design / tasks) are written before
implementation. See `.pi/prompts/opsx-*.md`.

**Consider every open change when forming or validating a plan.** Before authoring
a new change's spec deltas — and before validating any plan, new or in-flight — run
`openspec list --json` to see _all_ active (`in-progress`, `complete`-not-yet-
archived) changes, read their deltas under `openspec/changes/<name>/specs/**`
alongside the main `openspec/specs/**`, then run `openspec validate --all`.

**The MODIFIED-block hazard.** Two changes that each clarify the _same_ requirement
can add _different_ scenarios to the same block; whichever syncs/archives first
leaves the other's MODIFIED block stale, and a MODIFIED requirement **replaces the
whole block**, so a later `openspec validate` flags the dropped scenario. Reconcile
such overlaps at planning time — carry every scenario into each delta's MODIFIED
block — rather than discovering the collision during archive.

**Archive ordering.** When two changes MODIFY the same requirement, archive the
dependency first and re-run `openspec validate --all` after **each** archive. Record
the required order in the later change's `tasks.md`.

## Git conventions

- Commit **individual files**, never `git add -A` or broad globs. Print the exact
  staged set (`git diff --cached --name-only`) before committing.
- A pre-commit hook runs `nix fmt` and **rejects** the commit if it reformats a
  staged file; re-`git add` and commit again. That is normal, not a failure.
- `lake-manifest.json` is gitignored (the library shouldn't pin deps);
  `flake.lock` **is** tracked, for reproducibility.
- New files matter to Nix: `src = ./.` snapshots only **git-tracked** files, so an
  untracked `Codec/*.c` breaks `nix build .#bench` from a clean clone.

## Skills

- Global Lean theorem-proving skill: `lean4` (official).
- Our supplement (project layout, proving-over-primitives, `partial`/coinduction
  lessons, the `Classical.choice` and `omega`-modulo traps above): global skill
  `lean`. Keep it generic — no project-specific details.
- Lean PR/convention/proof/MWE skills: `lean-pr`, `lean-bisect`, `lean-proof`,
  `lean-mwe`, `mathlib-build`, `mathlib-pr`, `mathlib-review`, `nightly-testing`,
  `lean4-setup` (all under the `leanprover` skill family).
- Nix: the `nix` skill; `devenv`/`devenv-migration` only for actual devenv work.
