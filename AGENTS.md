# AGENTS.md

Guidance for AI coding agents working in this repository.

**This file is forward-looking operating instructions, not a session diary.**
History — what landed when, what was reverted, what a past session measured —
belongs in `openspec/` (the task ledger) and `CHANGELOG.md`. Do not append
"session status" sections here; that practice is what made this file 536 lines
of mutually-contradicting snapshots. Keep it short and true.

**Where a session leaves its handoff: the `## Current state` block below, in
place.** Rewrite that block; do not add to it, and do not create a new
`HANDOFF.md`/`NOTES.md`/`STATUS.md` per session — a second handoff file is the
same session-diary failure in a different filename, and it silently rots the
moment `Current state` disagrees with it. The distinction that keeps this file
honest: `Current state` states _what is true now and what is next_ (always
rewritten, never appended), while _how it got there_ and _what was measured_ live
in the change's `tasks.md` and in `CHANGELOG.md`.

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
  packed layer (`Codec/Packed.lean`, `Codec/DecodeOne.lean`), the Layer-2 trust
  seam (`Codec/ByteSlice.lean` + `.c`), and the normal-form layer
  (`Codec/Normal.lean`, below). Every law is `[propext, Quot.sound]`-only, zero
  `sorry`. `@[default_target] lean_lib codec` is the proof gate; `lean_exe bench`
  is the benchmark.
- **NOTHING IS COMPLETE. Do not archive anything.** An adversarial review
  (`openspec/changes/codec-review-remediation/`, 74 findings, 2 CRITICAL) found
  the documentation and the proof gate defective _in the work that was marked
  complete_. The task checkboxes are not the measure; the review is.
- **The ticked counts are not completion claims.** `codec-normal-form-case-quotient`
  16/16 and `basen-rfc-conformance-theorems` 31/31 mean _their own authored tasks
  are done_. Both carry a `> STATUS: NOT COMPLETE — DO NOT ARCHIVE` banner in
  their `tasks.md`, and both are **reopened** by `codec-review-remediation`
  (0/41). "Complete" for them means _their spec text and gate survive the review_
  — remediation tasks §1–§4.
- **Why the checkboxes lied:** `codec-normal-form-case-quotient` was marked
  16/16 and called "ready to archive" while (a) the zero-`sorry` gate it relied on
  was never enforced by the build, and (b) `CHANGELOG.md` advertised the removed
  `List UInt8` substrate. `openspec validate --all` was green throughout — it
  checks **schema conformance, not truth**. Never cite it as evidence of
  completion.
- **The evidence base:** `codec-review-remediation/review.md` (four verbatim
  reviews, ids `R<lens>.<n>`). Read its **"Verified-correct claims — do not
  re-litigate these"** list before re-opening anything; it records what was
  tested and held so it is not re-derived.
- `lean-basen` is 18/25 (seven mechanical polish items).

### `codec-normal-form-case-quotient` — tasks ticked 16/16, **NOT complete**, reopened

The information-free-variation layer (`Codec/Normal.lean`): `Normal S norm` (the
quotient `S/~` as the fixed points of a total idempotent `norm`), `Normalizer S
norm` (idempotence in the **type**; `norm` is a **parameter**, not a field, so
`Normal S norm` is definitionally shared), `fill`, `fill_fixed` (`norm ∘ fill =
id`, **no axioms**), `fill_surj`, `fill_inj`, and `decodeNormal` (the normalising
decoder — `norm` composed **outside** an ordinary `Iso`; not an `Iso`, no inverse)
with `decodeNormal_of_fixed` / `decodeNormal_encode`. **`Iso.law` is untouched.**
`Codec/Normal.lean` is fully **generic** — polymorphic in `S : Type`, no
`UInt8`/`Bytes`/hex/ASCII/text in the code, so `[S3]` holds.

Task 5.1 (its downstream consumer) is **done** — see `../lean-basen` below.

### `../lean-basen` — tasks ticked 31/31, **NOT complete**, reopened

The active downstream is `../lean-basen` (sibling repo — package `basen`, module
`BaseN`; base-2/4/8/10/16/32/64, all seven landed and proven as `Codec` values).
It consumes `codec` **by git input**, so a core change is only visible there after
pushing `lean-codec` and running `lake update codec` in `../lean-basen`. Its
`BaseN/Common.lean` already imports `Codec.Normal`. **Work there, in its own
`nix develop`.**

`openspec/changes/basen-rfc-conformance-theorems/` has its **31/31** tasks ticked,
but is **NOT complete** — reopened by `codec-review-remediation` (see above).

- **7.1, 7.2 (DONE)** — all seven bases state the in-image converse
  (`decodeFull_B{2,4,8,10,16}_char` join `decodeFullB{64,32}_char`), and the
  withdrawal of the "unrepresentable" claim is reversed via
  `decodeFullB{64,32}_char_via_type` / `_spine` / `b{64,32}BytesOf_tail1_eq`.
- **7.3 (DONE).** Base16 case-insensitive decoding (RFC 4648 §8), landed in
  `BaseN/Base16.lean`. Its old rationale — "folding case breaks `Unambiguous`" —
  was **false** and is withdrawn: `Unambiguous` constrains one input to at most one
  value, and folding case is a total function. The real constraint is the
  **canonicality of encode**, which holds (`encodeHex` emits uppercase only).
  Spec delta, `proposal.md`, `design.md` D6 and task 3.3 are amended;
  `rejects_lowercase`'s false rationale is withdrawn in-tree.

  **Two findings that changed the plan, both verified — do not rediscover them:**
  1. The planned commutation `hexBlockApply (foldList cs) = hexBlockApply cs` is
     **false**: `['6','f']` is rejected yet folds to the accepted `['6','F']` —
     that rejection-to-acceptance IS the §8 widening. The `Iso` law needs the
     one-directional `hexBlockApply_foldList` (`= some b → … = some b`); the
     refutation is `hexBlockApply_foldList_ne`.
  2. `decide_eq_true (by omega)` on a **disjunction** leaks `Classical.choice`
     (`omega` case-splits) — build the disjunct explicitly. A `match` on a `Bool`
     **in the goal** leaks too — split into `_true`/`_false` lemmas.

- **`lean-basen` shows 18/25** but is complete except **seven mechanical polish
  items** (5.2, 5.3, 5.4, 5.8, 5.9, 5.12, 5.13), listed in
  `openspec/changes/lean-basen/tasks.md` under "Still open — mechanical polish".
  Read them there; they are doc/tidy items, not proofs.

**Archive ordering — BLOCKED, not just "in this order".** Nothing is archivable
now. When it becomes unblocked (remediation §1–§4 green), the ordering constraint
is: both changes MODIFY the requirement "The `basen` bases are `Codec` values",
and archiving keeps only one version. The two MODIFIED/synced texts were
deliberately made identical (task 6.11), so either order is then _safe_ — but
archive **`lean-basen` first**, then `basen-rfc-conformance-theorems`, running
`openspec validate --all` after **each**, and re-reconcile the MODIFIED blocks if
the §8 wording lands in both.

**Why archiving is blocked:** archive freezes the change's spec text into
`openspec/specs/`. The review found passages in that text wrong (`[D4]`'s
mechanism, the `[S1]`/`[S4]` contradiction, the `[S6]` `sepBy` claim, and the
base16 case wording). Freezing them would make the defect permanent and propagate
it to every downstream repo that reads `openspec/specs/`.

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

## Standing preference (the owner's bias — apply it without being asked)

**Always take the most correct solution, not the most convenient one.** This is a
standing instruction, not a per-session choice. Concretely:

- When a plan's stated lemma turns out to be **false**, prove the true statement
  and fix the plan. Do not narrow, weaken, or paper over it to keep the plan. Do
  not stop and offer "the weaker option" as an alternative.
- Prefer the formulation that is actually true and sufficient, even when it is
  more work, an extra case split, a stronger hypothesis, or an extra file.
- If a choice is between _correct_ and _cheap_, take correct. If between two
  correct options, take the one that is more honest about its preconditions.
- Pause and ask only when the requirement itself is genuinely ambiguous or when
  doing the correct thing would be **outside the change's declared scope** — never
  merely because the correct path is harder.
- Record findings and refutations where the next reader will look (`tasks.md`,
  module docstrings), rather than silently diverging from the plan.

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
