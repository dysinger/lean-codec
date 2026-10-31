# AGENTS.md

Guidance for AI coding agents working in this repository.

**Four hard requirements, before anything else:**

1. **Play an audible alarm every time you pause** — see
   [Pause signal](#pause-signal-mandatory) below. It is a mandate, not a nicety.
2. **This file is a pointer to the active OpenSpec change, not a second copy of
   it.** Direction for the next session is `openspec/changes/<name>/`, applied
   through `openspec instructions apply`; `AGENTS.md` says _which_ change to work
   and _how this environment works_, and nothing else. Do not restate task lists,
   measured numbers, lemma tables, or status here — that is what `tasks.md` and
   `review.md` are for, and a copy in this file is stale the moment the ledger
   moves. When a fact already lives in `openspec/`, **link to it instead of
   duplicating it**; if this file and an `openspec/` artifact disagree, the
   artifact wins and this file gets fixed.
3. **Direction lives only here and in `openspec/`.** No `HANDOFF.md`, no
   `NOTES.md`, no `*-wip.lean` scratch files, no second place a next session could
   look. If a scratch file earns its keep, land its content in the library or in
   the change's `tasks.md` and delete the file.
4. **Work lands in the repo, and every session ends with a checkpoint commit.**
   Do **not** develop proofs in `/tmp` (or any path outside the repo) and intend
   to splice later. `AGENTS.md` permits `/tmp/probe.lean` for exactly one case —
   the library does not build and you need to iterate against the built library —
   and that file is deleted the moment the build is green again. New proofs, new
   lemmas, and half-finished cases are **written into `Codec/*.lean`**, with the
   unfinished obligation marked by a `sorry` that fails `lake build` (the gate is
   the honest marker). This is not a style preference: work in `/tmp` is invisible
   to `git`, to the build gate, and to the next session, and one reboot loses it.
   End every session with a commit (individual files, per the git conventions) so
   the tree is never the only copy of anything.

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

## Where the truth lives

**One source of truth per concern.** When two files disagree, the left column wins:

| Question                                        | Authoritative file                                |
| ----------------------------------------------- | ------------------------------------------------- |
| The `Bytes` type's definition                   | `Codec/Codec.lean:68`                             |
| What is this library, why each design choice    | `README.md` (`[D#]`/`[S#]`), `PAPER.md`           |
| **Which change to work next**                   | `openspec list --json` + `## Current state` below |
| What work is open, and how done is done         | `openspec/changes/<name>/tasks.md`                |
| The evidence behind a finding                   | `openspec/changes/<name>/review.md`               |
| What a change is _allowed_ to change            | `openspec/changes/<name>/proposal.md`             |
| The behavioural contract                        | `openspec/specs/**/spec.md`                       |
| How this environment is set up and how to build | this file                                         |

**Anything else is a summary.** If a summary and an `openspec/` artifact differ,
the artifact is correct and the summary is stale — fix the summary.

**`Bytes n` means `Fin n → UInt8`** (`Codec/Codec.lean:68`). That line is the
definition; every other document is a _record_ of it. A `Bytes` spelled without
its length index, or as `List UInt8`/`Array UInt8`/`ByteArray`, is a **defect**
in whichever doc contains it (including a changelog entry — a corrected entry can
drift again; a stated precedence cannot). The removed `List`-carrier's
`Array.extract`/`toList` transport lemmas are the `Classical.choice` source
`README.md`'s "Representations" section exists to keep out.

## Current state

**Do not record status here — point at it.** The live answer is one command:

```bash
nix develop --command openspec list --json | sed -n '/^{/,$p'
```

The active change is **`codec-review-remediation`**; work it and nothing else.
Its ledger is `openspec/changes/codec-review-remediation/tasks.md` (open work and
the definition of done), its evidence base is `review.md` (the adversarial
findings, ids `R<lens>.<n>`), and its edit licence is `proposal.md` / `design.md`.
Apply it with `openspec instructions apply --change codec-review-remediation
--json` rather than from memory of this file.

Two facts about that change are worth stating here **only because a reader who
skips the ledger would get them wrong**, and both are also in `tasks.md`:

- **The work order is §6 → §2 → §3/§4 → §5**, and **6.1a is a hard gate** on the
  rest of §6 (`decodeFullFastRoot = decodeFull` is currently verified by
  _measurement only_). §6 goes first because §3/§4 rewrite the paragraphs that
  quote the numbers §6 fixes. If `tasks.md` disagrees with this line, `tasks.md`
  wins.
- **Only `R5.1` may change a declaration _shape_** (design D9), and it must keep
  every theorem's statement, prove the new definition equal to the old, and stay
  `[propext, Quot.sound]`-only / zero-`sorry` / `#eval`-able. Nothing else may.

`lean-basen` (18/25) is a separate change whose work happens in the sibling repo
`../lean-basen`, in that repo's own `nix develop`; it does not touch this tree.

**History is not direction.** What landed, when, and what was measured belongs in
the change's `tasks.md` and in `CHANGELOG.md` — including for archived changes,
whose own `tasks.md` under `openspec/changes/archive/` is the reference. Do not
re-teach landed work here, and do not extend an archived change with new audit
work.

**Archive hazards, recorded where the archive step will look for them.** A
MODIFIED requirement **replaces** the whole block on archive, so: re-read
`openspec/specs/<area>/spec.md` immediately before archiving, confirm the delta's
text is a superset, and run `openspec validate --all` after **each** archive. Two
changes modifying the same requirement must archive dependency-first, with the
required order recorded in the later change's `tasks.md`. (`lean-basen` carries
the last live instance of this: it MODIFIES "The `basen` bases are `Codec`
values".)

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

Every command below names **its own repository**. They are different flakes with
different `checks` sets — never run one tree's recipe in the other.

### In `lean-codec` (this repo)

```bash
nix develop --command lake build            # 13 jobs, zero warnings; FAILS on `sorry`
nix develop --command lake build bench      # the bench lane (links Codec/ByteSlice.c)
nix develop --command openspec validate --all   # after ANY spec or task edit
```

**`lake build` enforces zero-`sorry`.** `lakefile.lean`'s `codec` lib carries
`moreLeanArgs := #["-DwarningAsError=true"]`, so `sorry`'s
`declaration uses 'sorry'` warning becomes an **error** and the build exits
non-zero naming the declaration. `default.nix`'s `check` runs that same build, so
`nix build '.#checks.…'` is the gate, not an observation. Verified load-bearing:
stubbing `Codec.roundtrip` to `sorry` fails the build with
`error: Codec/Sound.lean:441:8: declaration uses \`sorry\``.

Because the flag is on the _library_ rather than on one consumer, every path that
compiles `Codec` inherits it (including `bench` and the sandboxed `check`) —
there is no separate lint to drift from the compiler.

`nix build '.#checks.aarch64-darwin.lean'` is the same build, sandboxed — it is a
**long** build: detached with `nohup … > /tmp/x.log 2>&1 &`, then poll. Never
foreground it. To check one law by hand (in-repo):

```bash
printf 'import Codec\n#print axioms Codec.roundtrip\n' > /tmp/c.lean
nix develop --command lake env lean /tmp/c.lean    # expect [propext, Quot.sound]
```

### In `../lean-basen` (its own `nix develop`)

```bash
nix develop --command lake build         # library + Axioms.lean: zero sorry/warnings
nix develop --command lake build bench   # the bench lane (dev-loop; there is no
                                         # packages.bench — that repo's task 5.3)
```

`Axioms.lean` is a `@[default_target]` lib, so `lake build` runs its `#guard_msgs`
gates; a `Classical.choice` regression fails the build. To check one law by hand:

```bash
printf 'import BaseN\n#print axioms BaseN.Base64.decodeFullB64_reject_arity\n' > /tmp/c.lean
nix develop --command lake env lean /tmp/c.lean    # expect [propext, Quot.sound]
```

### The rail for a cross-repo import failure

`bad import 'Codec.Normal'` (or any core module) from `../lean-basen`'s
**sandboxed** build does **not** mean a bad import: the flake's `codec` pin
predates that module. Check `../lean-basen/flake.lock` →
`nodes.codec.locked.rev` against `git log --oneline -1 -- Codec/Normal.lean` here,
then `nix flake update codec` (targeted — not all inputs) and `lake update codec`
in `../lean-basen`. Never "fix" it by editing the importing Lean file.

- **Axiom discipline.** Every law stays `[propext, Quot.sound]`-only, zero
  `Classical.choice`, zero `sorry`. `#print axioms Codec.roundtrip` is the check;
  `../lean-basen`'s `Axioms.lean` is a `@[default_target]` lib so `lake build`
  enforces its `#guard_msgs` gates. **In _this_ repo the gate is enforced too**
  (`moreLeanArgs := #["-DwarningAsError=true"]` in `lakefile.lean`): a `sorry`
  fails `lake build` instead of warning. What is _not_ machine-enforced here is
  the `Classical.choice` half — that is what `#print axioms` is for, run per law
  family rather than by the build.
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
- **Decode/encode must stay within a small single-digit multiple of C — a
  requirement, not an aspiration.** Measured achievable floor: **~8.5×** a
  `memcpy` floor (222 vs 1,891 MiB/s) with the cursor shape. Lean 4.34.1's C
  backend boxes `Nat`/`UInt8`/`UInt64` arithmetic; `USize` is an unboxed `size_t`
  only as an `@[extern]` argument and re-boxes once stored in a `Prod`/`Option`.
  Rewriting a parser to thread a `USize` cursor made it _slower_ — but that is a
  fact about **boxed scalars**, not a licence for a 47× or 10^5× path. Those come
  from the **data you hand the next step**: `decodeArray`'s per-step `List` costs
  47×, and `decodeFull`'s chained `bdrop` closures cost ~10^5× (`R5.1`). Fast shape:
  `Array UInt8` + integer cursor + accumulating `Id.run` loop returning
  `(value, consumed)`. Do not quote an absolute MiB/s target — assert the **ratio**
  to a same-run `memcpy` (§6.4). Do not re-attempt pure-Lean micro-optimization
  _below_ the bar; that rule is what the old "20–40×" claim was propping up, and
  it was false.
- **The packed cursor is `Nat`, not `USize`.** A `System.Platform.numBits = 64`
  premise would break the `[propext, Quot.sound]`-only gate. `commitRemainder` is
  `USize`-indexed (matching `byteSlice`) so there is no `Nat ↔ USize` roundtrip;
  the conversion is the caller's, once.
- **No unbounded `many` `Codec` value.** It is derived, not a constructor — verified
  un-implementable: the definition-order cycle `Codec → Productive → Rel → Codec`, and
  the mutual-inductive escape fails the universe check. Unbounded repetition is the
  already-proved `relRepeat`/`decodeRepeat`/`encodeRepeat` triple, exposed as a **run
  value**. See the archived `basen-rfc-conformance-theorems`'s `design.md`
  §D0/D7 under `openspec/changes/archive/`.

## Lean proof ergonomics (learned the hard way)

- **`Classical.choice` trap — three verified shapes.** All three are silent (`#print
axioms` on the enclosing theorem is the only check) and all three happened here:
  1. **Dependent `cases`/`match` on a list whose _equation_ sits in context**
     (`bs.length = 1 ∨ bs.length = 2`, `ds.length = k`) — leaks even when every
     cited lemma is `[propext]`-clean. Fix: restate the hypothesis numerically
     (`1 ≤ bs.length`, `bs.length ≤ 2`) or derive the index from the term
     (`count ds.length …`) so the match stays non-dependent.
     **Bisection is goal-shaped, not universal.** Shrinking the body to
     `⟨_, rfl⟩` bisects a **sigma/`∃`** goal. On any other goal shape it does not
     typecheck at all (`⟨_, rfl⟩` is not a term there), so the prescribed
     bisection silently fails rather than isolating the leak. For a
     `decide … = true` goal, prefer rewriting the _proof shape_ — the disjunction
     form of shape 2 below is often the real culprit.
  2. **`decide_eq_true (by omega)` on a disjunction** — `omega` closes a disjunction
     by case analysis, which pulls in classical logic. `decide` alone is fine; the
     _disjunctive_ proof is not. Fix: build the disjunct explicitly
     (`decide_eq_true (Or.inl ⟨a, b⟩)`) and let `omega` close only the arithmetic
     leaf. Reproducer: a `decide ((48 ≤ n ∧ n ≤ 57) ∨ (65 ≤ n ∧ n ≤ 70)) = true`
     goal closed with `decide_eq_true (by omega)` reports
     `[propext, Classical.choice, Quot.sound]`.
  3. **A `match`/`if` on a `Bool` in the _goal_** — a dependent match: `cases b`
     fails with "Dependent elimination failed", and `subst h; rfl` fails with
     "not definitionally equal to `match true, ⋯`". Fix: split the claim into
     `_true`/`_false` lemmas, or `cases b <;> simp_all`.
- **`omega` and modulo.** It **cannot** use a modulo _hypothesis_
  (`n % 4 = 0`) or prove an existential from one; the equational form
  `n = 4 * k → n % 4 = 0` _is_ in its fragment. When it stalls, rewrite to the
  equational form and `rw [hn, Nat.mul_mod_right]`.
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

## Pause signal (MANDATORY)

**Always play an audible alarm when you pause.** Every time you stop and hand
control back to the owner — end of session, blocked on a question, waiting for a
decision, or presenting options — play an alarm first, then write the summary.
This is a **mandate**, not a nicety: the owner steps away while a long task runs
and relies on the sound, not on watching the terminal, to know when to come back.
A pause with no alarm is a defect in the session — the owner may sit idle for
minutes before noticing your output.

Play one for ~5 seconds (macOS):

```bash
for i in 1 2 3 4 5 6 7 8; do afplay /System/Library/Sounds/Sosumi.aiff 2>/dev/null & sleep 0.35; done; wait
```

- **Play it first, then write prose.** The alarm must arrive _before_ the summary
  it announces. Playing it after the last line defeats the purpose — by then the
  reader has already been waiting.
- **Do not skip it because the pause feels brief.** A one-line "which option?"
  question is exactly the kind of pause this exists for.
- **Do not skip it because it might be noisy.** That judgement belongs to the
  owner, not the agent.
- If `afplay` is unavailable, fall back to terminal bells (`printf '\a'`) in a
  loop, and say which fallback was used.

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
