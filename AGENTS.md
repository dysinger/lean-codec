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

## Current state

Run `openspec list --json` for the live answer; do not trust a snapshot here for
longer than the commit that wrote it.

### START HERE — `codec-review-remediation`

**The next session works `openspec/changes/codec-review-remediation/` and nothing
else.** Run the live counts with `nix develop --command openspec list --json`
(strip the dev-shell banner: `| sed -n '/^{/,$p'`); do not trust a snapshot here
for longer than the commit that wrote it. Currently **2/45**.

It is a codebase-wide audit. Four adversarial _reading_ lenses (74 findings, ids
`R<lens>.<n>`) cover the docs, the proof surface, `AGENTS.md`, and the global
`lean` skill; a fifth, **`R5`, added later because it _runs_ the binary**, is a
CRITICAL performance finding (id `R5.1`). `review.md` is the evidence base;
`tasks.md` is the work.

**Work order — do it in this sequence:**

1. **§1** — tasks 1.2, **1.3**, 1.5. Small, and 1.3 is the one that matters: it
   makes the proof gate real for every task after it.
2. **§6** — the `R5.1` performance defect (4 tasks). **This must run before §3
   and §4**, because those rewrite the very paragraphs that currently quote the
   defect's numbers; correcting prose against unfixed numbers would canonize the
   defect.
3. **§2** — the Layer-2 seam.
4. **§3**, then **§4** — the doc rewrites, now against fixed numbers.
5. **§5** — the global `lean` skill, last (outside this repo).

- **Task 1.3 makes the proof gate real.** `AGENTS.md` used to call zero-`sorry`
  "the proof gate" while `default.nix`'s `check` ran a plain `lake build`, which
  only _warns_ on `sorry`. Fixing that is a `default.nix` change and it makes the
  gate real for every change after this one.
- **`R5.1` — the defect is FOUND and a 9047× fix LANDED; the bridge proof is still
  open.** Root cause (measured, after refuting `WellFounded.fix`/`Sigma`/`.attach`/
  `List` as no-ops): `decode` returns a `Suffix` whose `bytes` is a `bdrop` **closure
  over its input**, so feeding `t.bytes` back **composes closures** — quadratic, 668×
  at n=4096. `Codec.decodeFullFastRoot` re-roots at the original byte string with a
  consumed-count cursor: **93,531 → 188 µs (n=4096), 24,905,804 → 2,753 µs
  (n=65536)**, linear, ~22 MiB/s. **`decodeFullFastRoot` is verified by measurement,
  NOT yet by proof** — the equality bridge to `decodeFull` is task 6.1's remaining
  work, and nothing calls the fast path yet. Do not describe it as proven, and do not
  wire it in until the bridge lands.
- **Two earlier diagnoses of `R5.1` were REFUTED — do not re-measure them.** Both
  looked plausible and both were no-ops:
  1. _"`WellFounded.fix` on a `Sigma` doesn't compile to a loop."_ Re-expressing
     structurally measured **0.5%** apart (93,691 vs 94,137 µs at n=4096) — Lean's
     `termination_by` elaborates to the same well-founded recursion. See
     `review.md` §"The refuted diagnosis".
  2. _"`decodeFullStep` is a backtracking search."_ It does re-call `decode p s`
     per level, but a tail-recursive rewrite with the same calls was **still**
     1.5 s at n=16384; the search was never the cost. See
     `review.md` §"The root cause, found".
     What _is_ settled: the **`bdrop` closure chain** (bullet above), which was found
     by A/B-ing chained `t.bytes` against flat `bdrop m root` over identical work.
     `decodeRepeat`'s Θ(n²) is separate and inherent to its all-prefix return type;
     it is **not** in scope for a speed fix.
- **`R5.1` carries the change's one shape-changing carve-out** (design D9): §6 may
  change `decodeFull`'s _algorithm_, but must keep every theorem's statement,
  prove the new definition equal to the old (`decodeFull_some` +
  `decodeFull_ne_none` are the bridge; `decodeFull_spec` then follows with `huniq`
  unchanged), and preserve `[propext, Quot.sound]`-only / zero `sorry` /
  `#eval`-ability. Nothing else may change a declaration shape.
- **None of its findings concern `basen`.** Do not extend an archived change with
  audit work.
- Its 45 tasks are sequenced: §1 cross-lens defects (5), §2 Layer-2 seam (8), §3
  `README.md` derivations (12), §4 `AGENTS.md` process (6), §5 the global `lean`
  skill (10), §6 the `R5.1` performance defect (4). Two are already done (1.1,
  1.4).

### The other open change — `lean-basen` (18/25)

`openspec/changes/lean-basen/tasks.md` holds **seven mechanical polish items**
(5.2, 5.3, 5.4, 5.8, 5.9, 5.12, 5.13) under "Still open — mechanical polish".
Doc/tidy items, not proofs. Its work happens in `../lean-basen` (sibling repo —
package `basen`, module `BaseN`; all seven bases landed and proven as `Codec`
values), in that repo's own `nix develop`.

**Archive hazard for `lean-basen` (the last one).** It MODIFIES the `basen`
requirement "The `basen` bases are `Codec` values", and a MODIFIED block
**replaces** the whole block on archive. Re-read `openspec/specs/basen/spec.md`
immediately before archiving it, confirm the delta's text is a superset (it is
today), then `openspec validate --all`.

### Landed and archived (do not re-teach)

- **`codec-normal-form-case-quotient`** (16/16) → `openspec/specs/codec/normal-form/`.
  The information-free-variation layer (`Codec/Normal.lean`): `Normal S norm` (the
  quotient `S/~` as the fixed points of a total idempotent `norm`), `Normalizer S
norm` (idempotence carried by the _type_; `norm` is a parameter, not a field, so
  `Normal S norm` is definitionally shared), `fill`, `fill_fixed` (`norm ∘ fill =
id`, **no axioms**), `fill_surj`, `fill_inj`, and `decodeNormal` (`norm` composed
  **outside** an ordinary `Iso`; not an `Iso`, no inverse) with
  `decodeNormal_of_fixed` / `decodeNormal_encode`. **`Iso.law` untouched.** The
  module is generic in `S : Type` — no `UInt8`/`Bytes`/hex/ASCII/text in the code,
  so `[S3]` holds.
- **`basen-rfc-conformance-theorems`** (31/31) → `openspec/specs/basen/`.
  All seven bases state the in-image converse (`decodeFull_B{2,4,8,10,16}_char`
  join `decodeFullB{64,32}_char`); `decodeFullB{64,32}_char_via_type` / `_spine` /
  `b{64,32}BytesOf_tail1_eq` reverse the "unrepresentable" withdrawal; and
  **RFC 4648 §8** Base16 case-insensitive decoding landed in
  `../lean-basen/BaseN/Base16.lean`.

  **Two verified findings from §8 — do not rediscover them:**
  1. The planned commutation `hexBlockApply (foldList cs) = hexBlockApply cs` is
     **false**: `['6','f']` is rejected yet folds to the accepted `['6','F']` —
     that rejection-to-acceptance _is_ the §8 widening. The `Iso` law needs the
     one-directional `hexBlockApply_foldList`; the refutation is
     `hexBlockApply_foldList_ne`.
  2. The old rationale "folding case breaks `Unambiguous`" was **false**:
     `Unambiguous` constrains one input to at most one value, and folding is a
     total function. The real constraint is the **canonicality of encode**, which
     holds (`encodeHex` emits uppercase only).

Severity-tagged evidence behind the archived §6 hardening tasks is in that
change's own `tasks.md` under `openspec/changes/archive/` — history, not a to-do.
(Its once-separate `REVIEW-basen-rfc-conformance.md` was deleted: nothing
referenced it, and direction comes from this file plus `openspec/`.)

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

Every command below names **its own repository**. They are different flakes with
different `checks` sets — never run one tree's recipe in the other.

### In `lean-codec` (this repo)

```bash
nix develop --command lake build            # 13 jobs, zero warnings — NOT yet a sorry gate
nix develop --command lake build bench      # the bench lane (links Codec/ByteSlice.c)
nix develop --command openspec validate --all   # after ANY spec or task edit
```

**`lake build` does not enforce zero-`sorry` today** — it reports `sorry` as a
_warning_. Task 1.3 adds `-DwarningAsError=true` to `default.nix`'s `check`
derivation; until it lands, check by hand (`grep -rn 'sorry' Codec/` → zero, in
prose only) and do not describe the gate as enforced.

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
  enforces its `#guard_msgs` gates. **In _this_ repo the gate is not yet enforced**
  (`lake build` only warns on `sorry`) — task 1.3 makes it real; until then verify
  by hand and say "observed", not "enforced".
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
     (`count ds.length …`) so the match stays non-dependent. **Only when the goal
     is a sigma/`∃`** does bisecting with `⟨_, rfl⟩` work.
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
