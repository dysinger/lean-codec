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

## Where the truth lives

**One source of truth per concern.** When two files disagree, the left column wins:

| Question                                        | Authoritative file                      |
| ----------------------------------------------- | --------------------------------------- |
| The `Bytes` type's definition                   | `Codec/Codec.lean:68`                   |
| What is this library, why each design choice    | `README.md` (`[D#]`/`[S#]`), `PAPER.md` |
| What work is open, and how done is done         | `openspec/changes/<name>/tasks.md`      |
| What a change is _allowed_ to change            | `openspec/changes/<name>/proposal.md`   |
| The behavioural contract                        | `openspec/specs/**/spec.md`             |
| How this environment is set up and how to build | this file                               |

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

Run `openspec list --json` for the live answer; do not trust a snapshot here for
longer than the commit that wrote it.

### START HERE — `codec-review-remediation`

**The next session works `openspec/changes/codec-review-remediation/` and nothing
else.** Run the live counts with `nix develop --command openspec list --json`
(strip the dev-shell banner: `| sed -n '/^{/,$p'`); do not trust a snapshot here
for longer than the commit that wrote it. Currently **2/50**.

It is a codebase-wide audit. Four adversarial _reading_ lenses (74 findings, ids
`R<lens>.<n>`) cover the docs, the proof surface, `AGENTS.md`, and the global
`lean` skill; a fifth, **`R5`, added later because it _runs_ the binary**, is a
CRITICAL performance finding (id `R5.1`). `review.md` is the evidence base;
`tasks.md` is the work.

**Work order — do it in this sequence** (the full ordering, with the measured
justification for each step, is at the end of `tasks.md` §6 — read it there; this
is the summary):

1. **§6** — performance, in this internal order. **§6 must run before §3/§4**,
   because those rewrite the very paragraphs that quote the defect's numbers.
   - **6.1a — the bridge proof. This is a hard gate on all of §6.** Every
     optimization multiplies `decodeFullFastRoot`; with the bridge unproved, one
     false bridge invalidates every downstream ratio at once. **Nothing in §6 or
     the fast-path wiring proceeds until it lands.**
   - then **6.1b** (decode → `Array`+cursor, ≈6.5×) → **6.5** (encode →
     `encodeArray`'s shape, ≈4–6×) → **6.2** (re-baseline the docs against the
     _fixed_ numbers) → **6.3** (wire it) → **6.7** (wire the seam, once there
     is a consumer) → **6.4** (assert the ratio; threshold from 6.1b/6.3) →
     **6.6** (the carrier decision the bar forces).
2. **§2** — the Layer-2 seam (non-performance items).
3. **§3**, then **§4** — the doc rewrites, now against fixed numbers.
4. **§5** — the global `lean` skill, last (outside this repo).

- **The proof gate is real (1.3, done).** `lakefile.lean` sets
  `moreLeanArgs := #["-DwarningAsError=true"]` on the `codec` library, so a `sorry`
  fails `lake build` (and therefore `checks.lean`) instead of warning. Verified
  load-bearing by stubbing `Codec.roundtrip` and observing a non-zero exit naming
  the declaration. Every task after this one inherits it.
- **`R5.1` — the defect is FOUND and a 9047× fix LANDED; the bridge proof is still
  open.** Root cause (measured, after refuting `WellFounded.fix`/`Sigma`/`.attach`/
  `List` as no-ops): `decode` returns a `Suffix` whose `bytes` is a `bdrop` **closure
  over its input**, so feeding `t.bytes` back **composes closures** — quadratic, 668×
  at n=4096. `Codec.decodeFullFastRoot` re-roots at the original byte string with a
  consumed-count cursor: **93,531 → 188 µs (n=4096), 24,905,804 → 2,753 µs
  (n=65536)**, linear, ~22 MiB/s. **`decodeFullFastRoot` is verified by measurement,
  NOT yet by proof** — the equality bridge to `decodeFull` is task **6.1a**, and
  nothing calls the fast path yet. Do not describe it as proven, and do not wire it
  in — nor build any further optimization on it (6.1b/6.5/6.3 all multiply it) —
  until 6.1a lands.
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
- Its 50 tasks are sequenced: §1 cross-lens defects (5), §2 Layer-2 seam (8), §3
  `README.md` derivations (12), §4 `AGENTS.md` process (6), §5 the global `lean`
  skill (10), §6 performance (9, incl. 6.1a/6.1b). Two are already done (1.1,
  1.4).
- **§6's measured landscape** (one process, n=65536, `memcpy` = 2,136 MiB/s;
  re-take with the 6.4 lane rather than trusting this): `memcpy` 1× ·
  `encodeArray` 18× · `Id.run` cursor decode floor 36× · `decodeArray` 71× ·
  `fastEncodeRepeat` 79× · `encodeRepeat` 112× · `decodeFullFastRoot` 237×.
  **The fast shapes already exist and the public API does not use them** — most
  of §6 is wiring plus proof, not invention. **No path is within a single-digit
  multiple of C**, so the owner's bar is not met; 6.6 is where that is decided,
  and it must be decided honestly rather than by redefining the bar.

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
