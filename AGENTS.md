# AGENTS.md

Guidance for AI coding agents working in this repository.

> ## START HERE: run `openspec list --json`, then read that change's `tasks.md` banner
>
> **One `codec` change is open: `codec-audit-round-nine`.** It is **ready to implement**
> and it is the only thing to start.
>
> `codec-gate-denominators` **landed and archived** 2026-11-08 (41/41, synced
> `+10 / -0`). It is history now — read
> `openspec/changes/archive/2026-11-08-codec-gate-denominators/` for what it established,
> and **do not re-implement it.** In particular its `isBareProj` predicate is landed and
> gate-green; round nine's task 6.2 is struck because that predicate supersedes it.
>
> The two `basen` changes (`basen-uppercase-prepass`, `basen-nat-iso`) are **PARKED by
> the owner** pending a library-division decision. Do not start them.
>
> ### Before you start round nine, read its banner — it re-scopes the change
>
> Round nine was authored **before** `codec-gate-denominators` existed, so its `tasks.md`
> now carries a **re-evaluation table** at the top. Eight of its findings are closed or
> re-scoped by the landed work, and **five of its 69 boxes are struck through** — those
> are done, not pending:
>
> - **6.2** is **wrong and deleted**: the head-constant set captures `Codec.roundtrip`.
>   The landed predicate is the answer. Do not implement the task.
> - **6.3, 6.6, 6.7, 6.8, 6.10** are **done** by the archived change. Read the strike-out
>   note before "finding" them again.
> - **6.1(c)** asked for an assertion that is **false and unassertable**: `eq_irrel`'s
>   last component matches none of the eight suffixes, so the classifier never dropped it.
>   The `authored` exception is **dead code** — a stronger finding than the original.
> - **5.3** was re-measured and its answer is none of the three candidates it lists:
>   see **5.3a**, a **new MUST** that is the most important thing in the change.
>
> **The count is therefore not "13 MUST / 17 SHOULD / 12 NITPICK".** Believe the banner
> and the checkboxes, never this box.
>
> ### 5.3a is the finding to internalise: the vocabulary was never audited
>
> Round nine's N-4 was "`blitBytes_spec`'s docstring states a footprint the gate
> contradicts". The question was _why the arm didn't fire_, and the three candidates
> offered (attribution, `thmInfo` scope, the `skipped = 8` bucket) were **all wrong**.
>
> Measured (`scratch/probe-vocabulary.lean`): the docstring writes
> `` `[propext, Quot.sound]` `` **without `-only`**, and `footprintClaimPhrases` only
> recognises the `-only` spellings — so the segment **never became a claim site at all.**
> Not checked, not skipped, not out of scope. An environment walk puts the hole at
> **22 of 159** `thmInfo` docstrings containing a backticked axiom-list literal, and the
> blind set includes **`Codec.Bytes.ext_iff`** and **`Codec.findByte_spec`** — both of
> which this repo believes it audited.
>
> **The lesson, and it is the sharpest one yet:** `codec-gate-denominators` audited the
> arms' **filters** — what removes things from the input — and the obligation it installed
> is about denominators and removals. But a _vocabulary_ is a filter too, one level down,
> and nothing asserted it was **complete over the spellings the tree actually uses**. That
> is round eight's §5 lesson (a hoisted list that cannot be narrowed silently) failing to
> generalise to "a list that cannot be silently too _short_". When you fix 5.3a, the arm
> must report **two** counts — what the vocabulary recognised, and how many docstrings
> contain a backticked axiom-list literal **at all** — and assert that they reconcile.
>
> ### This box has gone stale twelve times
>
> It has named a landed change, denied an open one, and undercounted tasks, repeatedly.
> **Believe the command, never this box.** It names the _change and the order_, never a
> task count, and **not the finding count either** — round nine's re-evaluation changed
> that by more than a deletion pass would suggest.
>
> ### Why the ninth and tenth rounds exist, in one paragraph
>
> Ten adversarial rounds have produced **zero soundness defects** — no
> `Classical.choice`, no `sorry`, every law `[propext, Quot.sound]`-only. What they
> produce, every round, is **one defect class, fourteen times over**: _a check whose input
> has a filter that nothing audits._ `codec-gate-denominators` exists to stop that at the
> generator instead of fixing instance fifteen. Read its proposal's table of all fourteen
> — it is the single most useful page in `openspec/` for understanding why the gate arms
> are shaped the way they are.
>
> ### What round eight closed, and the one thing to carry forward
>
> Round eight's findings were **all one shape: a check that reports nothing.** Four of
> them, and each is now a printed, asserted count:
>
> | was invisible                                                                                         | now                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           |
> | ----------------------------------------------------------------------------------------------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
> | `opaqueInfo`/`axiomInfo` — matched by **no arm** of eight, and `exclusions` _refuses_ an `opaque`     | a `constantKindCensus` arm prints all seven `ConstantInfo` kinds and **fails** the build on a non-zero `opaque`/`axiom`                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       |
> | `propProjections`' validity — the docstring said a non-projection entry "would fail"; nothing checked | a second arm reads the **same** `isBareProj`; mutation-tested                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 |
> | the footprint arm's denominator — it printed how many claims it **read**, never how many existed      | `769 scanned / 144 mentioning / 154 found / 146 checked` + the skip split `0 other-theorem / 0 no-owner / 8 def-docstring`. **Five are asserted** (`146 checked`, `144 mentioning`, and each of the three skip causes, by `expectedFootprintCounts`); `769 scanned` and `154 found` are printed-only — `found` needs no constant because `found = checked + all three causes` is itself asserted. (Round ten measured that an earlier version of this cell said "three are asserted, `8 left`"; `codec-gate-denominators` §1.3 then split the `8` by cause, so the number of asserted quantities moved from three to five. An earlier revision said "this cell claimed all five were asserted" — that was the _round-ten_ finding, and the cell was corrected then; this note records the later change, not a contradiction.) |
> | `gen-axioms.lean`'s **mirror** of `propProjections`                                                   | drift found and fixed; it had un-pinned `Codec.Suffix.hle` while `headerNumbers` read the mirror's own count, so the numbers agreed with each other and not with the tree                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     |
>
> **The lesson, now five times over, and the fifth one is the sharpest:** a check is only
> as good as what _enters_ it — and a **mirror list is a name list.** Round five's
> `isDerivedDefName` removed `Iso.prod` from a green gate; round seven's
> `nm.getPrefix == \`Codec` removed 139 declarations; round eight's attribution rule
> skipped two live claims; and round eight's regeneration found a _second copy_ of a
> name list, three entries to the real one's four, that had been silently un-pinning a
> law. Two lists that must agree, and no arm comparing them, is the same defect as one
> list with no completeness arm. **When you add a check, ask what removes things from
> its input, whether that removal is recorded — and whether anything else holds a copy
> of the same list.**
>
> ### `nix fmt` does not format markdown here — use the flake formatter
>
> Cost a build cycle in round eight, so it is here, not buried. **`nix fmt` in this
> dev shell has no `prettier`**: it formats `*.nix` only and prints "0 changed" for
> markdown it never touched. Every "`nix fmt` clean" claim in this file's history and
> in the archives covered Lean and Nix and **not markdown**. The real markdown gate is
> `checks.aarch64-darwin.formatting` (treefmt + sandboxed prettier), reachable as
> `nix build .#formatter.aarch64-darwin`; it **caches per tree**, so after an
> out-of-band edit run it with `--clear-cache`, and remember the check reads the
> **git tree**, so an uncommitted fix cannot turn it green. Round eight found a
> pre-existing red this way (`185eebd`, an archived ledger).
>
> ### The archive hazard, which has now fired three times
>
> A MODIFIED block **replaces** the live requirement wholesale, so any live scenario the
> delta does not restate is dropped at sync time. Two changes modifying the same
> requirement must archive dependency-first, with the order recorded in the later
> change's `tasks.md`. Fired in `lean-basen` / "The `basen` bases are `Codec` values",
> and twice in `codec/axiom-gate` (`round-two`→`round-three`, then `round-three`
> rewriting `round-two`'s text). **Check the live spec's scenario count against the
> delta's before syncing** — `openspec validate` will not always catch a narrowed set.
> Round eight's archive was checked: `+96 / ~0 / -0`, 32 scenarios, nothing dropped.
> Do the same for any future change that touches a requirement another already rewrote.
>
> ### History, so it is not re-invented
>
> `codec-audit-round-five` closed 46/46 and archived 2026-11-07
> (`R6-01`…`R6-38`; the def-side audit arms). `codec-audit-round-four` closed 52/52
> (`R5-01`…`R5-37`). `codec-audit-round-three` closed 56/56 on 2026-11-06 (7
> requirements added, 6 modified, 0 removed). `codec-audit-round-two` closed 42/42 on
> 2026-11-05. All four are additive-only deltas, verified scenario-by-scenario at their
> archive time rather than assumed. Read an archived `tasks.md` as **history**; do not
> reopen it.

## Current state

**Do not record status here — compute it.** The ledger is the source of truth:

| Question                       | Authoritative file                                                               |
| ------------------------------ | -------------------------------------------------------------------------------- |
| **What is the task right now** | whatever `openspec list --json` reports; **`codec-audit-round-nine` today**      |
| Open changes + task counts     | `nix develop --command openspec list --json`                                     |
| Are the spec deltas sound      | `nix develop --command openspec validate --all`                                  |
| Archived history               | `openspec/changes/archive/<date>-<name>/tasks.md` (e.g. `2026-11-05-lean-basen`) |
| Lessons (not direction)        | `openspec/lean-notes.md`                                                         |

**`codec` has one open change: `codec-audit-round-nine`, ready to implement.** It is the
seventh such round and the first authored _after_ the gate's own generator was fixed, so
its banner — not its original finding counts — is what to read. `codec-gate-denominators`
closed 41/41 on 2026-11-08 and is archived; it rewrote three of the four
`codec/axiom-gate` requirements round nine modifies, which is why round nine needed a
re-evaluation pass rather than a straight implementation. The two **PARKED** `basen`
changes remain deferred until the library division is decided. Everything else in this
list is archived history.

- `codec-gate-denominators` — **archived** 2026-11-08 as
  `openspec/changes/archive/2026-11-08-codec-gate-denominators/` (41/41, synced
  `+10 / -0`, 32 → 42 scenarios, none dropped). It installs the **arm obligation**: every
  diagnostic arm reports its _denominator_ and its _removals decomposed by cause_, both
  **asserted**, not logged. Three arms came into compliance (def classifier per-pattern
  decomposition, footprint `skipped` split into three causes, the pattern audit reading
  one rule), and `isBareProj` was hoisted from two `let rec` copies into **one** definition
  and fixed — it now separates a projection of a _hypothesis_ from an application of a
  proved _theorem_ by the head constant's own body, not by head-and-arity. Five captures
  moved out of the gated set (`CandAligned_fst`/`_at`, `packedCands_mem`, both
  `Iso.*_eq_some_of_*`); `roundtrip`, `findFrom_finds` and `CandAligned_tail` stay gated.
  Its `tasks.md` §1 has the measured log lines, §5.5 records the regeneration diff that
  caught a comment sitting inside a generated region, and **0.4a is a violation report**,
  not a completed task — read it before trusting a 41/41.

- `codec-audit-round-eight` — **archived** 2026-11-07 as
  `openspec/changes/archive/2026-11-07-codec-audit-round-eight/` (22/22). The eighth
  review round produced 9 MUST / 15 SHOULD / 18 NITPICK; five were fixed in the landing
  session and **two refuted** (R8-01's `filter ||` and M-2's `86→106`). What the change
  landed is four counts that were previously silent — the `constantKindCensus` arm, the
  `propProjections` **validity** arm, the footprint **denominator** (`769 scanned /
144 mentioning / 154 found / 146 checked / 8 left`), and the fix for a **mirror list**
  in `scripts/gen-axioms.lean` that had been un-pinning `Codec.Suffix.hle` while
  `headerNumbers` read the mirror's own count. Read its archived `tasks.md` as history.
  Its §6 records the paper/numbers SHOULDs it fixed and the ones it **refuted** (S-6's
  suffix-vs-component, N-7's "15 jobs" — `lake build` really does print that).

- `basen-uppercase-prepass` — **in-progress, PARKED**, 0/20. Replaces `Base16`'s
  24-theorem case-folding tier with an `upperBytes` pre-pass through
  `Codec/Normal.lean`, corrects the RFC `MAY`-vs-`MUST` misquote that justified the
  tier, and **excludes base64** because its lowercase letters are data. Three ADDED
  `basen` requirements; disjoint from `basen-nat-iso`'s, so neither can drop the
  other's scenarios.

- `basen-nat-iso` — **in-progress, PARKED and BLOCKED**, 0/18. Its premise is under
  review: `basen` is "base-N byte encodings" and a numeral is not one, so it may
  belong in a new repo. Read its §0 before anything else. The analysis inside is sound
  (a number is isomorphic to its canonical numeral, lax spellings are names not
  images) and will be reused wherever it lands; what is unsettled is the home.

- `codec-audit-round-six` — **archived** 2026-11-07 as
  `openspec/changes/archive/2026-11-07-codec-audit-round-six/` (32/32 tasks, both
  gates green). Authored 2026-11-07 from the seventh review round (three read-only
  workers; reports `/tmp/r7/{A,B,C}.md`, merged ledger `/tmp/r7-SYNTHESIS.md`).
  33 findings (`R7-nn`): 5 MUST / 12 SHOULD / 16 NITPICK, plus **10 refuted**, and
  **two more refuted while fixing them** (its §9 now records both). Read its archived
  `tasks.md` as history; do not reopen it. Four things worth carrying forward:
  - **Zero soundness defects.** 502-constant sweep: no `Classical.choice`, no
    `sorry`. Every MUST was a false claim _about_ the mathematics.
  - **§1 found 26 footprint claims, not the 11 reported** — an environment walk
    catches what a per-family `#print` sweep misses. The gate now **prints** the
    count, which is how the next finding below was possible: round seven widened the
    arm's enumeration predicate (`getPrefix` → `isPrefixOf`) and its attribution rule,
    after which the printed count went **9 → 145** and seven further mis-claims fell
    out (`codec-audit-round-seven` GC-01). The lesson: an arm that reports no count
    cannot be told from an arm that reads nothing.
  - **§6.6's port reproduced §1's trap.** `basen`'s new footprint arm was green on
    **6 of 52** claim sites until the attribution rule was fixed (a claim that names
    a _different_ declaration right beside it was being dropped). It then found two
    real under-strong claims. **Mutating a new check is not optional.**
  - **Two reviewer figures refuted** (`[S1]`'s "should be 21": the walk returns 19,
    only the decomposition was wrong; R7-14's "both CHANGELOG SHAs resolve nowhere":
    both resolve in `basen` and are ancestors of HEAD) — and a third refuted during
    §2.3 (the suggested `nativeDecideCount` fix left block comments uncounted; a
    naive total read 18 against a true 12).
- `codec-audit-round-five` — **archived** 2026-11-07 as
  `openspec/changes/archive/2026-11-07-codec-audit-round-five/` (46/46 tasks, all
  three repos gated). Authored 2026-11-07 from the sixth
  adversarial review round (three read-only workers; reports `/tmp/r6/{A,B,C}.md`,
  merged ledger `/tmp/r6-SYNTHESIS.md`). 38 findings: 7 MUST / 15 SHOULD / 16 NITPICK,
  plus **26 refuted** — a third of what the reviewers set out to falsify turned out
  sound, and those are recorded in its §9 so they are not re-derived. The proof it
  needed was inlined in its Appendix A and verified to compile, so no `/tmp`
  dependency remains. Do not reopen it; read its archived `tasks.md` as history.
- `codec-audit-round-four` — **archived** 2026-11-07 as
  `openspec/changes/archive/2026-11-07-codec-audit-round-four/` (52/52 tasks). 37
  findings (`R5-nn`): §1 refuted `LengthDet → RelAligned` and proved the four-way
  independence diagram, §2–§3 landed three advertised-but-absent laws, §5–§6 corrected
  the necessity/uniqueness docstrings and ported the def-coverage gate to `basen`.
  Do not reopen it; read its archived `tasks.md` as history.
- `codec-audit-round-three` — **archived** 2026-11-06 as
  `openspec/changes/archive/2026-11-06-codec-audit-round-three/` (56/56 tasks). It
  came from the third audit (three read-only reviewers; reports in `/tmp/r3-*.md`):
  §1 made law coverage structural, §2 fixed prose. The pre-archive scenario diff found
  **no live scenario dropped** (every MODIFIED requirement was a strict superset or
  identical) and `codec/law-coverage` was created with its `## Purpose` carried
  across. Do not reopen it; read its archived `tasks.md` as history.
- A **round-four audit** (three read-only reviewers, 2026-11-05; `/tmp/r4-*.md`) ran
  on top of that and its findings are **applied and pushed** — see the archived
  ledger's "Round-four audit" section in
  `openspec/changes/archive/2026-11-06-codec-audit-round-three/tasks.md` for what was
  fixed, what was refuted, and what is open.
  Its two structural additions are worth knowing before touching a gate: both
  `Axioms.lean` headers are now **asserted** by a `headerNumbers` `run_cmd` (a stale
  count is a build failure), and the template finally enforces `warningAsError`.
  Round three then went further: codec's `Axioms.lean` gained a **third** check
  (definition coverage, §1.8) and its footprint _distribution_ table became
  **generated** by `scripts/gen-axioms.lean` (§1.9) — so in codec the counts are
  asserted and the distribution is emitted, and the two must not be confused when
  updating the header.
- `codec-audit-round-two` — **archived** 2026-11-05 as
  `openspec/changes/archive/2026-11-05-codec-audit-round-two/` (42/42 tasks, all
  gates green, three spec deltas synced and verified). Do not reopen it; read its
  archived `tasks.md` as history.

### How `lean-basen` closed (history — the archived ledger has the detail)

§6.1 (proof gate), §6.2 (base64 `Zh==`/`Zm9=` whole-input rejection) and §6.3b
(base32 `MZ======`) all landed and gated, and the two post-audit items closed:
**§6.4** closed the gate's coverage of the then-current theorem set (91/404 ->
all of it; the count has moved since — read `../lean-basen/Axioms.lean`'s header,
not this file), and **§6.5** removed
every `set_option linter.… false` rather than deferring it. **§6.10** closed:
the ecosystem is on Lean 4.35.0. The `lean-toolchain` pins
now match what builds (`v4.35.0`), the lockfiles are nixpkgs `1d06008`
(2026-11-03), and `basen`'s `codec` pin was bumped in the same change — **read `basen`'s `flake.lock`, never a SHA here**. The bump cost **one line**
in `Codec/Packed.lean` — `basen` needed no source changes — because the
toolchain itself was a cache substitution. Two traps from that bump:

- **A single law was toolchain-dependent, and is now simply shorter.**
  `Codec/Packed.lean`'s `decodeFullArraySearch_cons`: 4.35.0 closes the goal at
  the `conv`+`rw` that 4.34.1 left open, so the old `simp only`/`split`/
  `injection` tail became dead. The provenance is worth knowing because the
  naive fixes were _wrong_: plain deletion is green on 4.35.0 but **red on
  4.34.1**, and `try`-wrapping fails the other way. While both toolchains were
  supported it carried a `first | (tail) | skip` guard; now that the ecosystem
  is pinned to 4.35.0 the guard is gone and the proof is **one line**. Verified
  non-vacuous by mutating an arm of the statement (it then fails with
  `unsolved goals`) — do that check whenever a proof collapses to one tactic.
- **A `lake build` segfault after a bump means stale build state.** Right after
  the bump, `lake build bench` aborted with `unsupported IRType` (exit 139);
  `rm -rf .lake` and the same command is green. So before diagnosing a crash as
  a toolchain or lakefile problem, clean the build dir.

**The one scoping lesson worth keeping, because it cost sessions.** §6.2 was for
a month recorded as "repeatedly blocked on `Suffix`/`splice` index bookkeeping
in the `blocks = []` branch" — and that was **wrong**. Measured: for the 4-byte
`Zh==` input, `decodeRepeat b64BlockElem …` yields **one** decomposition,
`blocks = []`, `t.remaining = 4`, because a base64 full block consumes exactly 4
bytes and a 4-byte input cannot populate `blocks` at all. There was no `cons`
branch to kill and no `splice` work; the `ZgAAAA`-shaped difficulty belonged to
that 8-byte input. The landed proof keeps a two-line `omega` for the `cons`
branch anyway — it must not depend on a `#eval` about one literal — and it
closed in one session.

### Where the work is going (a pointer, not a ledger)

The roadmap **lives in `openspec/`**. Five audit rounds have landed and each one found
a different layer, which is worth holding in mind because each next round confirms the
pattern: round one the gate's _existence_, round two the gate's _mechanism_, round three
the gate's _universe_ (theorems, not definitions), round four the universe's
_completeness_ (definitions, and one refuted predicate claim), round five the
universe's **filter** — the classifier that decides what enters it had no audit, so it
was silently removing `Iso.prod` from the check.

The lesson that generalises: **a gate is only as strong as its narrowest unaudited
step.** Every round so far has closed the step the previous round's fix introduced. When
you add a check, ask what removes things from _its_ input, and whether that removal is
recorded.

The next **format port** (another `lean-*` repo) is still an owner decision; this
file does not guess it. When one is chosen, author it as a new change under
`openspec/changes/` — the archived `lean-basen` ledger is the model for shape, not
a template to resume.

### Traps that have actually cost sessions here

- **A name-based classifier is the gate's weakest step, and it fails _silently by
  construction_.** `isDerivedDefName` drops a `def` by its last name component; the name
  then leaves the universe, so the coverage check cannot report it — a dropped `def` and
  a `def` that was never written are indistinguishable to the check. Round six measured
  it already dropping `Iso.prod`, the paper's own `×`, out of a green gate. The theorem
  side solved this with `partition` (every dropped name needs a reasoned allowlist
  entry); the def side had nothing until `round-five` §1 added
  `derivedDefDeclinationAudit` + `derivedDefPatternAudit`.

  **The question is now a build precondition, not a thing to remember.** "What removes
  things from this check's input, and is that removal recorded?" used to be advice a
  reviewer had to recall; since `codec-gate-denominators` it is the rule every arm is
  written against and every arm is checked by — see **"Adding a gate arm"** below. Read
  that section before writing a `run_cmd`; read this bullet for why it exists.

  **The trap is the pattern, not any one instance** — it fired **fourteen** times across
  rounds five to ten: a name list, a prefix filter, a `(…).length` sink, an attribution
  rule, an un-decomposed `skipped`, a predicate matching `Expr.proj` where Lean emits
  `And.left`, two copies of one predicate, and a guard testing the wrong variable. The
  full tabulation is in `openspec/changes/codec-gate-denominators/proposal.md`; read it
  before concluding a check is sound. The four instances `codec-gate-denominators` itself
  closed are in that change's `tasks.md` §1 and §3.

- **A `Prop`-valued structure field is not a law.** `Iso.law`, `Normal.fixed`,
  `Normalizer.idem` are projections (`fun … => self.1`), and gating them measures the
  structure's shape. `round-five` §2.2 moved all three into the allowlist group whose
  reason already covered them (`propProjections`), because the file had been gating
  three of the six and allowlisting the other three. The same file allowlists
  `MeasureDecreases.dec` and friends for
  exactly that reason, so the taxonomy has to be applied uniformly — if you find one
  field gated and its twin allowlisted, that is a defect, not a judgement call.

- **`#print axioms` reporting _no axioms_ does not mean "restatement".** It is neither
  necessary nor sufficient: `decodeWholeOneBytes_eq` _is_ an identity and reports
  `[propext, Quot.sound]`, while the three Layer-2 `*_spec`s report no axioms and are
  load-bearing referents for the C contract. To test for a restatement, `#print` the
  body. (Round six deleted the diagnostic that claimed otherwise.)

- **A completeness claim must come from an environment walk, never `grep '^def'`.**
  `grep` misses multi-line signatures (`Iso.prod`, `Iso.ofTotal`) and cannot see through
  an alias, and the sentence built on it then reads as an enumeration it is not. Two of
  round six's MUSTs are exactly this (`[S1]`'s "exactly two others", `[S3]`'s "every
  `Codec` value is one of these fifteen").

- **Never subtract two committed performance figures from different sessions.** This
  project has recorded **three** successive defects of that shape. `README` derived
  "~25 ns/step" from `52.4 − 27.4` where `52.4` appeared nowhere else in the document
  and the adjacent table gave 26.4/23.6 — three bullets below a sentence forbidding
  precisely that subtraction. Quote the table, name the run.

- **`Suffix`/`splice` bookkeeping is _not_ where §6.2 died — check the input
  length before reaching for it.** The old version of this bullet asserted six
  sessions were lost to `splice` in the `blocks = []` branch. Measured
  2026-11-05, that branch is **trivial** for the actual 4-byte `Zh==` input
  (`decodeRepeat` returns exactly one decomposition, `blocks = []`), because a
  full base64 block is 4 bytes. Reach for `Suffix`/`splice` API reading only if
  a `#eval` of the decomposition shows a non-empty `blocks`; do not assume it.
- **`decodeFull` is not `decodeFullB64`.** The fixed-width bases use the `Run`
  combinator (unfolds with `WellFounded.fix_eq` + `decodeFullStep.eq_def` +
  `simp`); the padded bases use a `filterMap` composition that same recipe gets
  **stuck** on. Use `cases h : decodeFullB64 s` + `decodeFullB64_some` instead —
  the library never unfolds that recursion, and none of its own rejection
  theorems do either.
- **A §3.5 pad-bit rejection is a `decide`, not an induction** — but the recipe
  does **not** transfer verbatim between bases. For base32,
  `b32BlockDecodeLenient` matches an **8-binder** list, and both `split` (its
  internal simp) and `simp_all` blow the simp step limit; `unfold … ; decide` on
  the whole closed goal is what works. Base64's 4-binder version does close with
  `split` + `decide`. See §6.3b's note in the ledger.
- **A base32 twin transfers the proof _shape_, never the constants.** Base64's
  `Zh==` needs `b64BlockUnapply [0x66] = some Zg==`; base32's `MZ======` needs
  `MY======`, because the two bases pad at different widths. Re-`#eval` every
  literal before writing the proof — `decide` will catch it, but only if you let
  it.
- **`../lean-basen` pins `codec` through `flake.lock`.** If it predates something
  this repo added, the fix is a targeted `nix flake update codec` + `lake update
codec` — a `bad import` means a stale pin, never a wrong import.
- **`huniq` is a hypothesis by design for any codec other than `Codec.byte`**
  (`Codec.huniq_not_derivable` machine-checks that it does not follow from
  unambiguity + productivity). Do not reopen it as unfinished work.

### Traps specific to the current ledger (round three)

These cost time _this_ session and are the ones §1/§2 will run into. Read them
before starting §1.

- **The `Classical.choice` leak in §1.2 is the trap to carry into §1.5+ — carry a
  `Nat` equation into an induction and a proof _compiles clean and leaks_.**
  Proving `Rel (count k p) xs s ↔ xs.length = k ∧ …` by induction on `k` with
  `xs.length = k` in context makes every `cases xs` a dependent match; the result is
  `[propext, Classical.choice, Quot.sound]` with **no compiler error**, only
  `#print axioms` shows it. Bisected: every ingredient was `[propext]`-only alone and
  the leak appeared only when the recursive call carried the equation. **The fix:
  recurse on the _list_ and let the length be `xs.length` derived from the term**
  (`relRepeatToCount`). Applies to every `count`/length-shaped law still to come.
- **Never let `simp`/`simpa` discharge a dependent `Fin`/`Array`/`List` index bound —
  it leaks `Classical.choice`.** Proven this round: the same pointwise transport of
  `arrayToBytes (bytesToArray s)` is `[propext, Classical.choice, Quot.sound]` with
  `by simpa using hi` and `[propext, Quot.sound]` with the bound written as
  `Nat.lt_of_lt_of_eq i.isLt (bytesToArray_size s)`. It compiles clean either way, so
  only `#print axioms` catches it. Also: `Array.getElem_mk` and
  `Array.getElem_eq_getElem_toList` **do not exist** in 4.35.0 — the bridge is
  `Array.getElem_toList` then `List.getElem_ofFn`.
- **A rewrite under a dependent `decode d h (size) (cast …)` argument is not a `rw`,
  a `subst` or a `generalize`.** All three fail (motive-does-not-typecheck /
  dependent-elimination / occurrence-not-captured). Prove a helper with **abstract**
  arguments instead — `(k : Nat) (hk : k = n) (a : Bytes k) (ha : a = cast …
hk.symm s)` — and `subst hk; subst ha`.
- **A `simp only` set that does not fire leaves `sorryAx`, not an error.** For
  `seqRight`'s composite `Iso`, `Option.some.injEq` does not match the
  `(some (y,u)).bind … = some x` shape, and an attempt that dropped the `simp`
  entirely still compiled. `injection … with h; subst h` is what closes it.
  `seqLeft`'s shape _is_ `simp`-dischargeable, so the recipe does not transfer
  between the two halves of the same family. Always `#print axioms` a new law family.
- **`unfold <def>` does not reduce a `match`-`def` at a variable argument.**
  `count` (matches on `n`) and `relRepeat` (matches on the list) both stay opaque, so
  `Rel_iso`/`Rel_seq`/`relRepeat_cons` cannot fire. State the recursion equation as
  its own `rfl` lemma (`count_succ`) or `cases` on the matched argument first.
- **A gate whose _prose_ quotes counts needs the counts asserted, or the prose rots
  while the gate stays green.** Both `Axioms.lean` files had a header table that was
  stale by a full regeneration (`292` vs `310` in codec; `446 / 437 / 9` vs
  `483 / 437 / 46` in basen — the `9` was a genuine authoring error, not drift),
  because `partition`/`gateCoverage` compare set _membership_ and never read prose.
  Both files now carry a `headerNumbers` `run_cmd` asserting the table's numbers and
  their sum. **When you regenerate, the header check fires — update the table and the
  `expected*` constants together.** Do not weaken it to a `logInfo`.

  **Several sets of "basen's numbers" have floated around the ecosystem; only the
  gate is current — do not grep for them, read the gate output.** The history above is
  `446 / 437 / 9`; round four found the prose paragraph still saying `440 / 437 / 483`
  and **fixed it by computing it** — `headerNumbers` now derives the `BaseN` pin count,
  asserts the three `Codec.*` pin names exist, and asserts the total, so the paragraph
  cannot rot behind a green table again. As of `round-six`'s archive the gate prints
  `490 = 444 + 46` theorems with `447 = 444 BaseN + 3 Codec` pins, `137 = 122 + 15`
  defs, and a footprint distribution of `381 + 48 + 15 = 444` that is itself
  asserted (it had rotted to `377 / 48 / 15 = 440` behind a green table).
  **Quote the gate, never a number written in a file.**

- **The gate catches your own new laws, by design — regenerate, do not investigate.**
  Every law added in §1 fails `lake build` with `not pinned by this gate` until
  `scripts/gen-axioms.lean` is run. That is §1.1 doing its job, not a regression.
- **A `def` with no law used to be invisible to every gate — §1.8 closed that, but
  only as a _mention proxy_.** `Axioms.lean`'s theorem partition is `thmInfo` only,
  so a public `def` was in neither `gatedNames` nor `generatedAuxAllowlist` — not
  "un-gated", _outside the partition_ — which is why `btake`, `maybe`, `manyUpTo`,
  `seqRight`, `seqLeft`, `between` shipped with zero theorems while the gate was
  green. There is now a third `run_cmd` requiring every public `def` to be mentioned
  by some gated theorem's **type** or listed in `definitionSurfaceAllowlist` with a
  reason, and the header asserts the counts (`140 = 111 + 29`). Read it as the proxy
  it is: it cannot be satisfied by _silence_, and it **can** be satisfied vacuously.
  When you add a `def`, still grep for a theorem mentioning it before believing the
  law is worth having.
- **"Free theorem" claims used to live in `Codec/Combinators.lean` and were false at a
  variable `n`; §1.7 rewrote them.** The docstring claimed the derived combinators'
  characterizations were definitional consequences and that
  `decode_spec`/`bidir`/`roundtrip` "hold unconditionally via `Codec.Sound`". Those
  three are **structural inductions on the `Codec` value** and `count n p` is
  `iso` of `seq p (count (n-1) p)`, so the case cannot close — no such law exists for
  any of the eight derived values, and that is a fact about the derivation's shape,
  not a backlog item. Do not reintroduce the claim.
- **`List.ofFn` equality is not `rfl` across two different functions.** In the
  base32 §3.5 work, `List.ofFn sb₁ = List.ofFn s₀` needed `congr 1; funext i;
exact hsb_eq i.1 i.2`. `cases`/`decide` on the whole goal also works when the
  inputs are literals.
- **`Iso` projections of structure fields defeat `unfold`/`split`.** A structure
  literal's `.apply` does not reduce under `split`; use
  `simp only [<the def>] at h` to expose it first. This is why the `Unambiguous`
  counterexample proofs use `simp only [uniqSeqBo, uniqSeqBt, Rel_alt, Rel_pure,
Rel_iso] at hx hy` rather than unfolding.
- **A `have := …` whose name collides with a definition shadows it.** `have := h …`
  named it `this`; naming it `RelAligned` or `hcon` collided. Use a name that is
  not a declaration.
- **Do not trust a reviewer's arithmetic without re-deriving it.** Round three
  reported `Axioms.lean`'s footprint table as wrong (197 vs 195); re-derived it was
  correct — their parser truncated at the `?` in `attach_getElem?_corr`. Design D1
  records this. A refuted finding is a result; relaying it unverified is the defect.
- **`native_decide` is banned for laws and does not appear anywhere in this repo.**
  Measured at `codec-gate-denominators`:
  `grep -c native_decide Bench.lean` → **0**, `grep -c native_decide Axioms.lean` → **1**
  (the prose line announcing the ban at `Axioms.lean:12`), and `grep -rln` over `*.lean`
  returns **`Axioms.lean` only**. So the token exists in exactly one file and in exactly
  zero proofs — `Bench.lean`'s checks are `example`s closed by `rfl`. An earlier revision
  of this bullet said it was "fine in the bench" and "appears only in `Bench.lean`", both
  false; `codec-audit-round-eight` corrected them, and this change re-measured rather than
  trusting that correction. Never introduce it into `Codec/`.

  (`codec-gate-denominators` task 4.4 was authored believing this bullet still said the
  token appears in `Bench.lean`. It did not — the correction had already landed. The
  measurement above is recorded so the next reader does not have to re-derive whether the
  task or the file was stale: **the task was**, and it is answered rather than closed
  unexamined.)

### Rules about this file

- **Direction lives in exactly two places: this file and `openspec/`.** No
  `HANDOFF.md`, no `NOTES.md`, no scratch tree. `openspec/lean-notes.md` is
  _lessons, not direction_ (the project half of the global `lean` skill); if an
  entry there reads like a task list, move it to the ledger.
- **History is not direction.** What landed, when, and what was measured belongs
  in the change's `tasks.md` and `CHANGELOG.md` — including archived changes,
  whose own `tasks.md` under `openspec/changes/archive/` is the reference. Do not
  re-teach landed work here.
- **Archive hazard.** A MODIFIED block **replaces** the live requirement wholesale,
  so any live scenario the delta does not restate is dropped at sync time. Two
  changes modifying the same requirement must archive dependency-first, with the
  order recorded in the later change's `tasks.md`. This has already fired twice:
  `lean-basen` / "The `basen` bases are `Codec` values", and
  `codec-audit-round-two` / `codec-audit-round-three` both rewriting
  `codec/axiom-gate`'s partition requirement. **Check the live spec's scenario
  count against the delta's before syncing** — `openspec validate` will not always
  catch a narrowed set, and round three authored its delta against the pre-sync
  text.

### Ecosystem shape (stable, not status)

Each verified format/protocol is its own git repo, initialized from
`lean-nix-flake-template`, prefix-dropped internally (`lean-basen` → `basen`/
`BaseN`; `lean-vbin` → `vbin`; …), depending on `codec` **by flake input +
`require codec from git` injection — never vendored**, and inheriting the
single-`Bytes n`-substrate and `[propext, Quot.sound]`-only discipline.

**Toolchain: all four Lean 4 repos are on 4.35.0** (2026-11-05):
`lean-codec`, `lean-basen`, `lean-nix-flake-template` and `../workflow` each pin
`lean-toolchain` `v4.35.0` and nixpkgs `1d06008`. Keep them in step —
`lean-basen` fetches `codec` by rev, so a `codec` bump means
`nix flake update codec` + `lake update codec` there.

**`../workflow` was the one exception and no longer is.** It used to pin a
`cauli/lean4` fork (`62b6a229`) with "Do NOT move this pin", because it was
compiling the kernel to WASM and needed emitted C to match a prebuilt link kit.
**That WASM path never worked and was removed 2026-11-05** — the link-kit
archives are `-m32` cross-compiled while the emitted `Kernel.c` is not (OOB crash
inside `l_Lean_Json_parse`), and rebuilding Lean to wasm32 to match hit an
`emscripten`/`lld-22` wall. The fork input and both packages that served it are
gone; it now uses nixpkgs `lean4` like everything else. **Do not reintroduce a
fork pin** without evidence the link kit is regenerated at a matching sha.

Two traps from the 4.35.0 bump: `lean-toolchain` is **inert** in these repos
(nothing reads it — check `lake build -v`), and a `lake build` segfault right
after a bump means stale `.lake` artifacts, so `rm -rf .lake` before diagnosing.

In `../lean-basen`, `codec` is a flake input threaded into `default.nix`, which
rewrites `require codec from git …` → a local `require codec from "./codec-src"`
path dependency, so the sandboxed `lake build` needs no network. (`lean-codec` is
public, so the `github:` input fetches anonymously — no token, no `--impure`.)

## Adding a gate arm

**Read this before you write a `run_cmd` in `Axioms.lean`.** Ten review rounds produced
zero soundness defects and **fourteen** instances of one defect class: _a check whose
input has a filter that nothing audits_. Each was fixed individually; the class survived
because no rule governed how a new arm is written. `codec-gate-denominators` makes this
the rule.

Every diagnostic arm **SHALL** report two quantities:

1. **denominator** — the universe its claim is about, and
2. **removals** — what it took out of that universe, **decomposed by cause**.

Both **SHALL be asserted** (`throwError` / an `expected*` constant), not merely `logInfo`'d.
A printed number rots silently; an asserted one fails the build. If a number must stay
printed-only, say so wherever the gate enumerates its own numbers.

**Why decomposed and not just counted.** Instance 14 was `skipped = 8`: the denominator
was present (`146 + 8 = 154`), but one total summed a survey paragraph with a claim that
had **no resolvable owner** — and the two claims carrying `decodeFull_spec`'s hypothesis
chain were in the second bucket. A single total cannot show that.

**Mutation-test the new assert before you commit.** Narrow the walk, widen a filter, or
add a name to the list you are guarding, and confirm the build fails _naming it_. A new
check that has not been mutated is not a check.

**And when you enumerate call sites, declarations or claim sites in prose — in a task, a
comment, or a docstring — get the count from a command and quote its output.** A short
list is a completeness claim that fails silently. Round nine's own enumeration of
`benchBurst` call sites was short by two.

### The third number: a vocabulary is a filter too

**A matcher's vocabulary is an input filter, and it SHALL be audited like any other.**
`codec-gate-denominators` installed the two-number rule for _filters_; round nine's
task 5.3a found the case it does not cover.

`CodecAxioms.footprintClaimPhrases` decides which docstring segments are footprint claims.
It recognised `` `[propext, Quot.sound]`-only `` but **not** `` `[propext, Quot.sound]` ``
without the suffix — so `Codec.blitBytes_spec`'s claim never became a claim site **at all**.
It was not checked, not skipped, and not out of scope: it did not exist. Measured, that
hole is **22 of 159** `thmInfo` docstrings containing a backticked axiom-list literal, and
the blind set includes `Codec.Bytes.ext_iff` and `Codec.findByte_spec` — both believed
audited.

So an arm whose input is selected by **matching against a list of spellings, patterns or
prefixes** SHALL report a **third** quantity:

3. **the denominator of the matcher itself** — how many items match a deliberately
   _broader_, independently-written predicate (for the footprint arm: "contains a
   backticked axiom-list literal"), against which the recognised count is reconciled.

The broader predicate must not be defined in terms of the list it audits, or the check
answers itself. Two counts that reconcile are the only evidence the vocabulary is
**complete** rather than merely **un-narrowed** — a list can be audited against shrinkage
and still be far too short, which is exactly what happened here for a whole round.

Mutation-test this too: delete one spelling and confirm the reconciliation fails naming it.

## Verification recipe

Every command below names **its own repository**. They are different flakes with
different `checks` sets — never run one tree's recipe in the other.

### In `lean-codec` (this repo)

```bash
nix develop --command lake build            # 10 gate lines; FAILS on `sorry`
nix develop --command lake build bench      # the bench lane (links Codec/ByteSlice.c)
nix develop --command openspec validate --all   # after ANY spec or task edit
nix build .#checks.aarch64-darwin.formatting   # THE markdown/nix format gate
```

**`nix fmt` is not the format gate here — `checks.…formatting` is.** `nix fmt` in this
dev shell has no `prettier`, so it formats `*.nix` only and prints "0 changed" for
markdown it never touched; every "`nix fmt` clean" in this file's history and in the
archives covered Lean and Nix and **not markdown**. Use the flake formatter, which is
treefmt with the sandboxed prettier: it **caches per tree** (pass `--clear-cache`
after an out-of-band edit) and it reads the **git tree**, so an uncommitted fix cannot
turn it green. `codec-audit-round-eight` lost a build cycle to this and found a
pre-existing red with it (`185eebd`).

`openspec` above needs **this** repo's `openspec/` root; `nix flake check` is
likewise a **per-repo** command (this flake's `checks` are
`formatting`/`lean`/`openspec`, which `../lean-basen` does not have) — never
"run it once for the ecosystem".

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
nix develop --command lake build bench   # the bench lane (fast dev loop)
nix build '.#bench'                      # same lane, sandboxed — BUILDS AND RUNS it
```

`packages.bench` exists and is a **package, not a `checks` entry**: the lane
value-checks known vectors, which is evidence, not proof, so it must not be able
to fail the proof gate. **The checks fire at BUILD time** — every `Bench.lean` check
is an `example` closed by `rfl` or `native_decide`, and `main` is `pure ()` — so
`nix build '.#bench'` proves the lane **builds and links in the sandbox**, not that a
runtime check passed. Its `installPhase` runs the binary only as a smoke test that it
starts and exits 0. An earlier revision said the `installPhase` "verifies the vectors";
that is the sentence `basen`'s `default.nix` records as false of the code
(`codec-audit-round-six` R7-16), and `codec` had not been corrected
(`codec-audit-round-seven` N-06).
Do not add it to `checks`, and do not treat a green `lake build bench` as having
verified anything — that only compiles.

`Axioms.lean` is a `@[default_target]` lib, so `lake build` runs its `#guard_msgs`
gates; a `Classical.choice` regression fails the build. To check one law by hand:

```bash
printf 'import BaseN\n#print axioms BaseN.Base64.decodeFullB64_reject_arity\n' > /tmp/c.lean
nix develop --command lake env lean /tmp/c.lean    # expect [propext, Quot.sound]
```

**Since §1.0 it also has a _mechanism_, not just blocks.** `lake build` now prints
**six** lines and fails if any disagrees with the environment (the fifth, the
`native_decide` count, was added by `codec-audit-round-five` §4.3; the sixth, stated
footprints, by `codec-audit-round-six` §6.6):

```
info: basen axiom gate: 444 pinned + 46 allowlisted = 490 of 490 public theorems (0 explicit exclusion(s))
info: basen axiom gate: 490 public theorems partitioned, 444 pinned and 46 allowlisted
info: basen axiom gate: header numbers verified (490 = 444 + 46); prose paragraph says 447 pins = 444 BaseN + 3 Codec
info: basen axiom gate: 137 public definitions covered, 122 mentioned and 15 allowlisted (mention proxy)
info: basen axiom gate: native_decide stated count verified (12 uses in Bench.lean, all bench-lane, none in the gate)
info: basen axiom gate: stated footprints verified against the environment (46 claim site(s))
```

So a new `BaseN` law fails the build until it is pinned, and a stale pin fails too.
Two traps, both hit in §1.0: a probe theorem must be **inside** `namespace BaseN.*`
or it is outside the gated universe and the gate stays green; and a `lake build`
that reports `Replayed Axioms` after you edited an imported module is reading a
stale `.olean` — delete `.lake/build/lib/lean/{BaseN/…,Axioms}.olean` before
believing a green result.

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

  **`Codec/`'s directory holds exactly one file that is not part of the library:**
  `Codec/CRef.c`, the bench reference parser. It _does_ parse bytes (and says so in
  its own header), so it is deliberately outside that design rule — it is
  **bench-only**, has **no `@[extern]`**, is **not in the axiom gate**, and is not
  reachable from any `Codec` module. It exists as the honest yardstick for the
  performance claims (`AGENTS.md`, "Speed" below). Do not add a second such file,
  and do not move or delete this one: `lakefile.lean`'s `moreLinkObjs` and the `.c`
  path in `default.nix` both name it.

- **Speed: get as close to C as possible, with no set threshold — and attribute
  the gap to named causes, never to "boxed scalars".** The owner has explicitly
  set **no ratio to hit**; the requirement is to make the per-element loop as fast
  as it can be and to say honestly where it stands.

  **The numbers live in `README.md`'s stamped table, not here** (this file's rule 2:
  one source of truth per concern). Quote them only with that table's vintage stamp,
  and only from the run that produced it.

  **What belongs here is the attribution discipline, and the fact that it has been
  wrong twice.** The named causes are: the per-step `List` that `decodeArray`
  returns; `packedCands`' `attach.map` rebuilding `PackedCand`'s _proof terms_; and
  the accumulator. The `Array` indexed read is cheap enough that the memory floor is
  **not** the problem — that part of the attribution has survived every
  re-measurement. What did not survive:

  - `packedCands` was attributed **91**, then **32**, then **~430 ns/call**, then
    **3 ns/call hot**, and in the compiled burst lane is **86 ns/call at `k = 1`**
    and **106 at `k = 2`**. **The 3 is withdrawn, not qualified**: its sink was
    `(…).length`, a constant, so the call was folded away. The 430 is a _memory_
    figure wearing a compute label (first-touching a 4 KiB array). Treat the
    remaining numbers as one lane each, and never as a sequence that "improved".
  - The "ideal floor" was quoted as **6 ns/step**, then **16**, then **2.4**, then
    **3.0**, and is **~2.5–2.7 warm (latest burst median; the range spans every committed
    floor, 2.46–2.67 — `codec-audit-round-eight` S-2 found this file's `~2.5–2.6` and
    the README's `~2.6–2.7` were two intervals neither of which contained the other's
    end) / ~15–18 cold**. Each step of that sequence was a
    different mistake: the 6 came from a lane that `Array.push`-ed every element
    (floor plus n elements of growth); the 16 is a real number but _cold_; and the
    2.4 was the **minimum of 5 decaying rounds** at an `8n` working set — the most
    favourable endpoint of the wrong variant. `benchBurst` now reports
    min/median/max over one L1-resident buffer, and 3.0 is its median.
  - The `Array` read was quoted as **3**; the README's stamped tables are the
    authority, and they give **~64–67 ns per call** (burst, one read per call) with
    **no** per-step figure — one read per call must not be divided by `n`. An earlier
    revision of this file said "~14–18 (cold, per `n`) / ~78 ns per call", which
    contradicted the README on both numbers and quoted the divided form the README now
    explains is wrong (`codec-audit-round-seven` N-05).

  **A three-reviewer audit (against `PAPER.md`/`README.md`) is on the record.**
  It found the core pure and proved, and "ready to use" **false** for three
  concrete reasons (no total-bijection `Iso` constructor; `ConsumesByte` never
  derived for `seq`/`iso`; no single-value decode entry point) — all three fixed
  in `Iso.ofTotal`, `seqConsumesByte`/`isoConsumesByte`, `decodeWholeOne` — all
  format-agnostic, **none with an in-tree caller**, because `[S3]` means this
  package ships no concrete codec. A `Codec/Examples.lean` (`u8`/`u16le`/`u16be`)
  was written and then **removed**: that is `../lean-basen`'s territory, and adding
  it here was a `[S3]` breach. It also found the remaining hole is `huniq` for
  unequal-length `alt`. **Do not re-audit; continue from the box above.** One reviewer claim was **refuted** on inspection: the
  paper's `iterate` does _not_ trivially satisfy `Iso.law` — substituting its two
  `Just ∘ driver` directions into `apply a = some b ↔ unapply b = some a` gives
  exactly the fixpoint-agreement claim, so `[D7]` is correct as written.

  **Warm and cold are two different questions and the bench now prints both.**
  `benchRatio` interleaves a same-size `memcpy` (right for a ratio to `memcpy`, but
  it evicts the input, so the figure is _cold_); `benchBurst` runs back-to-back
  calls in one window (the input stays hot, and the span clears the ~41 ns clock
  granularity). A **floor** is a compute claim, so quote it from a burst; a
  **throughput** figure comes from the interleaved lane. Never present one as the
  other — that conflation is what made a 2.4 ns/step floor read as 16 and turned an
  ~11× gap into a claimed ~3×.

  **And a burst is a _range_, not a point.** `benchBurst` used to report the
  minimum of its rounds and the rounds are not independent — they differ only in
  cache warm-up, so the minimum is systematically the most favourable one. It now
  prints min/median/max and the round count, over **one** buffer (the working set is
  `n`, not `8n`; the old 8-buffer rotation is still printed as `(burst@8buf)`).
  Quote the **median** and the range, never the min alone. The same rule as the rest
  of this section: the lane is the source, and the lane now prints the spread it
  always had.

  So: **a number is sourced because the lane, run, prints it — not because a lane
  exists.** Three rows were labelled with a lane and still did not match it. When
  you quote a figure here, run the lane in the same session and paste its output.
  This package has had **four distinct performance quantities** wrong at some point,
  across fourteen recorded values: the ideal floor (6 → 15 → 2.4 → 3.0 → 2.46),
  `packedCands` (91 → 32 → 430 → 3 → 75 → 86, the 3 withdrawn outright), the `Array`
  read (3 → 11–18), and the "~11×" gap derived from a cherry-picked burst round. It
  said **eight** until `codec-audit-round-eight` S-5 counted: no reading of the
  parenthetical — 4 quantities, 14 values, 4 explicitly withdrawn — reaches eight, and
  a remembered count is what this file forbids believing elsewhere. **Two were caught
  by the owner asking why two committed figures could not both be true, not by a
  lane** — so an internal inconsistency between two numbers is itself a legitimate
  check, and "it came from a lane" is not sufficient.

  Withdrawn, because no lane ever produced them: the "~1,200–1,290 ns/byte",
  "~8.5× floor", and "20–40× ceiling" figures that used to sit here. **Do not quote a
  "× off C" ratio for a per-element codec measured against `memcpy`** — `memcpy`
  moves a byte; a parser does per-element work, so the comparison is a category error
  and the honest reference is a hand-written C _parser_. **This repo now measures
  one** (`Codec/CRef.c` + `benchCReference`, bench-only, not Layer 2, not in the
  axiom gate), value-checked against `decodeWhole` before it prints. Measured:
  **Lean ≈ 4× the C parser** (28.6 / 27.0 ns/step vs 7.03 / 6.85), so the "10–21×"
  figures are _Lean-relative_ and must never be quoted as "off C" — that was the
  category error this bullet warned about, committed by omission while no C column
  existed. Note also the Lean floor (2.5) is _faster_ than the C reference (6.9):
  C spends most of its time materialising an n-element value array, not parsing.
  Before timing anything here read `tasks.md` 6.1b's MEASUREMENT RULES:
  naive timing reliably produces a wrong number (dead-code elimination reporting
  `0 ns/op`, loop hoisting, cold-start means).

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

- **A `omega` that closes a _disjunction_ goal leaks `Classical.choice`** — this is
  trap shape 2 below arriving in a new dress, and it cost a `basen` proof in round
  six. Proving `hexToNibble N ≤ 15 → (48 ≤ N ∧ N ≤ 57) ∨ (65 ≤ N ∧ N ≤ 70)` by ending
  each branch with `omega` reported `[propext, Classical.choice, Quot.sound]`;
  building the disjunct explicitly (`Or.inl ⟨h2, h1⟩` / `Or.inr ⟨h4, h3⟩`) and letting
  `omega` close only the _contradiction_ branches gave `[propext, Quot.sound]`. A
  `split`-based rewrite **also** leaked, because `split` on a `Nat ≤` condition takes
  the classical decidable instance. `by_cases` itself was fine — the leak is in what
  closes the goal. Always `#print axioms` a new disjunction-shaped law.

- **A `run_cmd` arm's own `if` is a removal step with no allowlist** — the seventh
  review's central finding. `codec`'s stated-footprint arm filtered with
  `nm.getPrefix == \`Codec` (immediate children only) while the six arms beside it
used `` (`Codec).isPrefixOf name ``; that silently removed **139 public
  declarations before the docstring was read**, and hid a live false claim
  (`Codec.Bytes.ext_iff` said `[propext, Quot.sound]`-only, measures `[Quot.sound]`).
  Round five's lesson was "ask what removes things from a check's input"; the clause
  it was missing is **"and check the `run_cmd`'s own filter, not only the library's
  classifier — the arm's `if` is a removal step too."** The arm now prints its
  claim-site count, because **an arm that reports no count cannot be told from an arm
  that reads nothing**.

- **A one-sided attribution rule discards real claims.** The same arm had only
  "a docstring naming a different declaration is not claiming its own", so a law whose
  docstring cites its own ingredients had its claim thrown away. The fix is
  **proximity**: split the segment at the claim marker, take the last backticked
  resolvable name in the _prefix_, and attribute to it; no name means it is self's
  own. Sites went **9 → 145** and six mis-claims fell out. `basen` had the fix (round
  six §6.6) and `codec` did not — **when you fix one arm, port it to its twin.**

- **A `_prop` projection is not a law, and a name list cannot enforce that.** Seven
  public theorems have bodies that are a bare `Expr.proj` (`fun … => self.k`). Six
  were allowlisted; `Codec.Suffix.hle` was **gated as a law** while the prose said
  "all six are classified the same way". `propProjections` is a name list, so the
  only durable fix is a **structural** arm that walks the environment and flags any
  `thmInfo` whose value is a projection — which is what now exists.

- **A pattern list that audits itself is the only one that can fire.** `basen`'s
  `isDerivedDefName` carried six dead entries (`rec`, `brecOn.go`, `mk`, `prod`,
  `sizeOf`, `sizeOf_spec`), including `prod` — the entry `codec` deleted for silently
  dropping `Iso.prod`. The first draft of the audit arm hardcoded its own copy of the
  pattern list, so re-adding `"prod"` left the build green. Make the classifier and
  its audit read **one** list, then mutate: re-add a dead pattern and confirm the
  build fails naming it.

- **`String.trim` does not exist** in this toolchain (`trimAscii` returns a `Slice`),
  `String.join` takes only a `List String` (no separator — use `String.intercalate`),
  `String.Pos.byteIdx` is not projectable, and `ID.run` is `Id.run`. Each of these
  cost a compile cycle in rounds six and seven.

- **A docstring that states a claim in _history_ re-fires the claim.** Writing
  "this used to say `[propext, Quot.sound]`-only" makes the footprint arm read the
  historical phrase as a live claim. Describe the history without reproducing the
  claim spelling ("used to state two different footprints two sentences apart").

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
  theorem** to `sorry`, get the build green, and iterate on a scratch file **inside the
  repo** (see "Scratch work lives in the repo" below) against the built library. Commit
  per law-family so a revert is never tempting — and see "Commit early, commit often"
  below, which makes that a mandate rather than advice.

## Scratch work lives in the repo, never in `/tmp` (MANDATORY)

**`/tmp` is not under git history.** Anything written there — a probe, a spike report, a
backup of a green file, a subagent's output — is unversioned, unreviewable, and gone at
the next reboot or cleanup. Work has been lost here by treating `/tmp` as a workspace,
and a snapshot in `/tmp` is not a recovery plan: it is a copy with no history, no author,
and no diff.

**Do not do working work in `/tmp`.** Concretely:

- **Scratch Lean files that import the library go in `scratch/` in the repo**, which is
  gitignored (so they never enter a commit, the flake snapshot, or the format gate). Use
  `scratch/probe.lean`, `scratch/mwe-<topic>.lean`; reference them as `scratch/…` in
  notes. `/tmp` is acceptable **only** for a file that is never part of the record and is
  reproduced by a command in the same session — and even then, if what it produced is
  evidence, paste the evidence into `tasks.md`, not a path to it.
- **A report worth keeping goes in `openspec/`** (a change's `design.md`, `tasks.md`, or
  `openspec/lean-notes.md` for a lesson). A reviewer's or worker's report that only lives
  in `/tmp/r7/A.md` is a citation to a file that will not exist for the next reader.
  Quote the finding in place; do not link to `/tmp`.
- **Never back a file up to `/tmp` and call it a safety net.** The safety net is a
  **commit**: work committed per law-family is recoverable, diffable, and reviewable, and
  `git checkout`/`git stash` then has nothing to destroy. If a file is in a state worth
  preserving, `git add <file> && git commit` — not `cp` to `/tmp`.

Scratch files still must not be `sorry`-carrying modules under `Codec/`: anything that
imports into the library's build is a law, and a law needs a proof. `scratch/` is for
probes that `import` the built library, never for modules the library imports.

## Commit early, commit often (MANDATORY)

**A long-running edit must never live only in the working tree.** The commit is the
recovery mechanism; everything else is a hope. This is a mandate, not a preference,
because it has already cost a session: work was lost to a `git checkout` that a commit
would have made harmless.

**Commit at every one of these boundaries**, even when the next step is obviously the
surrounding task:

- **per task section** (`§1`, `§2`, …) once its gate is green — not once per change;
- **per gate arm** when a change adds or reworks several (they are independently
  reviewable and independently revertable);
- **before any command that can rewrite the working tree** — `git checkout`,
  `git restore`, a regeneration script, a mass reformat. Those are exactly the moments
  where uncommitted work is at risk, so commit _first_, then run it;
- **before switching approach**, so an abandoned direction is still recoverable.

The commit message says **what landed and what it was measured against** (the gate line
that went green, the mutation that failed), because that is what makes the commit useful
when bisecting later. A commit per task section with a real message is also what makes
`git log` a readable ledger of a change's progress — which is the point of committing at
all rather than one squash at the end.

This does **not** license `git add -A`: stage individual files and print the staged set
(see "Git conventions"). Committing often and committing narrowly are the same
discipline, not competing ones.

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
- New files matter to Nix: `src = ./.` snapshots only **git-tracked** files _through
  the flake_, so an untracked `Codec/*.c` breaks the sandboxed bench build from a clean
  clone. A bare `nix-build` / `import ./default.nix` takes the whole directory,
  untracked files included — the unqualified sentence was false for that path
  (`codec-audit-round-seven` H-04, the same defect R7-30 fixed in the template).
  (The dev-loop command is `lake build bench`, which links the `.c` from the
  working tree and does not care about `git`. `nix build '.#bench'` exists —
  `flake.nix`'s `packages.bench` — as the sandboxed/CI equivalent, and it is a
  **long** build: `nohup`, never foreground.)

## Skills

- Global Lean theorem-proving skill: `lean4` (official).
- Our supplement (project layout, proving-over-primitives, `partial`/coinduction
  lessons, the `Classical.choice` and `omega`-modulo traps above): global skill
  `lean`. It holds **only the generic half** — keep it that way.
- **`openspec/lean-notes.md` is this project's half of that skill.** It is the
  domain-specific record (`Codec`, `Bytes n`, `relRepeat`, `Suffix`, the Layer-2
  seams) that used to live in the skill's Append; the skill points here. Read it
  when a proof involves this library's own primitives, and add to it — not to the
  global skill — when the lesson only makes sense knowing this library. It holds
  **lessons, not direction**: 57 of its entries are also still in the skill, which
  `tasks.md` 7.4 tracks closing. Do not add a new entry to both files.
- Lean PR/convention/proof/MWE skills: `lean-pr`, `lean-bisect`, `lean-proof`,
  `lean-mwe`, `mathlib-build`, `mathlib-pr`, `mathlib-review`, `nightly-testing`,
  `lean4-setup` (all under the `leanprover` skill family).
- Nix: the `nix` skill; `devenv`/`devenv-migration` only for actual devenv work.
