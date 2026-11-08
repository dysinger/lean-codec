# Tasks — `codec-drift-closure`

> **START HERE — read this before task 1.**
>
> **Status at hand-off:** authored and validating; **nothing implemented**. Zero tasks
> checked, and that is correct.
>
> **This change closes round nine's residue and attacks the one defect class the gate
> arms cannot see.** Round nine's own five-pass review ended its gate axis with _"NO
> FURTHER MUSTS FOUND"_ and its prose axis with _six_ findings, five of which share one
> shape: **a claim whose stated method is not its code's method.** Read
> `openspec/changes/codec-audit-round-nine/reviews/round-ten.md` before starting — it is
> the evidence base, in-repo, with every finding id resolvable.
>
> **Group A is blocked on the host, not on the work.** The re-run needs an idle machine.
> The owner deferred it once (`codec-audit-round-nine` tasks 2.1/2.3); **if the host is
> loaded again, do Group B/C/D and leave Group A open — do not restamp from a loaded
> run.** The reasoning is in `design.md` D1 and is not re-litigated here.
>
> **`basen-uppercase-prepass` and `basen-nat-iso` are PARKED by the owner.** Not in
> scope. Do not start them.
>
> Legend: **[M]** MUST, **[S]** SHOULD, **[N]** NITPICK.

## 0. Preconditions

- [ ] 0.1 Confirm the tree is clean and every gate is green **before** any edit:
      `git status --porcelain` empty, then `lake build`, `openspec validate --all`,
      `checks.formatting`, `checks.reviews`, `checks.mirror`, `checks.bench`. Record the
      numbers this session actually sees — **do not copy the block below**: it is
      `codec-audit-round-nine`'s closing state, not this change's starting state.
- [ ] 0.2 Re-read `AGENTS.md`'s "Pause signal" and play the alarm on every pause.
- [ ] 0.3 **Read `design.md` D2/D3 before writing an arm.** Both groups have a
      "prefer this mechanism, fall back to that" decision that is meant to be settled by
      measurement, not by preference.
- [ ] 0.4 **Do not** `git stash` / `git reset` / `git checkout -- <file>`. Commit per
      group.

## 1. [M] Group A — the benchmark re-run and the restamp

Findings: `codec-audit-round-nine` 2.1, 2.3, and `P4-N3` (the open range).

- [ ] 1.1 Confirm the host is **idle** before running anything: `uptime` and
      `ps -A -o %cpu,comm -r | head -5`, recorded in the commit message. If load is
      above ~1 per 4 cores, or the top consumer is not this session, **stop and do
      Group B instead**; leave 1.1–1.6 open with a note saying why.

      **BLOCKED — measured twice this session, and the second time is the decisive one.**

      | when | `uptime` | top consumer |
      | --- | --- | --- |
      | session start | `4.89 3.51 2.74` | `lean /tmp/p3.lean`, **99 %**, etime `10:21` |
      | after Groups B/C/D | `2.51 3.25 3.16` | the *same* `lean /tmp/p3.lean`, **99 %**, etime `10:32` |

      The load fell, but the criterion is **both halves**: load above ~1 per 4 cores (10
      cores here, so ~2.5 — the second reading sits exactly on it) **and** "the top
      consumer is not this session". The top consumer is a **stray `lake env lean
      /tmp/p3.lean` from a previous session**, parent PID 82234, which had been burning
      one core for ten and a half hours before this session began and was still burning it
      when the groups above were finished.

      Per the banner: **"never restamp the tables from a loaded run."** A one-core
      neighbour on a ten-core machine is exactly the perturbation that made round nine's
      burst rows clock granularity. So 1.1–1.6 stay **open**, and the reason is the host,
      not the work.

      **Do not kill it to unblock.** It belongs to another session (possibly another
      agent's live probe); killing it is a decision for the owner, not a way to make a
      measurement look clean. **And do not work around it** by running the bench anyway and
      stamping the result — that is the defect this group exists to prevent.

      To resume: when the owner confirms the machine is idle (`uptime` in the `0.3`–`0.8`
      range on 10 cores, top consumer this session), run 1.2–1.6 exactly as written.

- [ ] 1.2 `lake build bench`, then two runs of `.lake/build/bin/bench 4096 4096`. Save
      both logs. Do not run anything else concurrently.
- [ ] 1.3 Re-derive **every** cell with `python3` from the printed `ns` and
      `steps/burst` — not by eye, and not from `codec-audit-round-nine`'s recipe copied:
      read the span the lane prints (`512` for the window rows, `4096` otherwise).
- [ ] 1.4 Derive **every** interval twice — once from the medians (which is what this
      document quotes) and once from the full cell range — and state which is which. The
      padded-range defect has fired four times; the defence is to derive both and say
      which one the sentence is.
- [ ] 1.5 Update the three performance tables and **move the vintage stamp**. Delete the
      old medians; do not caveat them.
- [ ] 1.6 Close `P4-N3`: the `26.97–28.56` cross-table splice is replaced by whatever
      the run produces, and the sentence that made the claim is re-read against it.

## 2. [M] Group B — numbers become generated or deleted

Findings: the header-cell (`769` vs `427`) confusion, the stale gate-output block, and
the four padded ranges.

- [x] 2.1 **Decide the mechanism for the generated gate-output block by trying both**
      (`design.md` D2): (a) a marked region + generator, (b) a check that regenerates
      and diffs. Prefer (b). Record which worked and what broke.

      **(b) worked, as D2 predicted**, and it was tried against a live defect rather than
      a hypothesis. The region markers are kept **as well** (`<!-- BEGIN/END GENERATED
      gate-lines -->`), which D2 listed as an *alternative*; keeping both is strictly
      better here because the marker makes the generated span visible in a diff while the
      check still, and the check is what fails the build. What broke, and had to be fixed
      twice before it was right:

      - **`--write` was not idempotent.** The first version wrote one newline before the
        END marker where the committed file had a blank line, so `checks.gate-lines`
        would have failed on a green tree forever. Root cause: `$(emit_block)` — command
        substitution — **strips the trailing newline**, so the block has no terminator of
        its own and the separator must be written explicitly. Found by mutation-testing
        the check, which is what §2.2 asks for.
      - **The pre-commit hook reformats markdown**, so the committed README is
        prettier's, not the generator's. The generator must therefore be idempotent
        *against prettier's output*, which it now is (verified by running `--write` twice
        and getting a byte-identical file).

- [x] 2.2 Implement it so that the README's quoted block cannot drift from the gate.
      Mutation-test: change one asserted count in `Axioms.lean` without regenerating, and
      confirm the build fails **naming the block**.

      **Landed as `scripts/gen-readme-gate.sh` + `checks.gate-lines`.** The generator
      **asserts its own denominator**: `EXPECTED_GATE_LINES = 14`. Without it, a build
      that stopped emitting the gate would produce a zero-line block that "matched" a
      zero-line region — the vacuous-pass shape, in the check that exists to catch
      vacuous passes.

      **The check was red on the first sandboxed run, correctly**, with a real one-line
      diff — that failure is what found the idempotence bug above. Green after the fix:
      `gate-lines check: README's quoted gate block matches a fresh build`.

      **Mutation-tested** (both directions):
      - perturbing one count in the block (`345` → `344`, a stale hand-edit) makes
        `--write` produce a diff and the check fail naming the region;
      - `--write` twice is byte-identical.

      Measured justification, not hypothetical: **3 of the 14 committed lines were stale
      at HEAD** — `constant kinds`, `stated footprints`, `recursion-principle promotion` —
      while the prose above them read "pasted verbatim from a green build".

- [x] 2.3 Audit every remaining hand-written count in `Axioms.lean`'s header, `README`'s
      law/table prose, and `flake.nix`. For each, choose **generate**, **assert**, or
      **delete in favour of a pointer**. List them in this file with the choice, because
      the list is the completeness claim.

      The enumeration came from a command, not from reading: an `Axioms.lean` prose scan
      for bold/quoted/bare numerals outside the generated regions returned **56 sites**
      (re-measured after the §2.3 edits; the first count, taken before them, was 45 and
      is not the number to trust).
      The choices, by site class:

      | site | choice | how |
      | --- | --- | --- |
      | `Axioms.lean` header "Current state" tables (427/345/82, 140/115/25) | **assert** | `headerNumbers` `run_cmd` + `expected*` constants; unchanged, and the existing design is the right one |
      | `Axioms.lean` footprint distribution table | **generate** | `scripts/gen-axioms.lean` (pre-existing) |
      | `Axioms.lean` census table (771/348/0/0/8/14/8/0) | **assert** | `constantKindCensus` arm |
      | `Axioms.lean` `expected*` constants (7 of them) | **assert** | they *are* the assertions |
      | `Axioms.lean` history triples at former lines 176 / 216-218 / 229-230 / 1809-1810 | **delete** | three sets of historical counts (`141/112/29`, `364/292` vs `382/310`, `209/78/4/34=325`) that **no command reproduces**; the lesson is kept, the figures live in git history |
      | `README` "14 lines of output" block | **generate** | `checks.gate-lines` (§2.2) |
      | `README` [S1] "19 Iso-valued definitions (13+4+2)" | **assert** | `scripts/count-values.lean` → `checks.values` |
      | `README` [S3] "fifteen = 7 constructors + 8 bounded" and the four witnesses | **assert** | same script (`12 Codec-valued`, = 8 + 4) |
      | `README` performance tables | **untouched** | Group A's business (§1); every cell there is already a lane output or marked absent |
      | `flake.nix` prose | **unchanged** | audited and found to contain **no** hand-written count of the gate's output — its comments describe mechanisms and quote a `nix build` recipe, not a figure. Recorded as a checked row rather than skipped, because "we did not look" and "there was nothing" are different claims |

      **The three deleted triples are the interesting row.** Each was a *historical* count
      quoted to explain a past defect, and each was unverifiable: `git log -S` on
      `141 / 112 / 29` finds only the commit that **wrote the sentence**, not a run that
      produced the numbers. A historical count with no provenance is the padded-range
      defect wearing a citation, so the sentences now state the lesson and point at git
      history for the figures. AGENTS.md's own rule — "do not quote a withdrawn figure in
      the paragraph that forbids quoting withdrawn figures" — applies to never-measured
      ones too.

      **`scripts/count-values.lean` is a new, needed artifact**: README's two counts were
      hand-derived paragraphs whose *reproducing command did not exist*. They now do, the
      predicate is written out (including its removals, `_f`/`_sunfold`/`_unsafe_rec`/
      `_flat_ctor`, counted so the removal is visible), and the totals are `throwError`ed.
      Mutation-tested: `expectedIsoValues := 18` fails naming the README claim.

- [x] 2.4 Apply the same to `AGENTS.md`. It is full of numbers ("13 gate lines", "65–67
      ns/call"). Either they are generated, or they are pointers to the file that holds
      the authority, or — where `AGENTS.md` is deliberately a _lessons_ document — they
      are deleted and replaced by the rule.

      Three live errors were found and fixed, and the pattern is worth naming: **two of
      them were in the section whose job is to stop exactly this.**

      1. **"13 gate lines"** in the verification recipe — the gate prints **14**. A stale
         count in the one place a reader trusts to tell them what a green build looks like.
         The comment now says "runs the gate", and the count is the generated README
         block's business.
      2. **The round-eight footprint cell** quoted `769 scanned / 144 mentioning / 154 found
         / 146 checked` as if current; the gate now prints `771 / 153 / 170 / 157`. A cell
         that presents itself as the current state while holding a previous round's numbers
         is the `P4-N3` citation defect in table form. It now states the *design* (a
         denominator, removals by cause, and the vocabulary's own denominator) and refuses
         to state the quantities.
      3. **The round-eight landing summary** repeated the same stale quadruple; now a
         pointer.

      **The rule is added where it can be enforced**, under "Quote the gate, never a number
      written in a file": that sentence is now backed by `checks.gate-lines` and
      `checks.values`, so in `lean-codec` it is a build failure rather than advice.

      **Deliberately left as numbers:** the performance attribution bullet's history
      (`91 → 32 → 430 → 3 → 86`), because it is a *lessons* narrative whose every value is
      already marked as withdrawn or current, and the `../lean-basen` section, whose
      numbers are that repo's gate to print, not this file's.

## 3. [M] Group C — the "method sentence" audit

Findings: the five stated-method defects (`round-ten.md`: scope word, ordering,
comparison, path, and the census-vs-partition cell).

- [x] 3.1 Build the **enumeration** of method sentences by command (`design.md` D3
      step 1), and **report the denominator**: how many comment/prose lines were scanned
      and how many matched. An audit whose vocabulary is silent about its own coverage is
      §5.3a one level up.

      **Done — `scripts/audit-method-sentences.py`.** Measured, 6 files:

      ```
      method-sentence audit — denominator: 4991 prose lines scanned across 6 files
         2206  Axioms.lean
          133  flake.nix
          865  Bench.lean
          134  scripts/gen-axioms.lean
           66  scripts/gen-readme-gate.sh
         1587  README.md
      matched: 728 line(s)
      vocabulary: 9 markers declared, 9 fire
      ```

      **The corpus was wrong twice before it was right, and both times the audit would
      have reported a clean run on a false sentence** — recorded because that is this
      change's own defect class appearing in its own tooling:

      1. **`README.md` was not in the corpus at all.** The one live false method claim
         found (`grep -rn decodeWholeOne Codec/` "shows exactly those two laws") is a
         **README** sentence. An audit over the gate sources only would have missed it.
      2. **Then it read 28 of README's 1587 prose lines**, because the markdown branch of
         the line filter matched only lines starting `#` — i.e. headings. Fixed: in
         markdown, all prose is prose; only fenced ``` blocks are skipped, because a
         `grep` shown inside a fence is an example, not a claim about what a check does.

      Two findings from the audit's own denominator:

      - **`path-grep-rn` fires only 3 times, all in README** — the three paragraphs *about*
         path-scoped greps. It is not dead vocabulary after the corpus fix; it is vocabulary
         that only matches prose discussing the defect, which makes it a weak tripwire. Said
         here so the next reader knows what its 3 means.
      - **`comparison`'s 99 hits are mostly the idiom "is what" in explanation prose**, not
         method claims. The marker is **too broad**, and its count is a ceiling on the class,
         not a count of the class.

- [x] 3.2 For each candidate, classify: **assertable property** / **scope claim** /
      **unassertable**. Record the count of each — again, a denominator.

      **Re-measured after the §3.4 edits: 728 matched lines; the narrow markers select 76.**
      The classification below is over those **76 lines** — `path-literal` (65),
      `path-grep` (12), `ordering-longest` (1, the down-from-3 residue), which are the
      markers whose hits are readable one at a time. **The other 652 lines were not
      individually read**, and the table says so.

      | class | count | basis |
      | --- | --- | --- |
      | **inspected, true as written** | 66 | file pointers (`see Codec/Packed.lean`), module-inventory table rows, `nix develop …` invocations, and the `Normalizer`/`takeWhile` greps. Each verified to resolve and to say what it says. Nothing to do; re-reading them *was* the audit. |
      | **inspected, true claim, stated method did not reach it** | 2 | `README:1268`'s `grep -rn decodeWholeOne Codec/` (grep shows 13 lines, claim is two laws) and `README:461`'s `grep \`recorded at each law\`` (the phrase is **not in `Codec/`** at all, so the pointer sent the reader back to itself). Both repaired in 3.4. |
      | **inspected, scope claim wrong or overstated** | 3 | the three `longest-match-first` sentences. Two stated a rule **false of the correct list**; one quoted it as commentary. Repaired. |
      | **inspected, unassertable** | 5 | history prose that mentions a path (the stale-number paragraphs, the moved-paragraph note). Nothing to assert; each carries its reason in place. |
      | **not individually inspected** | 652 | everything matched only by the broad markers (`scope-every` 200, `scope-only` 193, `ordering` 138, `scope-all` 75, `comparison` 99 — heavily overlapping). |

      `66 + 2 + 3 + 5 = 76`, the narrow-marker count, and `76 + 652 = 728`, the
      denominator. **Both sums are printed because a classification whose rows do not add
      to the denominator is the shape round six named** — a correct total with wrong parts.

      **652 of 728 were not read line by line, and that is stated rather than hidden.** It
      is this change's own defect class in this change's own documentation. The follow-up a
      next round should make is to **narrow `comparison` and `ordering` and see whether a
      real method claim falls out**, or delete the markers as noise — not to claim 728
      audited judgements that were never made.

- [x] 3.3 For every **assertable property**, add an effect-level assertion (the
      `classifyFootprintClaim` pattern), and mutation-test it by breaking the property.

      **The order claim is the one that needed this, and round nine already landed the
      assertion.** The `footprintVocabulary` order arm asserts, for **every** phrase, that
      a segment containing exactly that phrase classifies to that phrase's own label —
      and it has two negative probes per label, with the `_` arm a *failure*. That is
      effect-level, not rule-level, and it is why round nine rejected a length-monotonicity
      assertion: it is **false of the correct list** (`` `[propext]`-only `` at 14 precedes
      `` `[propext]` `` at 9). No new arm was needed; what was wrong was the **sentence**
      claiming the rule, which is §3.4's business. A sentence and an assertion are not the
      same repair, and this task exists to keep them apart.

- [x] 3.4 For every **scope claim**, assert the scope from the environment the check
      walks, or delete the scope word. A `grep -rn … <dir>` in a comment is a scope claim
      and its path is part of it.

      **Four repairs, all live falsehoods at HEAD rather than hypotheticals:**

      1. **`Axioms.lean`'s `footprintVocabulary` comment** said the list is "ordered
         longest-match-first". **That is false of this list** — and the arm's own long note
         two screens later said so, so the file contradicted itself. Replaced with the true
         and sufficient statement (order is load-bearing; the guarantee is that every phrase
         wins its own segment) plus a pointer to the assertion. **A length-monotonicity
         assertion would have rejected the correct list**, which is why the fix is to the
         sentence, not to a new rule.
      2. **`classifyFootprintClaim`'s docstring** said "which is why the list is ordered
         longest-match-first". Same falsehood; the docstring now says the list is
         deliberately *not* length-sorted and names the effect-level arm.
      3. **`README:1268`** — "`grep -rn decodeWholeOne Codec/` shows exactly those two laws".
         That grep returns **thirteen** lines (two `def`s, two theorems, term occurrences);
         the claim (two laws) is true but the stated method does not show it. Replaced with
         the measured environment-walk result, naming both theorems.
      4. **`README:461`** — "grep `recorded at each law` for the sentence". **That phrase
         does not occur in `Codec/` at all**; it occurs in this README, so the grep sent the
         reader back to the sentence that sent them. Replaced with the file the claim is
         about (`Codec/ByteSlice.lean`). This is the F-1 shape once more: a pointer whose
         *stated method* does not reach its target.

      **The two remaining `grep` claims were verified, not deleted** — a scope claim is only
      wrong if its scope is: `grep -rn Normalizer Codec/` really returns only
      `Codec/Normal.lean` lines (13, none elsewhere — and the paragraph's whole point is
      that the falsifying `Bench.lean` is *outside* that stated path), and `grep -n
      'Iso.*takeWhile' Codec/Combinators.lean` really finds none, **non-vacuously** (the
      file has 24 `takeWhile` hits and 57 `Iso` hits separately, so the negative is not the
      silence of a broken pattern).

- [x] 3.5 For every **unassertable** one, record the reason in place. Do not leave a
      method sentence that is merely believed.

      The 10 unassertable lines are history and rationale ("the fix then claimed …",
      "round five's lesson was …"). Each already carries its reason where it sits, and
      each is explicitly past-tense so it does not read as a live claim about the tree.
      **Three historical count triples were deleted outright** and are part of §2.3's
      commit, not repeated here — they were the same class in its count form.

## 4. [S] Group D — round nine's residue

- [x] 4.1 Re-read `codec-audit-round-nine/tasks.md` for any box still open that this
      change's groups do not close, and either close it or record why it stays open.

      **Command, not memory:** `grep -n '^- \[ \]'` over round nine's `tasks.md` returns
      **exactly five** open boxes, and they are the five this change's `design.md` D4
      already predicted:

      | round nine box | this change | status |
      | --- | --- | --- |
      | `2.1` run the bench on an idle machine | §1.1 | **still open** — host, not work (see §1.1) |
      | `2.3` update the three tables and move the vintage stamp | §1.5–1.6 | **still open** — same cause |
      | `10.1` a tenth review round | §6.1 | closed by **not commissioning** one (recorded) |
      | `10.2` `basen-*` parked | §6.2 | stays parked; not touched |
      | `10.3` cross-repo consistency | §6.3 | stays deferred |

      **Nothing else is open in round nine.** So this change closes round nine's residue
      only partly — the two bench boxes remain, and they remain because of `§1.1`'s
      measured host state rather than because the change ran out of scope. That is a
      **partial** closure of D4 and is stated as such rather than as a completion.

- [x] 4.2 Update `codec-audit-round-nine/reviews/round-ten.md` if any finding id moves.
      `checks.reviews` reconciles the ids in **both** directions, so a stale row is a
      build failure — the file must stay true.

      **No id moved, and no citation was added or removed** — this change cites no
      `review P…` ids, it cites `tasks.md` sections. So `round-ten.md` is unchanged, and
      `checks.reviews` stays green. Verified by running the flake check, not by reading
      the file: see §5.4.

      **What *did* move, and is worth recording:** `round-ten.md`'s `P4-N3` section says
      the `26.97–28.56` range "is left open here rather than silently fixed because **the
      correct fix is a re-run**, and the owner has deferred benchmarking". That is still
      true — §1 could not take the re-run. So `P4-N3` **stays open**, its row is accurate
      as written, and `design.md` D4's claim that it "closes with Group A's run" is not
      yet discharged. Recorded here because D4 reads as though Group A happened.

      **`design.md` D5 additionally has a false premise**, found while doing this task and
      recorded under §4.3 rather than silently corrected: it says round nine modifies
      "the same two `codec/axiom-gate` requirements" as this change. Measured, it does
      not — the two deltas' requirement sets are disjoint. `design.md` is left as authored
      (it is the plan of record and the correction belongs where the evidence is), with
      this task as the pointer to it.

- [x] 4.3 **Archive-ordering check** (`design.md` D5): `codec-audit-round-nine` archives
      **first**, because both changes modify the same two `codec/axiom-gate`
      requirements. Before syncing this delta, re-run the scenario-count comparison
      against the then-live spec and record it here. Do not trust D5's authoring-time
      numbers.

      **D5's premise is measurably false, and the conclusion survives on a different
      reason.** Measured by command this session (`openspec/specs/codec/axiom-gate/spec.md`
      vs both deltas, scenario titles compared set-wise, not counted):

      | requirement | live | this delta | round nine's delta |
      | --- | --- | --- | --- |
      | A stated measurement is a measurement, or it is a classification | 1 | **3** | — |
      | A figure is committed only with the run that produced it | 5 | **6** | — |
      | The partition extends to public definitions, not only theorems | 9 | — | **10** |
      | A structure-field projection is not reported as a law | 2 | — | **3** |
      | A gate name-list asserts the property it exists to represent | 4 | — | **5** |
      | An axiom exclusion is explicit and justified in place | 6 | — | **6** |

      **The two changes modify DISJOINT requirements.** D5 says they "both modify the same
      two `codec/axiom-gate` requirements"; round nine's delta touches four *different*
      ones and neither of this change's two. So there is **no MODIFIED-block collision and
      no archive-ordering dependency from the hazard**. D5's stated reason is wrong.

      **What the table does show is a real hazard, of the other kind:** round nine's delta
      carries **more** scenarios than the live spec has for every requirement it touches
      (`10 vs 9`, `3 vs 2`, `5 vs 4`, `6 vs 6`) — i.e. **the live spec is already behind
      round nine's delta.** That is not a collision; it is an un-synced earlier change.
      It is safe (a superset), and it means round nine's archive will **add** those
      scenarios rather than drop any.

      **No live scenario is dropped by either delta** — checked set-wise above, `none` in
      all six rows.

      **Ordering conclusion, on the measured reason:** **archive `codec-audit-round-nine`
      first anyway**, because it is the earlier change and its delta is un-synced; syncing
      a later change first would leave the live spec in a state where round nine's
      archive then re-replaces blocks this change never touched — harmless here, but the
      rule "earlier change first" is the one that stays true as deltas accumulate. This
      change's delta is then synced and re-checked. **The check is re-run at archive time,
      not trusted from this paragraph.**

## 5. [S] Gates and docs

- [ ] 5.1 `lake build` — record the line count and every asserted count.
- [ ] 5.2 `openspec validate --all`.
- [ ] 5.3 `checks.formatting` (treefmt + sandboxed prettier — **not** `nix fmt`, and note
      that `--clear-cache` is not a flag this `nix` accepts; use
      `--no-link --print-build-logs`).
- [ ] 5.4 `checks.reviews`, `checks.mirror`, and the new generator check from 2.2.
- [ ] 5.5 `checks.bench` — builds **and runs**; note it needs `lean4` + `stdenv.cc`, not
      just `git`, and `set -euo pipefail`, or its greps cannot fail the build.
- [ ] 5.6 `checks.lean` sandboxed, detached with `nohup`, polled.
- [ ] 5.7 Spot-check `#print axioms` on anything this change touches. Expect
      `[propext, Quot.sound]` or empty, never `Classical.choice`.
- [ ] 5.8 `CHANGELOG.md` — one entry in the register of a **correction**, and
      `AGENTS.md`'s lessons section gains the two new shapes (**padded range**,
      **scope word**).

## 6. Recorded, deliberately not in this change

- [ ] 6.1 A tenth review round. This change closes the ninth's residue; it does not
      commission another.
- [ ] 6.2 `basen-nat-iso` and `basen-uppercase-prepass` — PARKED by the owner pending
      the library-division decision. Do not touch.
- [ ] 6.3 Cross-repo (`lean-basen`) consistency — out of scope by owner instruction.
