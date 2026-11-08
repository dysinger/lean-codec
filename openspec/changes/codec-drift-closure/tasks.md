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

- [ ] 2.1 **Decide the mechanism for the generated gate-output block by trying both**
      (`design.md` D2): (a) a marked region + generator, (b) a check that regenerates
      and diffs. Prefer (b). Record which worked and what broke.
- [ ] 2.2 Implement it so that the README's quoted block cannot drift from the gate.
      Mutation-test: change one asserted count in `Axioms.lean` without regenerating, and
      confirm the build fails **naming the block**.
- [ ] 2.3 Audit every remaining hand-written count in `Axioms.lean`'s header, `README`'s
      law/table prose, and `flake.nix`. For each, choose **generate**, **assert**, or
      **delete in favour of a pointer**. List them in this file with the choice, because
      the list is the completeness claim.
- [ ] 2.4 Apply the same to `AGENTS.md`. It is full of numbers ("13 gate lines", "65–67
      ns/call"). Either they are generated, or they are pointers to the file that holds
      the authority, or — where `AGENTS.md` is deliberately a _lessons_ document — they
      are deleted and replaced by the rule.

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

- [ ] 4.1 Re-read `codec-audit-round-nine/tasks.md` for any box still open that this
      change's groups do not close, and either close it or record why it stays open.
- [ ] 4.2 Update `codec-audit-round-nine/reviews/round-ten.md` if any finding id moves.
      `checks.reviews` reconciles the ids in **both** directions, so a stale row is a
      build failure — the file must stay true.
- [ ] 4.3 **Archive-ordering check** (`design.md` D5): `codec-audit-round-nine` archives
      **first**, because both changes modify the same two `codec/axiom-gate`
      requirements. Before syncing this delta, re-run the scenario-count comparison
      against the then-live spec and record it here. Do not trust D5's authoring-time
      numbers.

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
