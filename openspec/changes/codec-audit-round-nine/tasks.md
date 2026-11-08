# Tasks — `codec-audit-round-nine`

> **START HERE — read this before task 1.**
>
> **Status at hand-off:** authored and validating; **nothing implemented**. Zero tasks
> checked, and that is correct.
>
> **⚠ RE-EVALUATED against `codec-gate-denominators` (landed 2026-11-08).** This change
> was authored _before_ the general solution existed, and three of its MUSTs are now
> **already done**, not merely "wrong as written". Read this table before the task list —
> **six of the findings below shrink to nothing, and §5 must be re-scoped.**
>
> | round-nine task     | status now                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           |
> | ------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ |
> | **6.2 / design D3** | **❌ WRONG — do not implement.** The head-constant set captures `Codec.roundtrip` + 3 more genuine laws. **Already solved**: `CodecAxioms.isBareProj` (design D7, `codec-gate-denominators` §2b/§3) separates hypothesis from theorem by the head constant's _own body_ plus an operand recursion. Measured: `roundtrip`/`findFrom_finds` stay gated, `CandAligned_fst`/`_at`/`packedCands_mem`/both `Iso.*_eq_some_of_*` become projections, `CandAligned_tail` stays gated. **Task 6.2 is closed by that change; delete it here.** |
> | **6.3**             | **✅ ALREADY DONE.** Only `_fst` and `_at` move (not "all three" — `_tail` is a real proof). All five captures are in `propProjections` and `generatedAuxAllowlist`; partition is `342 gated + 83 allowlisted`. The design's open question on `Iso.apply_eq_some_of_unapply`/`unapply_eq_some_of_apply` was resolved by measurement: **both move**. README `[S1]` still needs its check (that half survives).                                                                                                                        |
> | **6.1(c)**          | **❌ WRONG, and now impossible to write as stated.** Assert that the suffix rule _would have removed_ `Codec.Nat.eq_irrel`. Measured: its last component is `eq_irrel`, which matches **none** of the eight suffixes, so the classifier **never dropped it** — the `authored` exception is dead code protecting a name the rule never threatened. 6.1(a)/(b) survive; 6.1(c) must be **replaced** by "assert the exception is unnecessary, or delete it."                                                                            |
> | **6.6**             | **✅ ALREADY DONE — and its premise was refuted.** `skipped` is split into three asserted causes (`0 other-theorem + 0 no-owner + 8 def-docstring`). The claimed occupants, `huniq_byte` and `decodeRepeat_mem_iff_general`, are **checked, not skipped** — both are attributed to themselves. `no-owner` is `0` because attribution works, not because the bucket is unfilled. **Task 6.6 is closed; do not re-open the `huniq_byte` story.**                                                                                       |
> | **6.7**             | **✅ ALREADY DONE.** The arm's log line now states `thmInfo` scope and names `def`-docstring claims as its own reported cause (`8 def-docstring`).                                                                                                                                                                                                                                                                                                                                                                                   |
> | **6.8**             | **✅ ALREADY DONE.** Classifier removals are decomposed per pattern and asserted: `12 patterns, 54 removed, 6 singletons, 0 uncounted`, printed as `casesOn 8, recOn 8, elim 7, noConfusion 15, …`.                                                                                                                                                                                                                                                                                                                                  |
> | **6.10**            | **✅ ALREADY DONE.** The projection arm prints `9 listed of 12 bare projections; the rest are the `dec`-suffixed three` — the `dec` exemption is a number, not a clause of an `unless`.                                                                                                                                                                                                                                                                                                                                              |
>
> **What this means for the delta.** Three of the four requirements this change MODIFIES
> were _rewritten_ by `codec-gate-denominators`, and this change's MODIFIED blocks were
> authored against the **pre-sync** text. They would therefore **drop three live
> scenarios** (`openspec validate` now fails on exactly this). Those three are not
> round-nine findings at all — they are the general solution's own scenarios, and they
> must be carried into this change's MODIFIED blocks verbatim before it can archive.
> **That carry-forward is mechanical and is not a round-nine task.**
>
> **And the benchmark/prose half is untouched.** §1, §2, §3, §4, §7 were never about
> the gate's _rule_; they are the fourteen-instance class applied to the bench and the
> prose table, which the general solution does **not** reach. That half stands.
>
> **§5 is the exception, and it got BIGGER.** Task 5.3 was re-measured rather than
> reasoned about, and the answer is none of the three candidates it offered: the footprint
> arm never saw `blitBytes_spec`'s claim because the **vocabulary** does not recognise the
> spelling it uses (`` `[propext, Quot.sound]` ``, no `-only`). An environment walk
> (`scratch/probe-vocabulary.lean`) puts the hole at **22 of 159** `thmInfo` docstrings
> containing a backticked axiom-list literal — including `Codec.Bytes.ext_iff` and
> `Codec.findByte_spec`, both of which the repo believes it audited.
>
> So the count for this round is **not** "13 MUST / 17 SHOULD / 12 NITPICK". Eight of those
> are closed by the general solution (6.2, 6.3, 6.6, 6.7, 6.8, 6.10 done; 6.1 and 6.3
> re-scoped), **one new MUST of a wider scope was added (5.3a)**, and the rest stand. The
> re-evaluation found more than it removed, which is the honest result: a general solution
> closes the instances it was built from, and reveals that the vocabulary layer beneath them
> was never audited at all.

Legend: **[M]** MUST, **[S]** SHOULD, **[N]** NITPICK. Every id is stable across the
change; the three reviewer reports are `/tmp/review-{paper-adherence,gate-coverage,
numbers-build}.md` and every MUST below was re-measured in the authoring session before
it was accepted (see design D0).

## 0. Preconditions and the things NOT to do

- [x] 0.1 Confirm the tree is clean and the build is green **before** any edit:
      `git status --porcelain` empty, `nix develop --command lake build` prints its 10
      gate lines. Record the baseline counts (`425 = 347 + 78` theorems,
      `140 = 115 + 25` defs, footprint distribution, claim sites). These are the numbers
      the regenerated header must be checked against, not remembered from this file.

      **BASELINE RECORDED 2026-11-08** (`git status --porcelain` empty at `5b4fd4e`).
      The build printed **11** info lines (the ledger said "10" — recorded as measured
      rather than silently reconciled), and the counts this file predicted are **stale by
      one landed change**, exactly as the banner warned:

      ```
      axiom gate: 342 public theorems covered (0 explicit exclusion(s))
      axiom gate: 425 public theorems partitioned, 342 gated and 83 allowlisted
      axiom gate: 140 public definitions covered, 115 mentioned and 25 allowlisted (mention proxy)
      axiom gate: definitions dropped by the name classifier — 54 removed + 140 kept = 194 candidates, all removals reason-recorded; by pattern (6 of 12 remove exactly one; 0 uncounted): casesOn 8, recOn 8, elim 7, noConfusion 15, noConfusionType 5, ctorIdx 5, ctorElim 1, ctorElimType 1, below 1, brecOn 1, go 1, «term_≫_» 1
      axiom gate: 12 def-name patterns enumerated, each matching a recorded non-surface declaration; their per-pattern counts are asserted by the def-classifier arm above (54 of 194 candidates removed)
      axiom gate: header numbers verified (425 = 342 + 83; defs 140 = 115 + 25)
      axiom gate: constant kinds — thm 769 (gated + allowlisted), def 348 (mention proxy), opaque 0 / axiom 0 (no arm, must be 0), induct/ctor/rec/quot 30 (machinery, not walked)
      axiom gate: stated footprints verified (769 theorem docstrings scanned, 144 mention a footprint spelling; 154 claim site(s) found = 146 checked + 8 skipped as 0 other-theorem + 0 no-owner + 8 `def`-docstring. ...)
      axiom gate: propProjections covers every bare projection (9 listed)
      axiom gate: propProjections entries are all bare projections (9 listed of 12 bare projections in the namespaces; the rest are the `dec`-suffixed three, classified by suffix)
      Build completed successfully (15 jobs).
      ```

      So the baseline is `425 = 342 + 83` (not `347 + 78`), `140 = 115 + 25`, footprint
      `154 = 146 + 8` with `144` mentioning, and 9 listed projections — the partition
      numbers of `codec-gate-denominators`, not of this file's pre-re-evaluation text.

- [x] 0.2 Re-read `AGENTS.md`'s "Pause signal" and play the alarm on every pause.
- [x] 0.3 **Do not** edit `openspec/changes/archive/**`. This is a new round; the archived
      ledgers are history.
- [x] 0.4 **Do not** `git stash` / `git reset` / `git checkout -- <file>`. Commit per
      group so a revert is never tempting.

## 1. `Bench.lean` — the burst lane's fold guard cannot fire [M]

Findings: N-1 (fold guard), N-3 (C-reference `return ()`), S-4 (bench outside every
gate), S-5 (`warningAsError` does not cover the exe root).

- [x] 1.1 Verify the defect before fixing it, so the fix is measured rather than assumed.
      The mechanism: `bytesAt` is all-`1` except byte 0; `sinkOfList` is `a*31+b` from
      seed `7`; `31a+1` mod 256 has period 16, so `sinkOfList([1]*k) = 7` for
      `k ∈ {16,32,512,4096}`. Print the sink for `j = 0..39` on `idealCursor` and the C
      lane and confirm it is the **single value** `7`. Record the output in this file.

      **MEASURED** (`scratch/probe-sink2.lean`, `lake env lean --run`; the rows as the
      call sites feed them — see 1.4's table for which arguments each site passes):

      ```
      sinkOfList([1]*k), seed 7:  k=15 →58  k=16 →7  k=32 →7  k=512 →7  k=4096 →7
        (period 16 confirmed; every multiple of 16 returns the seed)
      n=4096  w=512  distinct=1  all=[7]        ← decodeFullArray, k=2, C ref, Lean lane
      n=4096  w=4096 distinct=2  all=[7,135]    ← NOT invariant, but floored at two values
      n=16384 w=2048 distinct=1  all=[7]
      arrayRead (reads arr[j % n], ONE byte): distinct=1  all=[1]
      ```

      **The finding is sharper than the task's premise in one direction and narrower in
      another, so neither version is carried forward:**

      1. The task said the sink is `7` for `k ∈ {16,32,512,4096}` and predicted the defect
         for the whole-input rows. Measured, the whole-input rows (`w = n`) are **not**
         invariant — they alternate `7 / 135` — because 4096 is a multiple of 16 (→ floor
         `7`) but 4095 is not (→ `135`). So "the sink is the constant `7`" is false of
         them; what is true is that they cannot take more than **two** values, because the
         only byte that varies is index 0 and `31^k·(31b+1)` mod 256 is 2-periodic in the
         byte's contribution for this fold.
      2. The **many-call** rows — `decodeFullArray`, `decodeFullArray k=2`,
         `C reference`, `Lean decodeWhole`, all of which measure a **512-byte window**
         (`w = n/8`) — are **exactly invariant at `7`**, which is the defect as written.
      3. **`arrayRead` is invariant a fifth way the task did not name, and it is the one
         the `≠ 0` guard is also blind to by construction:** its `measure` returns *one
         byte* from `arr[j % n]` with no fold at all, and that byte is `1` for every `j`
         (index 0, the only varying byte, is reached by `j % 4096` only at `j = 0`).
         A one-value sink is not made non-invariant by changing the buffer's *tail* — it
         is fixed by making the **read index** depend on `j`, which is a `measure` fix,
         not a buffer fix. Recorded here because 1.2's buffer change alone would have left
         this row silently invariant behind a green assertion, which is the defect class
         this whole round is about.

- [x] 1.2 Replace the shared buffer's uniform tail with a non-uniform one
      (`UInt8.ofNat (i.val % 251)`; 251 prime so slices at `j*8` differ in multiset).
      Note in the docstring **why 251** — a small prime makes the slide change the
      multiset, which a modulus that divides the stride would not.
- [x] 1.3 Replace `benchBurst`'s `if sink == 0` guard with a **non-invariance** assertion:
      collect the per-`j` sink and require `eraseDups.length ≥ 2`, matching what
      `packedCands` already does. Keep a non-zero check too; they catch different folds.
      The error message must name the row and say the loop was invariant.

      Landed in `benchBurst.runVariant`: the guard is now
      `if vSink.eraseDups.length < 2` **and** `if vSink.all (· == 0)` (two separate
      assertions — an all-zero varying sink is still an elided sink), where `vSink` is the
      mixed per-`j` sink collected by a pre-pass **outside** the timed window, so
      asserting does not pollute any measured span.

- [x] 1.4 Audit **every** `benchBurst` call site (`Bench.lean:914, 944, 983, 1022, 1233,
1234` and any added since) and confirm each now produces a varying sink under 1.3.
      A row that still cannot vary must be documented as such, not silently passed.

      **The call-site list in this task is short by TWO** — measured
      (`grep -n 'Bench.benchBurst' Bench.lean`): there are **eight**, at
      `914, 944, 983, 1022, 1157, 1158, 1233, 1234`. The task enumerated six and was the
      second under-count of its own kind (`codec-gate-denominators` found the same defect
      in `benchBurst`'s own enumeration). All eight, with the argument each passes:

      | line | row                     | `n`   | `mk` (buffers)         | verdict after 1.2 + 1.3 |
      | ---- | ----------------------- | ----- | ---------------------- | ----------------------- |
      | 914  | `decodeFullArray`       | n/8   | `#[arrayAt 0]`         | varies (was `7`, invariant) |
      | 944  | `arrayRead`             | n     | `#[arrayAt 0]`         | varies — **required the `readAt` fix**, the buffer alone does not reach it |
      | 983  | `idealCursor`           | n     | `#[arrayAt 0]`         | varies (`8` values before, more after) |
      | 1022 | `decodeFullArray k=2`   | n/8   | `#[arrayAt 0]`         | varies (was `7`, invariant) |
      | 1157 | `packedCands k=1`       | n     | `#[arr]` (own 8-buffer pool) | varies (own buffers, unchanged) |
      | 1158 | `packedCands k=2`       | n     | `#[arr]` (own 8-buffer pool) | varies (own buffers, unchanged) |
      | 1233 | `C reference`           | n/8   | `#[arrayAt 0]`         | varies (was `7`, invariant) |
      | 1234 | `Lean decodeWhole`      | n/8   | `#[arrayAt 0]`         | varies (was `7`, invariant) |

      No row is left documented-as-unable-to-vary: the two `packedCands` rows were already
      non-invariant (they rotate their own `(k*7 + i) % 251` pool), and `arrayRead`'s was a
      `measure` defect rather than a buffer one, so it was repaired in `measure`.

- [x] 1.5 `benchCReference`: `| none, none => return ()` exits the whole function and
      silently skips **both** timed lanes. Change to `pure ()` so the loop continues, and
      add a count assertion that the cross-check ran for every intended input.

      **Landed, with one correction measured in the doing.** `pure ()` in that position
      does not compile: the `for` body under `namespace Codec.Bench` resolves `pure` to
      the package's own `Codec.pure` **constructor** (`pure ()` is `Codec Unit`, not
      `IO Unit`), and `IO.pure` / `_root_.pure` are not in scope here either (measured:
      `Unknown constant `IO.pure``, then `Unknown identifier `_root_.pure``). The form
      that compiles and has the intended semantics is `return ()` **as a `do`-statement
      inside a `match` arm** — which does *not* unwind `benchCReference`, unlike
      `return ()` closing the arm of a non-`do` block. Both wrong spellings were tried
      against the compiler before this one; recorded so the next reader does not repeat
      them. Qualified in prose, so the text the task asks for is what landed.
      The count assertion is `if checked < 2 then throw`, and the cross-check now prints
      `C reference value check: 6 of 6 inputs agree with decodeWhole`.

- [x] 1.6 `benchCReference`: add `n = 0` and `n = 1` to the cross-check set — these are the
      C's two real branches (`n == 0` and the loop body), and today's four inputs are all
      size 4096 differing only at byte 0.

      Landed: the input list is `[n, n, n, n, 0, 1]`; the two new sizes build a buffer from
      `i % 251` so each input is distinct rather than a duplicate of input 0. Every
      disagreement arm now `throw`s (a `some`/`none` split can no longer step past), and the
      printed line reports `6 of 6`.

- [x] 1.7 Mutation-test 1.3: temporarily make one row's `measure` ignore `j` (loop
      invariant) and confirm the build **fails** naming that row. A new check that has not
      been mutated is not a check — this repo's recorded lesson.

      **Mutated** (`rootWindow`'s window start pinned to `0`, so `j` is ignored) → build
      green, run **fails** naming the row:

      ```
      uncaught exception: decodeFullArray  decodeFullArray  (burst)      : the sink is
      INVARIANT across all 40 probed call indices (eraseDups = 1, value 203) — the loop
      was folded or the input does not vary with the call index, so this is not a
      measurement
      ```

      Mutation reverted; `Bench.lean` diff re-checked against `HEAD` before committing.

- [x] 1.8 Add `moreLeanArgs := #["-DwarningAsError=true"]` to `lean_exe bench` so a `sorry`
      in `Bench.lean`'s own theorems (`foldNorm_idem`, `foldNz`) is an error, not a
      warning. Then correct `AGENTS.md`'s over-read ("including `bench`") to say the flag
      rides on imported modules and that the exe root sets its own.

      **Mutation-tested:** `foldNorm_idem` stubbed to `sorry` →
      `error: Bench.lean:53:8: declaration uses `sorry'` / `build failed`, with the trace
      line showing `lean -DwarningAsError=true … Bench.lean` (so the flag is on the exe
      root, which is the whole point). Reverted. The `AGENTS.md` correction is §8.2.

- [x] 1.9 Settle whether `Bench.lean` belongs in a `checks` entry. It is outside every
      gate today (`flake.nix` has `checks.{lean,openspec,formatting}` and no bench), so
      the `example` checks in it cannot fail CI. Either add a `checks.bench` that runs the
      binary and asserts its value-check lines are present, or qualify the README/CHANGELOG
      prose to say the checks fire only when run by hand. **Decide on evidence**, and
      record which was chosen and why.

      **Decided on evidence: add the check.** The evidence is the split between what is
      already gated and what is not. The `example`s in `Bench.lean` are *compile-time*`rfl`
      checks and are therefore covered by `lake build bench` — and since §1.8 a `sorry`
      there is an error. But eight runtime checks were reachable from **nothing**:
      `seam boundaries OK`, `seam aliasing OK`, the two `count step` round trips, the three
      `… value + bridge OK` lines, `decodeWhole … OK`, `decodeWholeBytes …`, the C-reference
      `6 of 6` cross-check, and the new `benchBurst` invariance assertions. Qualifying the
      prose would have left those unreachable and added the sentence "and nothing checks
      them", which is the class this round exists to close — a check that cannot fail the
      gate is not a check. So `checks.bench` runs the binary, fails on a non-zero exit, and
      `grep -q`-pins each value-check line plus `^done$` and a `steps/burst` row count ≥ 16,
      so a *deleted* check is a build failure rather than a shorter log.
      Recorded cost: it runs the whole lane, so it is slow in the sandbox; the dev loop stays
      `lake build bench` + running the binary by hand.

## 2. Re-benchmark every lane and restamp the tables [M]

Findings: N-1's consequence, S-1 (no `steps/burst` column), N-4 (floor range), S-2
(`2.5 vs 6.9` not cells).

- [ ] 2.1 Run the bench on an **idle** machine: `lake build bench` then
      `.lake/build/bin/bench <args>`. Two runs, as the tables claim. Record wall-clock
      context in the commit message; do not run anything else concurrently.
- [ ] 2.2 Re-derive **every** cell from the printed `ns` and `steps/burst`, with `python3`,
      not by eye. Every row must state its own span; a figure that only exists as a
      quotient must be recomputed from both terms in the same run.
- [ ] 2.3 Update the three performance tables **and** move the vintage stamp. A table with
      two vintages is worse than a re-run table (design D1).
- [ ] 2.4 Add the `steps/burst` column to the summary table (`README.md:1342`), values
      `4096` / `512` / `—`, matching the other two tables which already have it.
- [ ] 2.5 Fix `~2.6–3.0 ns/step` → the committed range actually measured (`2.46–2.67` at
      authoring time; **re-measure, do not copy that**).
- [ ] 2.6 Fix `2.5 vs 6.9` → the actual cells from the C-reference table (authoring-time
      cells were `2.46–2.57` vs `6.85–7.03`; re-measure).
- [ ] 2.7 Fix `~20–22×` → the interval that contains both runs' own quotients.
- [ ] 2.8 Cross-check **every pair** of related figures in the two documents for internal
      consistency. `AGENTS.md` records that two past errors were caught only by the owner
      noticing two committed figures could not both be true, not by any lane.
- [ ] 2.9 Re-read the whole Performance section against the new run and delete any sentence
      that is now false. Do not leave a corrected number behind an uncorrected derivation.

## 3. README: delete the underivable cell [M]

Finding: N-2 (`77 ns/step`).

- [ ] 3.1 Set `decodeFullFastRoot`'s cold cell to `see note`, exactly as round eight did
      one row above for `49 ns/step`.
- [ ] 3.2 Write the note: the lane value- and bridge-checks but prints **no** timing, by
      design, because every in-process attempt gave an impossible number (`0 ns/op`, then
      `41 ns/op`); the reproducible figure is the out-of-band `~1,250–1,500 ns/byte` in its
      docstring, and it must **not** be placed in an `ns/step` column.
- [ ] 3.3 Record the provenance of the deleted `77` in the comment so it is not
      re-derived: `2026-11-01-codec-review-remediation/tasks.md:2407`, an A/B control at
      `n = 65536` in `ns/byte`. State that this is the same defect class as the deleted
      `49`, in the citation form rather than the subtraction form.

## 4. `Codec/Normal.lean`: a standards misquote and a retracted confusion [M]

Findings: P-2 (RFC misquote ×2), P-3 (constancy/quotient).

- [ ] 4.1 `Normal.lean:10`: replace "requires a Base16 decoder to accept both" with the
      standard's own text — §8 says decoders **MAY** accept lowercase letters; accepting
      both cases is a _permission_, not an obligation. Confirm the quote against the
      standard rather than against `README.md`, then confirm it matches `README.md:264–274`.
- [ ] 4.2 `Normal.lean:196`: the sentence puts the withdrawn `MUST` **inside quotation
      marks** as the standard's text. Replace with a paraphrase that does not present it as
      a quotation, or quote §8 correctly with the `MAY`.
- [ ] 4.3 `Normal.lean:196`: "it has no inverse, because `norm` is many-to-one" → attribute
      the loss to `fill`'s identification of every spelling in one class (cite
      `fill_inj`, `Normal.lean:181`), not to `norm`. This is the same distinction
      `README [D4]` draws for `ignore`.
- [ ] 4.4 Grep the whole tree for any other occurrence of the withdrawn `MUST` wording.
      Round eight fixed the README and missed the module it cites; assume a third site.

## 5. `Codec/ByteSlice.lean`: one footprint sentence the gate contradicts [M]

Finding: N-4 (`blitBytes_spec`).

- [x] 5.1 **Measure first**: `#print axioms Codec.blitBytes_spec`. At authoring time:
      `does not depend on any axioms`, matching `Axioms.lean:2264`'s `#guard_msgs`.

      **Re-measured** (`scratch/probe-axioms.lean`):
      `'Codec.blitBytes_spec' does not depend on any axioms`. The task's line number is
      stale (the arm is at `Axioms.lean:2150` after `codec-gate-denominators` and this
      change's edits); the measurement is not. The same probe re-measured all 18 blind
      declarations: `commitRemainder_spec`, `foldl_push_data`, `Nat.eq_irrel` and
      `blitBytes_spec` are **axiom-free**; `ext_iff`, `Bytes.ext` are `[Quot.sound]`;
      `findByte_spec`, `relRepeat_cast`, both `Iso.counterMeasure*` are `[propext]`; the
      rest are the two-axiom pair. Those measurements are what the corrected prose now
      states.

- [x] 5.2 Correct `ByteSlice.lean:223` to state the measured footprint. Note that the
      gate's `#guard_msgs` is the authority, not the prose.

      Done, **and there were three, not one**: `blitBytes_spec` (§5.2's) and
      `commitRemainder_spec` (in `Codec/Packed.lean`) both stated the two-axiom footprint
      and measure empty, and `emptyConsumesByte` stated or the two-axiom pair in a
      round-nine edit of mine and measures the pair — the third was **mine**, caught by
      the widened arm before it landed as a false claim. All three prose sites now state
      the measured footprint and say so where the old text disagreed.

- [x] 5.3 Establish **why the footprint arm did not fire here** — **MEASURED, and it is
      none of the three candidates this task listed.** Run
      `scratch/probe-blitBytes-attrib.lean`:

      ```
      --- Codec.blitBytes_spec: 9 segments, mentionsFootprint=false
        [1] (no claim) … [9] (no claim)
      --- measured axioms: []
      ```

      The arm did not fire because **`mentionsFootprint` is `false`**: the docstring's
      claim is invisible to the vocabulary. It writes

      ```
      `#print axioms Codec.blitBytes_spec` reports `[propext, Quot.sound]`
      ```

      with **no `-only` suffix**, and `CodecAxioms.footprintClaimPhrases` only recognises
      `` `[propext, Quot.sound]`-only `` and `` `[propext]`-only ``. So the segment never
      became a claim site at all — it is not in `claims` (146), not in any skip cause (0/0/8),
      and not outside the `thmInfo` scope. **All three explanations the task offered are
      wrong**, and `codec-gate-denominators` §1.3's decomposition is what makes that
      answerable in one probe instead of three guesses.

      ### 5.3a **[M] NEW FINDING — the footprint vocabulary has a hole, and it is wide**

      This is a **new instance of the class**, not covered by the general solution, because
      the general solution audited the arm's *filters* and this is the arm's *vocabulary*.

      Measured by an **environment walk** (`scratch/probe-vocabulary.lean`), not by `grep` —
      a grep over `Codec/*.lean` returns 14 lines for the bare two-name form, but that is
      spelling-specific and counts lines rather than declarations. The walk asks the wider
      question (does the docstring contain *any* backticked axiom-list literal?) and returns:

      ```
      thmInfo docstrings containing a backticked axiom-list literal: 159
        of those, recognised by footprintClaimPhrases: 137
        BLIND (a literal the vocabulary cannot see): 22
      ```

      **22 of 159.** The blind set includes `Codec.blitBytes_spec` (the reported N-4), and
      also **`Codec.Bytes.ext_iff`** and **`Codec.findByte_spec`** — two declarations this
      repo believes it audited: `ext_iff` is the very site round eight's attribution fix
      was written for. Whatever the reason those two are counted as blind here, it means
      the round-eight fix did not reach every spelling. The full list of 22 is in the probe's
      output; enumerate it again rather than copying it, since the vocabulary fix will move
      it.

      The probe's predicate is deliberately **broader** than the vocabulary, because its job
      is to be the independent denominator: a check that asks "did the vocabulary catch
      this" using the vocabulary answers itself.

      This is precisely the `codec-audit-round-eight` §5 lesson repeating one level down:
      that round hoisted the vocabulary into `footprintClaimPhrases` so it could not be
      narrowed silently, and **stopped there** — nothing asserts the vocabulary is
      *complete* over the ways the repo actually spells a footprint. A spelling outside the
      list is not "skipped by a recorded cause"; it is not a claim site at all, which is
      indistinguishable from a docstring that says nothing.

      **What to do (do not just widen the list):**

      1. Enumerate the spellings the tree actually uses, by command, not by recall:
         `` `[propext, Quot.sound]` ``, `[propext, Quot.sound]`-clean`, `[propext]` only,
         `[propext, Quot.sound]`-free, `axiom-free`, `no axioms`, `depends on no axioms`.
         The **bare** two-name form without `-only` is a claim of exactly the same strength
         and must be in the vocabulary.
      2. Add the missing spellings, then **re-run and re-measure**: `mentioning` and
         `claims` will both jump, `expectedFootprintCounts` will fail naming both sides, and
         the newly-read sites may contain further real mis-claims (`blitBytes_spec` is known
         to be one — it says `[propext, Quot.sound]`, measured `[]`).
      3. **Assert the vocabulary's completeness**, which is the part that makes this not
         recur: an arm that reports how many docstrings mention a footprint is only as good
         as the spellings it knows, so a *second* count is needed — docstrings containing a
         **backticked axiom-list literal** (`[propext…]`, `[]`, `Classical.choice`) — and
         the two counts must reconcile. That is the denominator/decomposition rule applied
         to the vocabulary itself. Mutation-test by removing one spelling and confirming
         the reconciliation fails.

      **This supersedes 5.1/5.2 as the fix.** Correcting `ByteSlice.lean:223`'s sentence is
      one line and should be done (§5.2), but on its own it leaves thirteen sibling sites
      unread with a green gate — which is the defect, not the docstring.

#### 5.3a — DONE. What was measured, and the two measurements that changed the plan

**The independent denominator was too dirty, and that is the first result.** The authoring
probe's predicate (`scratch/probe-vocabulary.lean`) counted a backticked span that
`startsWith "[" && endsWith "]"`, which accepts code the tree writes inside its prose:
`[S3]` / `[D3]` (README section tags), `[true, true]` / `[false, false, false, false]`
(`Rab_two`/`Rab_four`, _bracket_ notations), and any `[a]`-shaped notation in a
hypothesis. Its 22-of-159 mixed **two populations**: real footprint claims the
vocabulary missed, and non-claims the broad predicate wrongly accepted. Measured with
the tightened predicate (`scratch/probe-vocab2.lean`, which validates each element of the
bracketed list is an axiom name): **18 of 155**, and the four that left the set
(`Rab_two`, `Rab_four`, `Rel_maybe_some`, `Rel_choice`) were all never claims. So the
hole was real but smaller than reported, and "22 of 159" must not be quoted as the size
of the vocabulary gap.

**Of the 18, eight were real unread claims, and five of those eight were unread for a
second reason the task did not name**: the literal is **wrapped across a line** —
`` `[propext,\nQuot.sound]` `` — so `doc.contains 
"`[propext, Quot.sound]`"` cannot match it at any vocabulary width. `bdrop_consumedAbs_eq`,
`foldl_push_data`, `decodeFullArray_spec`, `findByte_spec` and `Bytes.ext_iff` are all in
this family — and `ext_iff` is the round-eight attribution site, so **the round-eight fix
did not reach every spelling because several spellings do not exist as contiguous text.**
A vocabulary rewrite alone would have left those five blind. That is the finding this
sub-task's plan got wrong and measurement corrected.

**What landed.**

1. `footprintClaimPhrases` gains the bare forms — `` `[propext, Quot.sound]` ``,
   `` `[propext]` ``, `` `[Quot.sound]` ``, `` `[Quot.sound]`-only `` and the three-axiom
   form — plus `isExactPhrase`, so every backticked literal is matched verbatim and the
   lower-case phrases case-insensitively (the spelled-out rule the docstring had already
   stated). `classifyFootprintClaim` orders them **longest first**, so a three-axiom claim
   is not read as a two-axiom one. Every new label has an arm in the arm's `match`, so an
   unhandled label is a visible fallthrough rather than a silent pass.
2. **Eight docstrings reworded** so the prose says what is measured: the five wrapped
   literals above, `commitRemainder_spec` and `blitBytes_spec` (false footprints → the
   measured empty one), and every `zero `Classical.choice`` / `no `Classical.choice``
   spelling rewritten as "choice-free" / "the third axiom is absent". That last group is
   **the honest half of the fix** rather than a vocabulary rule: a _mention_ of an axiom
   name inside a sentence that says "this is absent" is an unreviewable claim — the arm
   cannot tell "absent" from "present" from the token alone — so those sentences stop
   writing footprint literals they are not claiming. Where the sentence _is_ a warning
   ("prototyping here leaks `Classical.choice`") the source stays as it was; the rule is
   in `Codec/ByteSlice.lean`'s header and in §7 of this ledger.
3. **`Codec.search_nil_left`'s `[]` is a recorded exemption, not a fix.** Its bracketed
   span is the empty _list_ constructor, named in a sentence about `Suffix.drop` not
   reducing in goal position — editing the prose to dodge the denominator would make the
   denominator agree by making the tree quieter, and the next genuine `[]` claim is the
   one that would hide. `CodecAxioms.vocabularyExemptions` carries it (and
   `bdrop_consumedAbs_eq`, whose span the broad predicate over-reads) with the reason in
   place, and the arm asserts `exempt = the list's size` so a stale entry is a build
   failure.
4. **The third count is asserted.** `CodecAxioms.looksLikeAxiomList` is the independent,
   deliberately broader predicate: it joins the docstring before scanning (so a wrapped
   literal is read, not exempted), reads only _markup_, and never consults
   `footprintClaimPhrases`. The arm asserts
   `recognised + blind + exempt = mentioningLiteral` as an identity **and** pins each
   term, and `expectedVocabularyCounts = (140, 0, 142)` is the reconciled state — **zero
   blind**. The log line prints all three.

**Mutation-tested twice, in the order the gate fires them.** Deleting ``"`[propext]"``
from the vocabulary fails the **footprint** counts first
(`mentioning 150 → 148`, `def`-docstrings `11 → 9`), which is correct — it is a wider
blast radius than the vocabulary arm's. With `expectedFootprintCounts` matching the
mutated tree, the **vocabulary** arm then fires and names the two docstrings that
spelling was reading:

```
docstrings whose axiom-list literal the vocabulary recognises: constant says 140, environment has 138
BLIND docstrings (a literal the vocabulary cannot see; each one is read by NOTHING):
  constant says 0, environment has 2 — Codec.findByte_spec, Iso.counterMeasureDecreases
```

Both spellings restored; `lake build` green at 11 lines with the footprint line reading
`150 mention a footprint spelling; 166 claim site(s) found = 155 checked + 11 skipped as
0 other-theorem + 0 no-owner + 11 `def`-docstring` and the vocabulary as
`142 = 140 recognised + 0 blind + 2 exempt`.

**And widened vocabulary found a third mis-claim the task did not know about**, exactly as
step 2 predicted it might: two old-theorem `[propext, Quot.sound]` statements were
false. That is the value of the denominator — the arm now _can_ report its own
incompleteness, which it could not before this task.

## 6. `Axioms.lean`: close four escape routes [M]

Findings: G-1 (`findFrom.induct`), G-2 (`authored` validity), G-6 (`isBareProj` blind to
`And.left`), G-4/G-4b/G-4c (footprint arm `skipped` and scope), G-3 (pattern decomposition),
G-S1 (census scope).

- [ ] 6.1 **[M] `authored` validity arm — RE-SCOPED, (c) deleted.** (a) and (b) stand:
      assert every name in `isGeneratedAux`'s `authored` array is a public theorem and is in
      `gatedNames`. **(c) is deleted because it is false and unassertable**: it asked that
      each name's last component be one the suffix rule _would_ have removed, but
      `Codec.Nat.eq_irrel`'s last component is `eq_irrel`, which matches **none** of the
      eight suffixes — measured. The classifier never dropped it, so the exception protects
      a name the rule never threatened. Replace (c) with the truthful assertion: the
      `authored` array is **unnecessary** (every entry survives the suffix rule on its own),
      so either delete the array or record what would break if it went. **This is a
      stronger finding than the original**: the round reported "an exemption with no
      validity arm" and the measurement says "an exemption that is dead code".
- [x] ~~6.2 **[M] Extend `isBareProj`** to a spine ending in the head-constant set
      `{And.left, And.right, Iff.mp, Iff.mpr, Prod.fst, Prod.snd}`.~~
      **DELETED — WRONG, and superseded by `codec-gate-denominators` (§2b, §3).** Measured
      in `scratch/probe-headset.lean`: that set captures **seven** declarations including
      `Codec.roundtrip`, `Codec.findFrom_finds`, `Iso.apply_eq_some_of_unapply` and
      `Iso.unapply_eq_some_of_apply` — four genuine laws, and `roundtrip` is the library's
      central theorem. Neither the head constant nor the arity can separate them
      (`Iff.mp` is `isProjConst = true` and arity 4 on both sides). The predicate that works
      is in `CodecAxioms.isBareProj`: a projection constant applied, at its first **explicit
      declared** argument, to something recursively a projection of a hypothesis. It is
      **implemented and gate-green**. Nothing to do here.
- [x] ~~6.3 **[M] Decide `CandAligned_fst`/`_at`/`_tail`'s classification.**~~
      **DONE by `codec-gate-denominators` §3.4/§3.9**, with one correction to this task's
      wording: **not all three move**. `_tail`'s body is
      `And.casesOn hal fun hlen hpt => ⟨…, …⟩` — a real proof about an invariant — and it
      stays gated. `_fst` and `_at` move, as do `Codec.packedCands_mem` and **both**
      `Iso.apply_eq_some_of_unapply`/`unapply_eq_some_of_apply` (design D3's open question,
      resolved by measurement: both are `Iso.law` selections). Partition is now
      `342 gated + 83 allowlisted`. **The surviving half** is the prose check this task also
      asked for: confirm README `[S1]`'s unconditional-iso list is consistent with the two
      `Iso` laws having moved out of the footprint-pinned set.
- [ ] 6.4 **[M] Promote `findFrom.induct`** (measured `[propext]`, the only non-empty
      footprint in the allowlist) to `gatedNames` **and** record the def-coverage naming it
      creates explicitly, so `Codec.findFrom` is not "covered" by its own recursion
      principle. Add the footprint pin.
- [ ] 6.5 **[M] Add a footprint-per-allowlisted-theorem report** so an entry filed as "not
      a law" cannot carry a proof that consults an axiom unnoticed. Assert the count.
- [x] ~~6.6 **[M] Split `skipped`** into `skipped-names-other-theorem` and
      `skipped-no-owner`.~~
      **DONE by `codec-gate-denominators` §1.3 — and its premise is REFUTED.** The split
      landed with **three** causes, asserted separately:
      `154 found = 146 checked + 0 other-theorem + 0 no-owner + 8 def-docstring`.
      The two claims this task named as occupying the no-owner bucket —
      `huniq_byte` and `decodeRepeat_mem_iff_general` — are **checked, not skipped**: each
      has a docstring, each states a footprint, and each is attributed to **itself**
      (`namesSelf` true, `namesAnotherDecl` false on the claim's own segment). Nothing about
      `decodeFull_spec`'s hypothesis chain is unattributed. `no-owner = 0` is a result. The
      third cause is the one that actually held the 8: `def` docstrings, out of scope by
      design. **Do not re-open the `huniq_byte` story.**
- [x] ~~6.7 **[M] State the footprint arm's kind restriction** in its printed counts.~~
      **DONE by `codec-gate-denominators` §1.3/§1.4.** The log line now reads the scope and
      the `def`-docstring claim count as one of its three asserted skip causes
      (`8 def-docstring`), and the header section states which numbers are asserted and
      which are printed-only. A `def` footprint claim is reported as a count, not a silence.
- [x] ~~6.8 **[S] Decompose the classifier's removals per pattern.**~~
      **DONE by `codec-gate-denominators` §1.1/§1.2**, and the tuple is four numbers rather
      than a per-pattern list: `(12 patterns, 54 removed, 6 singletons, 0 uncounted)`,
      printed as:
      `casesOn 8, recOn 8, elim 7, noConfusion 15, noConfusionType 5, ctorIdx 5, ctorElim 1, ctorElimType 1, below 1, brecOn 1, go 1, «term_≫_» 1`.
      `uncounted` was **added** beyond this task and makes `removed + kept = candidateDefs` a checked
      identity. Measured: the six single-name patterns are
      `ctorElim, ctorElimType, below, brecOn, go, «term_≫_»` — note **`eq` is not among
      them**, so this task's parenthetical example was wrong about `eq`.
      The classifier and the audit now read one rule (`derivedDefMatchingPattern`).
- [ ] 6.9 **[S] Extend `constantKindCensus`** to walk `axiomInfo`/`opaqueInfo` **globally**
      and allowlist the 12 known axioms by name. The repo's one authored `opaque`
      (`Codec.Bench.cRefByteMany`) currently sits outside the wire the census built.
- [x] ~~6.10 **[S] Print the projection arm's decomposition.**~~
      **DONE, in the runnable form rather than the proposed one.** The arm prints
      `9 listed of 12 bare projections in the namespaces; the rest are the dec-suffixed three`.
      So the exemption is a number. The task proposed `listed + constant-headed`;
      the implemented split is `listed + suffix-classified`, which is what the code actually
      does — "constant-headed" would describe round nine's own rejected predicate.
- [ ] 6.11 Regenerate the header with `scripts/gen-axioms.lean`, then update the
      `expected*` constants **and** the prose paragraph together. The gate will fail
      loudly until both are done — that is §1.1 working, not a regression.
- [ ] 6.12 Confirm `scripts/gen-axioms.lean`'s output actually matches the committed
      `Axioms.lean` by running it and diffing. Anything that holds a second copy of a name
      list is the round-eight mirror hazard; report every such pair.

## 7. README prose: overclaims and the unadvertised departure [S]

Findings: P-1 (`relRepeat` departure), S-1 (`everything else is kept`), S-2 (`takeWhile`
denotation), P2-4 (porter list), P2-5 (`ignore` ruled out), P2-7 (`isoConsumesByte`
invisible to the proxy), P2-8/9/11/12, N-2/N-4.

- [ ] 7.1 **[M-adjacent] Add the `relRepeat` departure paragraph** to `[S5]`: the `nil`
      branch is `n = 0`, not the paper's `True`; that is what makes
      `relRepeat_induction` an induction on the **list**; `decodeRepeat_spec` is stated
      against this denotation and is unaffected. Add the matching sentence to
      `Codec/Codec.lean:327–334`'s docstring, which currently says "well-founded reading"
      without saying it is a _choice_. Add a "porter will not close the `[]` case"
      warning — that is the actionable half.
- [ ] 7.2 **[S]** `[S6]`'s "Everything else is **kept**" contradicts `[D7]` (`iterate`
      omitted) and `[S2]`/`[D1]` (`token`'s carrier changed). Reword to "Everything not
      listed under a `[Dn]` is kept".
- [ ] 7.3 **[S]** State `takeWhile`'s denotation explicitly in `[D4]`: it relates a
      `List UInt8`, not the paper's `[()]`. That type is the fact a porter needs.
- [ ] 7.4 **[S]** "This is the list a porter must reproduce" → "the `Codec` list", and
      point at `[S1]`'s thirteen `Iso` combinators.
- [ ] 7.5 **[S]** Soften "strict isomorphism rules out `ignore`-shaped constructors": it
      rules out a lossy **`Iso`**; `Codec.pure x` is a lossy `Codec` and inhabits fine.
- [ ] 7.6 **[S]** The `isoConsumesByte`-is-called claim is true of the source and invisible
      to every gate (0 referrers on both channels). Say so, so the next maintainer re-reads
      it by hand rather than trusting a green proxy count.
- [ ] 7.7 **[N]** `birid` → `bidir`; move `findFrom` from the `Sound.lean` row to the
      `ByteSlice.lean` row in the module inventory.
- [ ] 7.8 **[N]** The `Combinators.lean` inventory row claims `sepBy`/`chainl1`/`chainr1`
      symbols; there are none (the module's own header says so).
- [ ] 7.9 **[N]** "`#check @Codec.optional` has no `Nat`" — it does take
      `[DecidableEq α]`, which the sentence omits and which `[D8]` says is an obligation.
- [ ] 7.10 **[N]** Move the `Codec/CRef.c` carve-out into `[S3]` (one sentence), so a
      reader of the "no C that parses" rule finds it in the rule and not 400 lines later.
- [ ] 7.11 **[N]** `Codec/CRef.c:44–48` describes a `none` arm the C does not contain.
      Replace with the fact: there is deliberately no `none` arm because an empty buffer
      decodes to `some []`.

## 8. `AGENTS.md` and `CHANGELOG.md`

- [ ] 8.1 Add this round's lesson to `AGENTS.md`: **"a check is only as good as what
      _enters_ it" has now fired in three layers — the gate (rounds five–eight), the
      **bench** (this round: a fold guard testing `== 0` against a constant `7`), and the
      **prose table** (a cell borrowed from another session's `ns/byte` control). Name all
      three so the pattern is recognisable rather than the instance.
- [ ] 8.2 Correct `AGENTS.md`'s `warningAsError` sentence per 1.8.
- [ ] 8.3 Correct `default.nix:16`, `default.nix:116–118`, `flake.nix:57–58` to name both
      link objects (`byteSliceO`, `cRefO`) — they describe one.
- [ ] 8.4 Correct/qualify `AGENTS.md`'s and README's "the bench checks X" claims per 1.9.
- [ ] 8.5 `CHANGELOG.md`: one entry, naming the withdrawn `77` cell and the two
      docstring corrections, in the register of a _correction_ rather than a feature.

## 9. Gates

- [ ] 9.1 `nix develop --command lake build` — 10 gate lines, zero warnings; record the
      new counts.
- [ ] 9.2 `nix develop --command lake build bench`; then run the binary and paste its
      value-check lines **and** the new spread (min/median/max, round count) for each row.
- [ ] 9.3 `nix develop --command openspec validate --all` — must stay 12+ passed.
- [ ] 9.4 `nix build .#checks.aarch64-darwin.formatting --clear-cache` — the markdown gate.
      **Not `nix fmt`**: this dev shell has no prettier, `nix fmt` formats `*.nix` only and
      reports "0 changed" for markdown it never opened. The check reads the **git tree**, so
      commit first or it cannot see the fix.
- [ ] 9.5 `nix build '.#checks.aarch64-darwin.lean'` — detached with `nohup`, polled, never
      foregrounded.
- [ ] 9.6 Spot-check `#print axioms` on every law this change touched (the docstring edits
      touch none, so this is a regression guard): expect `[propext, Quot.sound]` or empty,
      never `Classical.choice`.

## 10. Recorded, deliberately not in this change

- [ ] 10.1 A tenth review round. This carries round nine's remainder; it does not
      commission more.
- [ ] 10.2 `basen-nat-iso` and `basen-uppercase-prepass` — PARKED by the owner pending the
      library-division decision. Do not touch.
- [ ] 10.3 Cross-repo (`lean-basen`) consistency — out of scope for this round by owner
      instruction. Reviewer B's axis E was explicitly skipped.
