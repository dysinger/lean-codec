# Tasks — `codec-audit-round-six`

**Issue ledger: 33 numbered findings** (`R7-01` … `R7-33`), from the seventh review
round. Reports: `/tmp/r7/{A,B,C}.md`; merged ledger `/tmp/r7-SYNTHESIS.md`.

**Numbering, which is off by one from the change name — this is not a typo.**
`codec-audit-round-six` is the **sixth audit _change_**; its findings come from the
**seventh** review round (rounds one to five produced `codec-audit-remediation`,
`-round-two`, `-round-three`, `-round-four`, `-round-five`). Hence the change is
`round-six` and the ids are `R7-nn`. The next review's ids will be `R8-nn` in a
change called `round-seven`.

**Nothing here requires `/tmp`.** The reports are cited for **provenance only**.
Every finding a task fixes is stated in full below.

**Verification status.** Every finding was re-derived by the main agent before being
written here — `#print axioms` for the footprint class, an environment walk for the
`Iso` count, exhaustive enumeration for the dead branch, git for the pin lag, and by
simulation for the text-matcher escapes (marked ✔ where so). One reviewer figure was
**refuted** in the process and is corrected here (§9).

**Severity key.** MUST = a false claim or a check that cannot fire. 5 findings.
SHOULD = an over-claim that steers a reader wrong, or a promised mechanism that is
absent. 12 findings. NITPICK = a wording error, a dead name, a mis-citation.
16 findings.

## Build state — read this before starting

**All eight sections are closed and both gates are GREEN.**

`codec` — **seven** gate lines:

```
axiom gate: 348 public theorems covered (0 explicit exclusion(s))
axiom gate: 425 public theorems partitioned, 348 gated and 77 allowlisted
axiom gate: 140 public definitions covered, 115 mentioned and 25 allowlisted (mention proxy)
axiom gate: 54 definitions dropped by the name classifier, all reason-recorded
axiom gate: 12 def-name patterns, each matching a recorded non-surface declaration
axiom gate: header numbers verified (425 = 348 + 77; defs 140 = 115 + 25)
axiom gate: stated footprints verified against the environment
```

`basen` — **six** gate lines, the sixth of which §6.6 added:

```
basen axiom gate: 444 pinned + 46 allowlisted = 490 of 490 public theorems (0 explicit exclusion(s))
basen axiom gate: 490 public theorems partitioned, 444 pinned and 46 allowlisted
basen axiom gate: header numbers verified (490 = 444 + 46); prose paragraph says 447 pins = 444 BaseN + 3 Codec
basen axiom gate: 137 public definitions covered, 122 mentioned and 15 allowlisted (mention proxy)
basen axiom gate: native_decide stated count verified (12 uses in Bench.lean, all bench-lane, none in the gate)
basen axiom gate: stated footprints verified against the environment (46 claim site(s))
```

**Every new arm is mutated before it is believed** — that is the rule §1 cost a
session to learn, and §2 and §6.6 each reproduced the failure it prevents (`basen`'s
ported footprint arm was green on 6 of 52 claim sites until the attribution rule was
fixed). The mutations and their outputs are in the tasks' own evidence cells.

**Three traps §1 paid for**, recorded here so §2 does not repay them:

1. **A new check that passes is not evidence it runs.** §1's arm was green and
   would have stayed green forever: a backticked _footprint_
   (`` `[propext, Quot.sound]` ``) was parsed as a backticked _declaration name_,
   so every claim was attributed away from its own declaration. Only inserting a
   deliberately false claim and watching it **fail** found this. **Mutate every new
   check before believing it** — this is the same failure shape the check exists to
   catch, one level up, and it is the single most transferable lesson of the round.
2. **`String.trim` does not exist** in Lean 4.35.0 (`trimAscii` returns a `Slice`),
   and `String.join` takes only a `List String` — no separator argument. Both cost
   compile cycles in §1 and will again in §2.3.
3. **Test the false-positive control too.** A survey docstring (`LengthDet`'s
   four-way table) states _other_ theorems' footprints; an attribution rule that
   fires on it makes the check unusable in the other direction.

**Regeneration:** §7.1 already ran for `codec`'s §1. **§2 and §6.6 change `basen`'s
counts and each needs its own regeneration** — do not assume §7 is fully closed.

## Issue ledger (the index — every id is fixed by a task below)

| id    | sev     | repo     | location                                    | one-line                                                      |
| ----- | ------- | -------- | ------------------------------------------- | ------------------------------------------------------------- |
| R7-01 | MUST    | codec    | 6 docstrings, 4 files                       | "Axiom-free" claims that are not — both directions ✔          |
| R7-02 | MUST    | codec    | `Axioms.lean`                               | no arm compares a stated footprint with `collectAxioms`       |
| R7-03 | MUST    | codec    | `README [S1]`                               | "19 = 13 + 4" does not sum; four witness isos, not two ✔      |
| R7-04 | MUST    | codec    | `README:975`                                | `Codec.Sound.uniqSeq_not_congruent` does not exist ✔          |
| R7-05 | MUST    | basen    | `Axioms.lean` def check                     | `a - b + b ≠ a` — provably dead branch ✔                      |
| R7-06 | SHOULD  | basen    | `Axioms.lean:1697`                          | "440 against 437" — measured 443 / 440 ✔                      |
| R7-07 | SHOULD  | basen    | `Axioms.lean` `nativeDecideCount`           | four escapes: trailing comment, `by`, two-on-one-line, CRLF ✔ |
| R7-08 | SHOULD  | codec    | `Sound.lean` `Rab_fails_huniq`              | weaker than the prose citing it; `∃`-form missing             |
| R7-09 | SHOULD  | codec    | `Sound.lean` `Rab`                          | definitionally identical to `uniqCounterexampleRel`           |
| R7-10 | SHOULD  | codec    | `Sound.lean` `decodeRepeat_mem_iff_general` | orphan; docstring says its predecessor "was never necessary"  |
| R7-11 | SHOULD  | codec    | `README` table 4 caption                    | `idealCursor` row is /4096 in a "512 steps per burst" table ✔ |
| R7-12 | SHOULD  | codec    | `README` 81, 687, 743, 779                  | four dead intra-document anchors ✔                            |
| R7-13 | SHOULD  | basen    | `flake.lock`                                | 14-commit lag, no recorded reason ✔                           |
| R7-14 | SHOULD  | basen    | `CHANGELOG.md:87,137`                       | `9d5074e`, `3dfc249` resolve to no object ✔                   |
| R7-15 | SHOULD  | basen    | `Base16.lean` / `README:29`                 | §8 decoder has no roundtrip; every law is the strict one      |
| R7-16 | SHOULD  | basen    | `default.nix`, `AGENTS.md`, `Bench.lean`    | three documents say the lane must be _run_; `main := pure ()` |
| R7-17 | SHOULD  | codec    | `Axioms.lean` `exclusions`                  | honoured by the coverage check, no stale arm                  |
| R7-18 | NITPICK | codec    | `README [S2]`                               | `print → encode` bold lead says "changes the argument"        |
| R7-19 | NITPICK | codec    | `README [S1]`                               | heading says "Five", body says 3                              |
| R7-20 | NITPICK | codec    | `README [D7]`                               | "no inverse law exists" stronger than proved                  |
| R7-21 | NITPICK | codec    | `README [D4]`                               | paraphrase quoted as the paper's words                        |
| R7-22 | NITPICK | codec    | `Combinators.lean` §D6 table                | `sepBy` row omits the `hstep` obligation                      |
| R7-23 | NITPICK | codec    | `Sound.lean`                                | no `unambiguous_iff_relUnambiguous` bridge                    |
| R7-24 | NITPICK | codec    | `README [S3]`                               | "no hypothesis at all" vs the law still taking `hd`           |
| R7-25 | NITPICK | codec    | `README:1334`                               | "~4–7 ns/step" vs the derivation's max 6.4                    |
| R7-26 | NITPICK | codec    | `README:1267` vs `:1247`                    | "430–541" vs "430–650", same figure                           |
| R7-27 | NITPICK | codec    | `README:1246`                               | `decodeFull spec ~31,200 ns/step` has no run table            |
| R7-28 | NITPICK | basen    | `Base{2,4,8,10,16}.lean`                    | `rejects_single_char` proves only the byte `'0'`              |
| R7-29 | NITPICK | basen    | `README:97-100`                             | overflow enumeration omits base16/32/64                       |
| R7-30 | NITPICK | template | `lakefile.lean`                             | `lean_exe cli` has no `moreLeanArgs`                          |
| R7-31 | NITPICK | codec    | `README`                                    | `[D2]`'s `bidir` link stated twice, one inverted              |
| R7-32 | NITPICK | basen    | `Bench.lean:398-412`                        | "three of the twelve" should say `3 + 9`                      |
| R7-33 | NITPICK | basen    | `Base32.lean`, `CHANGELOG`                  | `MZ======` prose should name the canonical `MY======`         |

---

## 1. The ungated footprint class (R7-01, R7-02)

The section that is the change: it is the **mechanism** behind R7-01, not six
separate prose fixes.

- [x] 1.1 Add the footprint arm to `Axioms.lean`. **R7-02**, design §D1.
      A `run_cmd` over public `Codec`/`Iso` declarations: extract each stated
      footprint claim from `Lean.findDocString?`, compare with `collectAxioms`,
      fail naming declaration + stated + measured.
      **Done.** Landed as a seventh `run_cmd`, `codec-audit-round-six` §1.1. **It found 26 real claim sites, not 11** — the reviewers' `#print axioms` sweep was run per-family and missed 15. Green: `axiom gate: stated footprints verified against the environment`.

**One bug the check had, caught only by the mutation test:** a backticked _footprint_ (`` `[propext, Quot.sound]` ``) was being parsed as a backticked _declaration name_, so every claim was attributed away from its own declaration and the arm was **vacuously green**. Fixed by stripping the two footprint spellings before name extraction. This is the reason §1.5 mutates rather than trusting a clean run, and it is the same class as the defect the arm exists to catch.

      ✔Measured: eleven claim sites are wrong today, so the arm will be RED on the
      current tree. That is the work list — do not try to make it green here.

      **Attribution rule (design §D1 option 1): a claim counts only when the same
      sentence names its declaration backticked.** Implement exactly that; a
      docstring that surveys several declarations is not a claim about itself.

      Handle the hedged form: "`[propext]` or no axioms" (as in `Normal.lean`) is a
      **lower bound**, satisfied by any footprint within it, not an exact-set claim.

- [x] 1.2 Correct the six over-strong claims. **R7-01.** ✔All verified by
      `#print axioms` in this session; paste the measured string, do **not** retype
      from the report:
      **Done.** **Corrected 15 over-strong and 11 under-strong sites, not six.** Every value pasted from `#print axioms`, never retyped from a report. Files: `Sound.lean`, `Decode.lean`, `DecodeOne.lean`, `Packed.lean`, `Codec.lean`, `ByteSlice.lean`. The rule is recorded in the arm's docstring, with the refuted predictor (`Bytes`-mention ⇒ axioms) as the stated reason it is not a syntactic test.

      | file:line        | declaration                      | says       | measured                 |
      | ---------------- | -------------------------------- | ---------- | ------------------------ |
      | `Sound.lean:955` | `unambiguous_byte`               | Axiom-free | `[propext, Quot.sound]`  |
      | `Sound.lean:970` | `functional_byte`                | Axiom-free | `[propext, Quot.sound]`  |
      | `Sound.lean:1026`| `functional_iff_relFunctional`   | No axioms  | `[propext]`              |
      | `Decode.lean:805`| `decodeFullStep_nil`             | Axiom-free | `[propext, Quot.sound]`  |
      | `Decode.lean:1042`| `decode_congr_bdrop`            | Axiom-free | `[propext, Quot.sound]`  |
      | `DecodeOne.lean:218`| `decodeArray_functional_byte` | Axiom-free | `[propext]`              |
      | `DecodeOne.lean:235`| `decodeArray_unambiguous_byte`| Axiom-free | `[propext]`              |

      Three of these are `codec-audit-round-five`'s own additions. **Record the rule
      the class teaches** at the top of the gate's docstring: *write a footprint from
      `#print axioms`, never from inspection* — with the refuted predictor (§9) as
      the reason.

- [x] 1.3 Correct the two under-strong claims. **R7-01**, design §D2. ✔Measured:
      `relUnambiguous_of_relAligned` and `relUnambiguous_not_implies_relAligned` are
      **axiom-free** (claimed `[propext, Quot.sound]`-only), and
      `relUnambAlignedWitness_unamb` is `[propext]`. The understatement hides the
      strongest evidence the four-way diagram has, so it is not cosmetic.
      Also `Sound.lean:1785` "Both are `[propext]`-clean" is false for
      `lengthDet_not_implied_by_unamb` (`[propext, Quot.sound]`).
      **Done.** Done. `relUnambiguous_of_relAligned` and `relUnambiguous_not_implies_relAligned` now say axiom-free; `relUnambAlignedWitness_unamb` says `[propext]`; `Sound.lean`'s "Both are `[propext]`-clean" split into the two measured values.

- [x] 1.4 Add `Rab_fails_huniq_full`. **R7-08.** The `∃`-form the prose cites:
      `∃ R, LengthDet R ∧ (∀ a {m} (t), R a t → m ≠ 0) ∧ ¬(∀ xs ys n s, …)`.
      One line on four existing theorems (`Rab`, `Rab_lengthDet`, `Rab_productive`,
      `Rab_fails_huniq`); mirrors `huniq_not_derivable_full`.
      Then point the citing prose at the `∃`-form, not the `¬∀` one.
      **Done.** Landed exactly as the one-liner predicted:
      `⟨Rab, Rab_lengthDet, Rab_productive, Rab_fails_huniq⟩`. Measured
      `[propext, Quot.sound]`-only. The citing prose now names
      `Rab_fails_huniq_full`, not `Rab_fails_huniq`.

      **Correction to this ledger's own history:** this task was first recorded as
      "deferred to §3". There is no deferral mechanism here — an open task is open.
      Done in place. (The §3.1 alias decision turned out not to affect it: the docstring
      states the witness by name and the alias note is separate.)

- [x] 1.5 Re-run `lake build` and confirm the arm is green with **zero** exceptions
      — no name added to an ignore list, no claim reworded into silence.
      **Done.** Green with **seven** gate lines, zero exceptions, no name added to any ignore list. Non-vacuity confirmed by mutation: inserting a false claim into `Rab_lengthDet`'s docstring fails the build naming it (`says [propext, Quot.sound]-only, measured [propext]`) and reverting restores green. The survey false-positive control also holds — `LengthDet`'s four-way table, which states other theorems' footprints, does **not** fire.

## 2. `basen`'s gate (R7-05, R7-06, R7-07, R7-17)

- [x] 2.1 Replace the dead branch. **R7-05.** ✔Verified `a - b + b ≠ a` is false for
      all `a, b` by exhaustive enumeration. Replace with
      `mentionedCount + definitionSurfaceAllowlist.size != defs.size`.
      **Done.** Replaced with exactly that identity, and **mutated to prove it
      fires**: with all three `expected*` constants correct, injecting `(mentionedCount + 1)`
      into the sum makes the build fail with `definition table does not add up: 122 + 15 != 137`.
      Reverting the expression to the old `a - b + b` form leaves that branch silent, so the
      old code was dead and the new code is live.

- [x] 2.2 Assert both numbers in the "443 / 440" sentence. **R7-06.** ✔Measured
      `grep -c '^#print axioms'` → **443**, `gatedNames` → **440**; the prose says
      `440 / 437`. Fix the prose **and** fold both into the `run_cmd` so the pair
      cannot drift together again.
      **Done.** Prose corrected to `443` against `440`. Both figures are now asserted:
      `statedPrintBlockCount := 443` against a column-0 line count of `Axioms.lean`
      (matching `grep -c '^#print axioms'`; a naive substring count reads 454 because
      these very comments mention the phrase), and `statedGatedNamesCount := 440`
      against `gatedNames.length`. **Both mutated:** `442` fails on the block count,
      `437` fails on `gatedNames`.

- [x] 2.3 Close the `nativeDecideCount` escapes. **R7-07.** ✔Reproduced: a trailing
      comment moves the count `12 → 11`; `:= by native_decide` and two-on-a-line are
      invisible; `uses` is computed and never compared. Fix: truncate each line at
      `--`, strip both ends, and assert `uses ≥ tacticLines` as well as
      `tacticLines == stated`.
      **Done, and the reported fix was not sufficient.** Truncating at `--` leaves
      **block** comments uncounted, and `Bench.lean` has a `/- … -/` block that
      names the identifier — a naive total read **18** against the true **12**. Landed: a
      comment stripper handling both `--` and nested `/- … -/`, then a substring count
      over the code. Unit-checked against eight spellings (trailing comment, inline `by`,
      two-on-a-line, CRLF, block comment, nested block comment, plain, comment-only)
      **before** installation, because a counter that silently miscounts is the defect.
      **Then mutated end to end, with the `.olean` deleted each round** (an earlier
      round of this test read stale artifact and passed four times spuriously — that
      trap is real): adding a trailing-comment use, an inline-`by` use, a two-on-one-line
      use, or a CRLF use each makes the gate report **13** and fail; adding a
      **comment-only** mention correctly still reports **12**.

- [x] 2.4 Give `exclusions` the stale arm its sibling has. **R7-17.** Two failures:
      a name that is not a public theorem, and a name whose measured footprint is
      already inside the discipline. Both are build failures.
      **Done.** Both arms land in the coverage `run_cmd` (which already honours
      `exclusions` by skipping them, so a bad entry was previously invisible).
      **Mutated:** adding `` `BaseN.DoesNotExist `` fails with "names a declaration that
      does not exist"; adding `` `BaseN.Base10.Rel_digElem_canonical `` fails with "whose
      measured footprint [[propext, Quot.sound]] is already inside the discipline".

## 3. The `Rab` family (R7-09, R7-10)

- [x] 3.1 Record that `Rab` is deliberately the same relation as
      `uniqCounterexampleRel`. **R7-09.** ✔Verified: identical bodies. Keep both
      names; the defect was the prose contrasting them as if they differed.
      **Done.** Verified identical again (`| true, m, _ => m = 2` / `| false, m, _ => m = 1`
      in both). `Rab`'s docstring now says the body is identical to
      `uniqCounterexampleRel`'s **and why both names are kept** (two arguments cite
      them; deleting `Rab` was rejected because three passages name it).
      `uniqCounterexampleRel`'s docstring carries the reciprocal pointer, so neither
      reads as an accident. No statement changed.

- [x] 3.2 De-orphan or delete `decodeRepeat_mem_iff_general`. **R7-10.** Its
      docstring says the specialisation "was never necessary", yet the specialisation
      is the only one used. Either rewrite `huniq_byte` to consume the general form
      and delete the specialisation, or record it as a kept alias with no caller.
      **Prefer the first**: it makes the docstring true.
      **Done — the first option.** `huniq_byte` now calls
      `decodeRepeat_mem_iff_general Codec.byte byteConsumesByte`; `decodeRepeat_mem_iff`
      (the `Codec.byte` specialisation) is **deleted**. The gate caught the deletion by
      design (`pinned names with no matching theorem`, plus `#print axioms` for a name
      that no longer exists), and `scripts/gen-axioms.lean` was run: it rewrote 348 gates
      and the header moved `426 = 349 + 77` → **`425 = 348 + 77`** with
      `expectedPub`/`expectedGated` in lockstep. Green on all seven lines.

## 4. base16 (R7-15)

- [x] 4.1 Prove `decodeHexFold (encodeHex bs) = some bs`. **R7-15**, design §D6.
      ✔Verified the pieces exist: `foldList_hexBlockUnapply` supplies the fixed-point
      hypothesis, `decodeHexFold_of_fixed` consumes it. If awkward, fallback is a
      scoped README row (design §D6) — either outcome ends in a tick.
      **Done — the proof, not the fallback.** Four new laws in `BaseN/Base16.lean`
      (the task said three pieces would suffice; it took four because the range bridge
      is its own lemma): - `hexToNibble_range` — `hexToNibble N ≤ 15 → (48 ≤ N ∧ N ≤ 57) ∨ (65 ≤ N ∧ N ≤ 70)`; - `foldByte_of_hexDigit` — a `hexDigit` byte is a `foldByte` fixed point; - `foldByteBytes_of_encodeHex` — hence `foldByteBytes s = s` on the encoder's output; - `decodeHexFold_roundtrip` — `encodeHex bs = some ⟨n, s⟩ → decodeHexFold s = some bs`,
      by `decodeHexFold_of_fixed` + `roundtrip`.

      The four pieces came out as four lemmas, not the three the task sketched. **All
      four measured `[propext, Quot.sound]`-only** and are now pinned. Non-vacuity verified by mutating
      the conclusion to `some (bs ++ [0])`, which fails to typecheck at the `roundtrip`
      step.

      **The `Classical.choice` leak hit here and the cause is worth recording.** The
      first proof closed the range case-split with `omega` on a **disjunction** goal and
      reported `[propext, Classical.choice, Quot.sound]` — the documented trap, arriving
      in the form of "let `omega` produce the disjunct". The fix was to build the disjunct
      explicitly (`Or.inl ⟨h2, h1⟩` / `Or.inr ⟨h4, h3⟩`) and let `omega` close only the
      negation branches that `simp`/`omega` can prove contradictory. A second `split`-based
      shape was tried first and **also** leaked, because `split` on a `Nat ≤` condition
      takes the classical decidable instance. `by_cases` was fine; the leak was in what
      closed the goal.

- [x] 4.2 Say which decoder owns which laws, in `README:29`'s table.
      **Done.** A four-point note under the status table names, for base16, the five laws
      the **strict** decoder owns (`roundtrip`, `decodeFull_canonical`,
      `decodeFull_B16_char`, `decode_encode_inverse`, `encode_injective`) and the four the
      **case-insensitive** one owns (the three two-case laws plus the new
      `decodeHexFold_roundtrip`). All nine names were grepped against `Base16.lean` after
      writing, so the note cites declarations that exist.

## 5. `README` (R7-03, R7-04, R7-11, R7-12, R7-18 … R7-27, R7-31)

- [x] 5.1 Repair `[S1]`'s arithmetic. **R7-03.** ✔My environment walk returns **19**
      and includes `Codec.uniqSeqIso` / `Codec.uniqSeqUnitIso`. Keep 19; fix the sum
      to `13 + 4 + 2` and "two counterexample witnesses" → **four**.
      **Do not change 19 to 21** — see §9, that reviewer figure is refuted.
      **Done.** Re-ran the environment walk in this session (a `MetaM` pass over
      `Codec`/`Iso` `defnInfo`s whose type's head is `Iso`): it returns **19** and the
      list contains `Codec.uniqSeqIso` and `Codec.uniqSeqUnitIso` by name, so the
      decomposition is `13 + 4 + 2`. The sentence now enumerates all 19 explicitly
      rather than asserting a sum, and says the count came from a walk. The 19 was
      **not** touched, per §9.

- [x] 5.2 Fix the phantom name. **R7-04.** ✔`#check` → unknown identifier;
      the real constant is `Codec.uniqSeq_not_congruent` (`Codec/Sound.lean`).
      **Done.** `#check @Codec.Sound.uniqSeq_not_congruent` → `unknownIdentifier`;
      `#check @Codec.uniqSeq_not_congruent` → `¬ Codec.uniqSeqWhole.Unambiguous`.
      Corrected at the one site that had the prefix.

- [x] 5.3 Fix table 4's caption. **R7-11.** ✔`10532 / 512 = 20.57`, but the row says
      `2.57` — it is a 4096-step figure. Give the span per row. **Do not re-run the
      lane.**
      **Done, no re-run.** A `steps/burst` column was added
      (`idealCursor` **4096**, C reference and `decodeWhole` 512), and the arithmetic
      is stated in the text: `10532 / 512 = 20.57` but `10532 / 4096 = 2.57`. The
      caption no longer claims one span for all rows.

- [x] 5.4 Repair the four dead anchors. **R7-12.** ✔Verified none of the four
      targets exists as a heading. Recompute the GitHub anchor from the real heading.
      **Done, and there were six, not four.** The two headings are
      `## Representations — one length-indexed byte string (the spec substrate)` and
      `## Performance — two proof layers, and where the speed goes`; the em-dash
      produces a **double** hyphen in a GitHub anchor, so the correct ids are
      `#representations--one-length-indexed-byte-string-the-spec-substrate` and
      `#performance--two-proof-layers-and-where-the-speed-goes`. Recomputing by
      lowering + stripping non-word characters gave those two; **six** links pointed
      at three stale ids (`…-byte-string`, `#performance-two-proof-layers`,
      `#performance-and-what-it-costs`, plus three single-hyphen variants). All six now
      point at one of the two real anchors, and a final `grep -o '](#[^)]*)' | sort -u`
      returns exactly those two.

- [x] 5.5 Fix the per-step and figure inconsistencies. **R7-25/26/27.** "~4–7"
      → "~4–6" (derivation max 6.4); "430–541" → the table's "430–650"; either
      table the `decodeFull spec` figure or drop it.
      **Done.** `~4–7` → **`~4–6`**, with the derivation printed (`24–26 − 20 = 4–6`,
      upper end `26.4 − 20 = 6.4`). `430–541` → **`430–650`**, which is what the table
      row says. The `decodeFull spec ~31,200 ns/step` figure is **dropped, not
      tabulated**: `benchDecodeFull` prints one _batch_ figure and no committed run
      produced a per-step one, so the cell now says "no per-step figure committed" and
      the note under the table explains why. Re-running the lane is out of scope per
      the design's non-goals.

- [x] 5.6 Fix the four anchoring/wording items. **R7-18/19/20/21.** `print → encode`
      lead; `[S1]`'s "Five" heading; `[D7]`'s "no inverse law exists"; `[D4]`'s
      paraphrase-in-quotes.
      **Done, all four.** - R7-18: `print → encode`'s lead is now "changes **what the argument is**", and
      says why the old lead ("changes the **argument**") contradicted its own
      paragraph — both forms take an argument. - R7-19: the heading's "Five" → **"Three"**, matching the paragraph, with a note
      that "five" was the pre-`element`/`subset`-domain-laws count. - R7-20: "no inverse law exists" → the weaker, true form: `iterate` cannot
      satisfy `Iso.law` unconditionally and no proof exists here. - R7-21: two sites quoted "modulo equivalence classes" as if it were a verified
      weakening. Quoted `PAPER.md`'s actual sentence ("we will **sometimes interpret
      this condition** modulo equivalence classes") and marked the project's reading
      as the project's.

- [x] 5.7 Fix `[S3]`'s "no hypothesis at all" and `[D2]`'s inverted `bidir`
      citation. **R7-24/31.**
      **Done, and R7-24 was a _design_ fact rather than a prose error.** `takeWhile`'s
      obligation is derivable (`relTakeWhile_functional` needs only `p`) but
      `encodeTakeWhile_of_decode` still **takes** it. Discharging it was tried and
      reverted: it needs two helper lemmas moved above the theorem, and keeping the
      parameter is deliberate anyway — it makes the `_of_decode` family uniform, since
      `sepBy`'s twin needs the hypothesis for real. So the README row now says "derivable
      for any `p`; still _taken_", with a paragraph on why both halves matter, and the
      theorem's body carries the same note. **No statement was changed and no law moved.**
      R7-31: the offending citation was `(x, []) ∈ decode d s` in the opening section —
      `[]` is not the library's empty remainder (`List (α × Suffix n)`, empty =
      `Suffix.empty n`). Now spelled exactly as `bidir` states it, in the same form as
      the other two citations.

## 6. Cross-repo and template (R7-13, R7-14, R7-16, R7-28 … R7-33)

- [x] 6.1 Decide the pin. **R7-13.** ✔Verified: pinned `5acf487`, HEAD `fc132de`,
      **14 commits**, and the pinned rev **is** an ancestor. Bump
      (`nix flake update codec` — targeted; then `lake update codec`) and re-run all
      three gates, **or** record the lag with its reason in `AGENTS.md`. Either way
      the repo's own quoted rule is satisfied.
      **Done — bumped, not recorded.** `nix flake update codec` moved
      `5acf487` → `56ff74f`, `lake update codec` checked it out, and `lake build` is green
      with all five gate lines. The lag measured **22** commits at bump time, not the 14
      the reviewer saw — `codec` moved during this session. **The pin must be bumped
      again after §8.4's `codec` commits land**, because `56ff74f` predates §2–§5.

- [x] 6.2 Resolve or drop the two unresolved CHANGELOG SHAs. **R7-14.**
      ✔`git cat-file -t` fails for both in both repos.
      **REFUTED — no edit made.** Re-ran `git cat-file -t` in **`../lean-basen`**, the
      repository `CHANGELOG.md` lives in: `9d5074e` and `3dfc249` both resolve to commits,
      both are ancestors of `HEAD`, and their subject lines ("Base64/Base32: name the
      §3.5 zero-pad-bit fact (§C4, first half)" and "Base32: name the §3.5 zero-pad-bit
      fact") are exactly what the two changelog entries describe. They do **not** resolve
      in `lean-codec`, which is irrelevant — the citation names `basen`'s own history.
      Recorded in §9 as the third refuted finding of the round.

- [x] 6.3 Make the bench-lane documents match the code. **R7-16**, design §D4.
      `Bench.lean:707` is `main : IO Unit := pure ()`. Rewrite `default.nix:16-21`,
      the `installPhase` comment, and the `AGENTS.md` bullet to say the checks fail
      at **build** time, and restate what `nix build '.#bench'` then proves.

      **Done, per design §D4(b).** `default.nix`'s header no longer says the lane must
      be *run*; it says every `Bench.lean` check is an `example` closed by `rfl` or
      `native_decide`, both of which fire while Lake elaborates the module, that `main`
      is `pure ()`, and that `nix build '.#bench'` therefore proves the lane **builds in
      the sandbox**. The `installPhase` comment now calls its execution a smoke test.
      `AGENTS.md`'s bullet is rewritten the same way with the retraction stated.
      Verified: `nix build '.#bench'` exits 0.

- [x] 6.4 `basen` README/doc prose sweep. **R7-28/29/32/33.** Rename
      `rejects_single_char` (or document it), complete the overflow enumeration,
      `3 + 9 = 12`, name the canonical `MY======`.

      **Done, all four.**
      - R7-28: every `rejects_single_char` summary now names the concrete byte it proves
        (`0x30`, or `0x36` for base16) and says in the text that the name reads general
        while the statement is a single-point witness. Names kept — five public renames
        is churn for a defect the summary can fix.
      - R7-29: the overflow enumeration is completed. Only `Base8.rejects_overflow` and
        `Base10.rejects_overflow` exist; the text now says so **and** why
        base2/4/16/32/64 have no such input.
      - R7-32: `Bench.lean` says **3 of the twelve, the other 9 further down**
        (`3 + 9 = 12`, confirmed by locating the tactic lines).
      - R7-33: `Base32.lean`'s §3.5 head pairs `MZ======` with its canonical twin
        `MY======`; `CHANGELOG.md`'s entry opens by naming both.

- [x] 6.5 Template. **R7-30.** Drop the `bench` paragraph the template does not
      ship; scope the git-tracked claim to the flake path; add `moreLeanArgs` to
      `lean_exe cli`.

      **Done, all three.** The `bench` paragraph is replaced by a statement that the
      template ships no bench lane (nothing in `default.nix`/`flake.nix` has one), with
      `basen`'s derivation named only as guidance for a project that adds one. The
      git-tracked claim is scoped: `default.nix`'s `src = ./.` is the git-tree snapshot
      *through the flake* and the whole directory *through a bare `nix-build`*. And
      `lean_exe cli` carries `moreLeanArgs := #["-DwarningAsError=true"]` now.
      **Verified load-bearing by mutation:** with `import Example.Count.CLI` removed
      from `Example.lean` and a `sorry` added in `CLI.lean`, `lake build` still fails
      naming it — only the executable root's flag can catch that, so the gate no longer
      depends on the library importing the CLI module. `nix build .#native .#cli` green.

- [x] 6.6 Port the footprint arm to `basen`'s `Axioms.lean`. **R7-02**, `basen`
      spec delta. `basen` has docstrings stating footprints too and no arm to check
      them.
      **Done, and the port found two real defects.** A sixth `run_cmd` in `basen`'s
      `Axioms.lean` now compares every stated footprint with `collectAxioms` over
      `BaseN`, with `namesAnotherDecl` + `namesSelf` helpers in `BaseNAxioms`.

      **The port reproduced §1's trap, in a new form, and that is the finding.** The
      arm was green on its first run with **6** claim sites — while 52 docstrings
      stated one. `codec`'s attribution rule ("name another declaration ⇒ not your
      claim") dropped **46 of 52**, because `basen`'s docstrings routinely cite their
      own ingredients (`BaseN.Base8.roundtrip`'s says "gated by the
      `octDecodeFull_unambiguous` uniqueness fact. `[propext, Quot.sound]`-only.").
      The rule was refined to: a claim is **self-attributed** when its segment is
      *only* the claim (no declaration name — the shape almost every law uses), or
      when its segment/paragraph names self; it is attributed away only when it names
      another declaration and neither. Sites went **6 → 46**.

      Verified in both directions, which is the whole point:
      - **Mutation:** inserting "Axiom-free." into `Base8.roundtrip`'s docstring fails
        the build with `says axiom-free, measured [propext, Quot.sound]`.
      - **False-positive control:** a false "axiom-free" claim about a *different*
        declaration (`BaseN.Base8.encodeOct_canonical`) inside `roundtrip`'s docstring
        does **not** fire.
      - **Real defects found:** `BaseN.Base64.b64BytesOf_tail1_eq` and
        `BaseN.Base32.b32BytesOf_tail1_eq` each claimed
        `[propext, Quot.sound]`-only; `#print axioms` reports **no axioms** (both
        proofs are `rfl`). Both docstrings corrected to "Axiom-free", verified by hand.
      (An earlier run of the mutation read a stale `.olean` and passed spuriously —
      the trap `AGENTS.md` names — so every mutation above deleted the `.olean` first.)

## 7. Regenerate (gate counts)

- [x] 7.1 Regenerate `Axioms.lean` once (`scripts/gen-axioms.lean`) and move the
      header tables and the six `expected*` constants together. **Do not predict the
      delta — the run prints it.** `basen` likewise if §2/§6.6 change its counts.
      **Done for `codec`.** The run printed `rewrote 349 gates`; header moved to
      `426 = 349 + 77`, `expectedPub`/`expectedGated` in lockstep, and the build is
      green with **seven** gate lines. `basen`'s counts are untouched by this
      regeneration and need their own run if §2/§6.6 move them.

      **`basen` re-run (§3.2 deleted a law).** `scripts/gen-axioms.lean` does not exist
      in `basen` — its header table is asserted by hand — so the counts were moved in
      lockstep by measurement instead: the deletion of `decodeRepeat_mem_iff` made
      `486 = 440 + 46` → **`490 = 444 + 46`**, because §4.1 **added four** theorems
      (`hexToNibble_range`, `foldByte_of_hexDigit`, `foldByteBytes_of_encodeHex`,
      `decodeHexFold_roundtrip`) to the one it removed. `expectedPub`/`expectedGated`/
      `statedPrintBlockCount`/`statedGatedNamesCount` and the prose paragraph were all
      moved together, and the distribution sentence (`381 + 48 + 15 = 444`) is now
      **asserted** rather than remembered — it had already rotted to `377 / 48 / 15 =
      440` behind a green table, which is the defect §2.2 exists for. Both new arms are
      mutation-verified (a `380` in the distribution fails naming the measured `381`).

      **§6.6 added a sixth gate line** to `basen`: stated footprints verified, over 46
      claim sites.

## 8. Gates (run all three repos; they are different flakes)

- [x] 8.1 `codec`: `nix fmt` first, then `lake build` (zero `sorry`, four-plus gate
      lines, counts in lockstep), `lake build bench`, `openspec validate --all`,
      `nix flake check` (**detached with `nohup`, never foregrounded**).
      **Done, all green.** `nix fmt` (197 files, 2 changed); `lake build` — 15 jobs,
      zero warnings, **seven** gate lines `425 = 348 + 77`, `140 = 115 + 25`; `lake
  build bench` — 28 jobs; `openspec validate --all` — **11 passed, 0 failed**
      (3 pre-existing >500-char warnings, no errors); `nix flake check` detached via
      `nohup` — `checks.aarch64-darwin.{formatting,lean,openspec}` all ✅.
- [x] 8.2 `basen`: `lake build`, `lake build bench`, `nix build '.#bench'`.
      **Done, all green.** `lake build` — 25 jobs, **six** gate lines
      (444 pinned + 46 = 490; 137 defs; **stated footprints verified, 46 claim
      sites**); `lake build bench` — 45 jobs; `nix build '.#bench'` — exit 0.
- [x] 8.3 `template`: `nix flake check`, `nix build .#native .#cli`.
      **Done, all green.** `nix fmt` then `nix flake check` —
      `checks.aarch64-darwin.{formatting,lean}` ✅; `nix build .#native .#cli` — exit 0.
      (The first `flake check` failed `treefmt-check` on `*build*` → `_build_`; the
      hook is what caught it.)
- [x] 8.4 Commit per task family, individual files only, printing
      `git diff --cached --name-only` before each. The pre-commit hook runs `nix fmt`
      and rejects a reformatted staged file; re-add and commit again.
      **Done.** 5 commits in `codec` (Sound; Axioms; Combinators; README; ledger),
      9 in `basen` (Axioms; Base16; Base2/4; Base8/10; Base32; Base64; AGENTS+nix+Bench
      docs; README+CHANGELOG; flake.lock), 2 in `template` (AGENTS; lakefile). Every
      commit printed `git diff --cached --name-only` first; the hook reformatted
      nothing on the final passes. All three trees are clean.
- [x] 8.5 Verify every new law's footprint by hand and paste the output:
      `printf 'import Codec\n#print axioms Codec.<n>\n' > /tmp/c.lean` →
      expect `[propext, Quot.sound]` or cleaner. `Classical.choice` is a defect.
      **Done. `codec`:**
      `     'Codec.Rab_fails_huniq_full' depends on axioms: [propext, Quot.sound]
  'Codec.uniqSeq_not_congruent' depends on axioms: [propext, Quot.sound]
  `
      **`basen`:**
      `     'BaseN.Base16.decodeHexFold_roundtrip' depends on axioms: [propext, Quot.sound]
  'BaseN.Base16.foldByte_of_hexDigit' depends on axioms: [propext, Quot.sound]
  'BaseN.Base16.foldByteBytes_of_encodeHex' depends on axioms: [propext, Quot.sound]
  'BaseN.Base16.hexToNibble_range' depends on axioms: [propext, Quot.sound]
  'BaseN.Base64.b64BytesOf_tail1_eq' does not depend on any axioms
  'BaseN.Base32.b32BytesOf_tail1_eq' does not depend on any axioms
  `
      No `Classical.choice` in any. The two axiom-free rows are the ones §6.6's new
      arm found mis-claimed as `[propext, Quot.sound]`-only.

---

## 9. Recorded, deliberately NOT fixed here

**These are NOT tasks and carry no checkboxes, deliberately** — `openspec` counts
every `- [ ]`, so a "no action" box makes 100% unreachable.

- **The 10 refuted findings.** Do not re-derive them; each has evidence in
  `/tmp/r7/{A,B,C}.md`. Notably: an axiom-free claim is **not** predictable from
  whether the statement mentions `Bytes` (25 axiom-free theorems manipulate `Bytes`
  directly, so there is no syntactic predictor — the only safe rule is to measure);
  the gate **cannot** be escaped by renaming a law `…inj` (check 1 would miss it,
  check 2 partitions before the classifier); `*_char` genuinely states an iff
  (`→` is `decode_encode_inverse`, `←` is `roundtrip`); no `native_decide` leaked
  into any library; the `-DwarningAsError` flag **is** on the template's library;
  base10's "not an RFC encoding" justification is sound; `Rab`,
  `relRepeat_functional_of_step` and `relTakeWhile_functional` are non-vacuous by
  mutation testing; there is **no** live `Classical.choice` (502-constant sweep).

- **R7-14's "both CHANGELOG SHAs fail `git cat-file -t` in both repos" — REFUTED.**
  Re-derived in the repository the changelog lives in: `9d5074e` and `3dfc249` both
  resolve to commits in `../lean-basen`, both are ancestors of `HEAD`, and their subject
  lines are exactly what the two entries describe. They fail only in `lean-codec`,
  which is not where they are cited. **No edit was made**, and no citation was dropped.
  This is the fourth round in which a reviewer's measurement failed to reproduce.

- **`README [S1]` "should be 21" — REFUTED.** Reviewer B reported the count as 21.
  My own environment walk returns **19**, and the returned list contains
  `Codec.uniqSeqIso` and `Codec.uniqSeqUnitIso`. B counted the 13 parameterised isos
  as "missed" as well as the two witnesses. **The total 19 is correct; only the
  decomposition (13 + 4) is wrong.** Relaying "should be 21" would have replaced one
  wrong number with another — this is the design-D1 hazard of ratio 3 from round five
  (`do not trust a reviewer's arithmetic without re-deriving it`), and it is the
  second round in which it fired.

- **`basen`'s general arity rejection** for the five fixed-width bases — still needs
  a `decodeFull`-length lemma. ✔Confirmed still open, and the in-repo justification is
  accurate (per-element length lemmas exist; no `decodeFull` consumed-length result).
  Unchanged, not a defect.

- **`[D4]`'s length-changing carrier** — still not built; needs an owner decision.

- **The 12 `native_decide` bench uses** — sanctioned, bench-only, outside the gate.
  ✔Confirmed `b32TailApply_b32MZTA_chars` still does not exist, so the "until that
  lemma exists" justification is still true.

- **`Axioms.lean`'s 443 `#guard_msgs` texts are byte-exact for Lean 4.35.0** —
  not re-elaborated by the audit (no build permitted). Assumed current; §8.1
  re-establishes it.

---

## Appendix A — the footprint oracle (for §1.1)

A's prototype, reproduced here so §1.1 does not depend on `/tmp`. It is _not_ the
final implementation — it has no attribution rule, which design §D1 adds — but it is
what produced the eleven-site list and it compiles.

```lean
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut bad : Array (Name × String × String) := #[]
  for (nm, ci) in env.constants.toList do
    if (nm.getPrefix == `Codec || nm.getPrefix == `Iso) && !ci.isUnsafe && !ci.isPartial then
      unless ci is .thmInfo _ || ci is .defnInfo _ do continue
      let axs ← liftCoreM <| Lean.collectAxioms nm
      let fp := String.intercalate "," (axs.toList.map toString)
      let some d ← Lean.findDocString? env nm | continue
      if d.contains "Axiom-free" || d.contains "No axioms at all" then
        unless fp == "" do bad := bad.push (nm, fp, "claims axiom-free")
      if d.contains "`[propext]`-only" then
        unless fp == "propext" do bad := bad.push (nm, fp, "claims [propext]-only")
      if d.contains "`[propext, Quot.sound]`-only" then
        unless fp == "propext,Quot.sound" do
          bad := bad.push (nm, fp, "claims [propext, Quot.sound]-only")
  unless bad.isEmpty do
    throwError m!"footprint claims disagree with the environment:\n{String.join
      (bad.toList.map fun (n, f, c) => s!"  {n}: {c}, measured [{f}]\n")}"
```

Measured on the pre-change tree: **29 raw mismatches**, of which **11** are genuine
(the rest are survey docstrings claiming about other declarations — the attribution
problem design §D1 solves).

---

## Archive ordering

`codec-audit-round-five` archived 2026-11-07, so this change's MODIFIED blocks are
authored against the **post-sync** text. Before archiving:

1. Re-run the live-vs-delta scenario diff for all four modified requirements.
   Expected, from the deltas as authored:
   - `codec/axiom-gate` "An axiom exclusion is explicit and justified in place"
     1 → 4 scenarios;
   - `codec/review-remediation` "Documentation SHALL distinguish quoted from
     derived claims" 8 → 14 scenarios;
   - `basen` "The conformance laws are gated like the roundtrip laws" 8 → 11;
     `basen` "Base16 decoding accepts both cases" 4 → 5;
   - `template` "The template documents the dependency-injection convention"
     2 → 5.
     **Nothing may be dropped.** Every delta as authored is a strict superset — the
     validator already refused one omission during authoring, which is the hazard
     firing early rather than at archive time.
2. `openspec validate --all` after the archive; it is 11/11 while this change is open
   and should be 10/10 live capabilities once archived.
3. Two ADDED `codec/axiom-gate` requirements, no new capability. All four are
   MODIFIED-or-ADDED-existing.
