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

**§1 is closed and `lake build` is GREEN**, with **seven** gate lines:

```
axiom gate: 349 public theorems covered (0 explicit exclusion(s))
axiom gate: 426 public theorems partitioned, 349 gated and 77 allowlisted
axiom gate: 140 public definitions covered, 115 mentioned and 25 allowlisted (mention proxy)
axiom gate: 54 definitions dropped by the name classifier, all reason-recorded
axiom gate: 12 def-name patterns, each matching a recorded non-surface declaration
axiom gate: header numbers verified (426 = 349 + 77; defs 140 = 115 + 25)
axiom gate: stated footprints verified against the environment
```

**No section from §2 on needs a red build.** §1's arm is verified non-vacuous by
mutation (see task 1.5), so a green run now means something.

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

- [ ] 2.1 Replace the dead branch. **R7-05.** ✔Verified `a - b + b ≠ a` is false for
      all `a, b` by exhaustive enumeration. Replace with
      `mentionedCount + definitionSurfaceAllowlist.size != defs.size`.

- [ ] 2.2 Assert both numbers in the "443 / 440" sentence. **R7-06.** ✔Measured
      `grep -c '^#print axioms'` → **443**, `gatedNames` → **440**; the prose says
      `440 / 437`. Fix the prose **and** fold both into the `run_cmd` so the pair
      cannot drift together again.

- [ ] 2.3 Close the `nativeDecideCount` escapes. **R7-07.** ✔Reproduced: a trailing
      comment moves the count `12 → 11`; `:= by native_decide` and two-on-a-line are
      invisible; `uses` is computed and never compared. Fix: truncate each line at
      `--`, strip both ends, and assert `uses ≥ tacticLines` as well as
      `tacticLines == stated`.

- [ ] 2.4 Give `exclusions` the stale arm its sibling has. **R7-17.** Two failures:
      a name that is not a public theorem, and a name whose measured footprint is
      already inside the discipline. Both are build failures.

## 3. The `Rab` family (R7-09, R7-10)

- [ ] 3.1 Record that `Rab` is deliberately the same relation as
      `uniqCounterexampleRel`. **R7-09.** ✔Verified: identical bodies. Keep both
      names; the defect was the prose contrasting them as if they differed.

- [ ] 3.2 De-orphan or delete `decodeRepeat_mem_iff_general`. **R7-10.** Its
      docstring says the specialisation "was never necessary", yet the specialisation
      is the only one used. Either rewrite `huniq_byte` to consume the general form
      and delete the specialisation, or record it as a kept alias with no caller.
      **Prefer the first**: it makes the docstring true.

## 4. base16 (R7-15)

- [ ] 4.1 Prove `decodeHexFold (encodeHex bs) = some bs`. **R7-15**, design §D6.
      ✔Verified the pieces exist: `foldList_hexBlockUnapply` supplies the fixed-point
      hypothesis, `decodeHexFold_of_fixed` consumes it. If awkward, fallback is a
      scoped README row (design §D6) — either outcome ends in a tick.

- [ ] 4.2 Say which decoder owns which laws, in `README:29`'s table.

## 5. `README` (R7-03, R7-04, R7-11, R7-12, R7-18 … R7-27, R7-31)

- [ ] 5.1 Repair `[S1]`'s arithmetic. **R7-03.** ✔My environment walk returns **19**
      and includes `Codec.uniqSeqIso` / `Codec.uniqSeqUnitIso`. Keep 19; fix the sum
      to `13 + 4 + 2` and "two counterexample witnesses" → **four**.
      **Do not change 19 to 21** — see §9, that reviewer figure is refuted.

- [ ] 5.2 Fix the phantom name. **R7-04.** ✔`#check` → unknown identifier;
      the real constant is `Codec.uniqSeq_not_congruent` (`Codec/Sound.lean`).

- [ ] 5.3 Fix table 4's caption. **R7-11.** ✔`10532 / 512 = 20.57`, but the row says
      `2.57` — it is a 4096-step figure. Give the span per row. **Do not re-run the
      lane.**

- [ ] 5.4 Repair the four dead anchors. **R7-12.** ✔Verified none of the four
      targets exists as a heading. Recompute the GitHub anchor from the real heading.

- [ ] 5.5 Fix the per-step and figure inconsistencies. **R7-25/26/27.** "~4–7"
      → "~4–6" (derivation max 6.4); "430–541" → the table's "430–650"; either
      table the `decodeFull spec` figure or drop it.

- [ ] 5.6 Fix the four anchoring/wording items. **R7-18/19/20/21.** `print → encode`
      lead; `[S1]`'s "Five" heading; `[D7]`'s "no inverse law exists"; `[D4]`'s
      paraphrase-in-quotes.

- [ ] 5.7 Fix `[S3]`'s "no hypothesis at all" and `[D2]`'s inverted `bidir`
      citation. **R7-24/31.**

## 6. Cross-repo and template (R7-13, R7-14, R7-16, R7-28 … R7-33)

- [ ] 6.1 Decide the pin. **R7-13.** ✔Verified: pinned `5acf487`, HEAD `fc132de`,
      **14 commits**, and the pinned rev **is** an ancestor. Bump
      (`nix flake update codec` — targeted; then `lake update codec`) and re-run all
      three gates, **or** record the lag with its reason in `AGENTS.md`. Either way
      the repo's own quoted rule is satisfied.

- [ ] 6.2 Resolve or drop the two unresolved CHANGELOG SHAs. **R7-14.**
      ✔`git cat-file -t` fails for both in both repos.

- [ ] 6.3 Make the bench-lane documents match the code. **R7-16**, design §D4.
      `Bench.lean:707` is `main : IO Unit := pure ()`. Rewrite `default.nix:16-21`,
      the `installPhase` comment, and the `AGENTS.md` bullet to say the checks fail
      at **build** time, and restate what `nix build '.#bench'` then proves.

- [ ] 6.4 `basen` README/doc prose sweep. **R7-28/29/32/33.** Rename
      `rejects_single_char` (or document it), complete the overflow enumeration,
      `3 + 9 = 12`, name the canonical `MY======`.

- [ ] 6.5 Template. **R7-30.** Drop the `bench` paragraph the template does not
      ship; scope the git-tracked claim to the flake path; add `moreLeanArgs` to
      `lean_exe cli`.

- [ ] 6.6 Port the footprint arm to `basen`'s `Axioms.lean`. **R7-02**, `basen`
      spec delta. `basen` has docstrings stating footprints too and no arm to check
      them.

## 7. Regenerate (gate counts)

- [x] 7.1 Regenerate `Axioms.lean` once (`scripts/gen-axioms.lean`) and move the
      header tables and the six `expected*` constants together. **Do not predict the
      delta — the run prints it.** `basen` likewise if §2/§6.6 change its counts.
      **Done for `codec`.** The run printed `rewrote 349 gates`; header moved to
      `426 = 349 + 77`, `expectedPub`/`expectedGated` in lockstep, and the build is
      green with **seven** gate lines. `basen`'s counts are untouched by this
      regeneration and need their own run if §2/§6.6 move them.

## 8. Gates (run all three repos; they are different flakes)

- [ ] 8.1 `codec`: `nix fmt` first, then `lake build` (zero `sorry`, four-plus gate
      lines, counts in lockstep), `lake build bench`, `openspec validate --all`,
      `nix flake check` (**detached with `nohup`, never foregrounded**).
- [ ] 8.2 `basen`: `lake build`, `lake build bench`, `nix build '.#bench'`.
- [ ] 8.3 `template`: `nix flake check`, `nix build .#native .#cli`.
- [ ] 8.4 Commit per task family, individual files only, printing
      `git diff --cached --name-only` before each. The pre-commit hook runs `nix fmt`
      and rejects a reformatted staged file; re-add and commit again.
- [ ] 8.5 Verify every new law's footprint by hand and paste the output:
      `printf 'import Codec\n#print axioms Codec.<n>\n' > /tmp/c.lean` →
      expect `[propext, Quot.sound]` or cleaner. `Classical.choice` is a defect.

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
