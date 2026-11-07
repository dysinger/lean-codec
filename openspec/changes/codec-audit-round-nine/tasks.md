# Tasks — `codec-audit-round-nine`

Legend: **[M]** MUST, **[S]** SHOULD, **[N]** NITPICK. Every id is stable across the
change; the three reviewer reports are `/tmp/review-{paper-adherence,gate-coverage,
numbers-build}.md` and every MUST below was re-measured in the authoring session before
it was accepted (see design D0).

## 0. Preconditions and the things NOT to do

- [ ] 0.1 Confirm the tree is clean and the build is green **before** any edit:
      `git status --porcelain` empty, `nix develop --command lake build` prints its 10
      gate lines. Record the baseline counts (`425 = 347 + 78` theorems,
      `140 = 115 + 25` defs, footprint distribution, claim sites). These are the numbers
      the regenerated header must be checked against, not remembered from this file.
- [ ] 0.2 Re-read `AGENTS.md`'s "Pause signal" and play the alarm on every pause.
- [ ] 0.3 **Do not** edit `openspec/changes/archive/**`. This is a new round; the archived
      ledgers are history.
- [ ] 0.4 **Do not** `git stash` / `git reset` / `git checkout -- <file>`. Commit per
      group so a revert is never tempting.

## 1. `Bench.lean` — the burst lane's fold guard cannot fire [M]

Findings: N-1 (fold guard), N-3 (C-reference `return ()`), S-4 (bench outside every
gate), S-5 (`warningAsError` does not cover the exe root).

- [ ] 1.1 Verify the defect before fixing it, so the fix is measured rather than assumed.
      The mechanism: `bytesAt` is all-`1` except byte 0; `sinkOfList` is `a*31+b` from
      seed `7`; `31a+1` mod 256 has period 16, so `sinkOfList([1]*k) = 7` for
      `k ∈ {16,32,512,4096}`. Print the sink for `j = 0..39` on `idealCursor` and the C
      lane and confirm it is the **single value** `7`. Record the output in this file.
- [ ] 1.2 Replace the shared buffer's uniform tail with a non-uniform one
      (`UInt8.ofNat (i.val % 251)`; 251 prime so slices at `j*8` differ in multiset).
      Note in the docstring **why 251** — a small prime makes the slide change the
      multiset, which a modulus that divides the stride would not.
- [ ] 1.3 Replace `benchBurst`'s `if sink == 0` guard with a **non-invariance** assertion:
      collect the per-`j` sink and require `eraseDups.length ≥ 2`, matching what
      `packedCands` already does. Keep a non-zero check too; they catch different folds.
      The error message must name the row and say the loop was invariant.
- [ ] 1.4 Audit **every** `benchBurst` call site (`Bench.lean:914, 944, 983, 1022, 1233,
    1234` and any added since) and confirm each now produces a varying sink under 1.3.
      A row that still cannot vary must be documented as such, not silently passed.
- [ ] 1.5 `benchCReference`: `| none, none => return ()` exits the whole function and
      silently skips **both** timed lanes. Change to `pure ()` so the loop continues, and
      add a count assertion that the cross-check ran for every intended input.
- [ ] 1.6 `benchCReference`: add `n = 0` and `n = 1` to the cross-check set — these are the
      C's two real branches (`n == 0` and the loop body), and today's four inputs are all
      size 4096 differing only at byte 0.
- [ ] 1.7 Mutation-test 1.3: temporarily make one row's `measure` ignore `j` (loop
      invariant) and confirm the build **fails** naming that row. A new check that has not
      been mutated is not a check — this repo's recorded lesson.
- [ ] 1.8 Add `moreLeanArgs := #["-DwarningAsError=true"]` to `lean_exe bench` so a `sorry`
      in `Bench.lean`'s own theorems (`foldNorm_idem`, `foldNz`) is an error, not a
      warning. Then correct `AGENTS.md`'s over-read ("including `bench`") to say the flag
      rides on imported modules and that the exe root sets its own.
- [ ] 1.9 Settle whether `Bench.lean` belongs in a `checks` entry. It is outside every
      gate today (`flake.nix` has `checks.{lean,openspec,formatting}` and no bench), so
      the `example` checks in it cannot fail CI. Either add a `checks.bench` that runs the
      binary and asserts its value-check lines are present, or qualify the README/CHANGELOG
      prose to say the checks fire only when run by hand. **Decide on evidence**, and
      record which was chosen and why.

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

- [ ] 5.1 **Measure first**: `#print axioms Codec.blitBytes_spec`. At authoring time:
      `does not depend on any axioms`, matching `Axioms.lean:2264`'s `#guard_msgs`.
- [ ] 5.2 Correct `ByteSlice.lean:223` to state the measured footprint. Note that the
      gate's `#guard_msgs` is the authority, not the prose.
- [ ] 5.3 Establish **why the footprint arm did not fire here**, given that the arm exists
      to catch exactly this. Record the mechanism (attribution? `thmInfo` scope? the claim
      being one of the `skipped = 8`?). If the cause is one of Group 6's findings, say
      which, so one fix closes both.

## 6. `Axioms.lean`: close four escape routes [M]

Findings: G-1 (`findFrom.induct`), G-2 (`authored` validity), G-6 (`isBareProj` blind to
`And.left`), G-4/G-4b/G-4c (footprint arm `skipped` and scope), G-3 (pattern decomposition),
G-S1 (census scope).

- [ ] 6.1 **[M] `authored` validity arm.** Assert that every name in `isGeneratedAux`'s
      `authored` array (a) is a public theorem, (b) is in `gatedNames`, (c) has a last
      component the suffix rule _would_ have removed. (c) self-invalidates. Mutation-test:
      rename `Codec.Nat.eq_irrel` in a copy and confirm the build fails naming it.
- [ ] 6.2 **[M] Extend `isBareProj`** to a spine ending in a constant from
      `{And.left, And.right, Iff.mp, Iff.mpr, Prod.fst, Prod.snd}`. Do **not** add these
      names to `propProjections` — the round-eight validity arm would (rightly) fail.
      Mutation-test by confirming the arm now reports `true` on `CandAligned_fst`.
- [ ] 6.3 **[M] Decide `CandAligned_fst`/`_at`/`_tail`'s classification** after 6.2. They
      are hypothesis projections gated as laws with pinned footprints. Move them to the
      projections group with that reason, and account for the three newly-unpinned names in
      `partition`. Per design D3's open question, resolve
      `Iso.apply_eq_some_of_unapply`/`unapply_eq_some_of_apply` at the same time by
      measurement, and if they move, update README `[S1]` in the same commit.
- [ ] 6.4 **[M] Promote `findFrom.induct`** (measured `[propext]`, the only non-empty
      footprint in the allowlist) to `gatedNames` **and** record the def-coverage naming it
      creates explicitly, so `Codec.findFrom` is not "covered" by its own recursion
      principle. Add the footprint pin.
- [ ] 6.5 **[M] Add a footprint-per-allowlisted-theorem report** so an entry filed as "not
      a law" cannot carry a proof that consults an axiom unnoticed. Assert the count.
- [ ] 6.6 **[M] Split `skipped`** into `skipped-names-other-theorem` (a real survey
      paragraph) and `skipped-no-owner` (no resolvable name in the claim's prefix). Measure
      the second; at authoring time `huniq_byte` and `decodeRepeat_mem_iff_general` were in
      it. Assert both numbers, and require `no-owner` to be reviewed.
- [ ] 6.7 **[M] State the footprint arm's kind restriction** in its printed counts: it
      examines `thmInfo` docstrings, so a `def` footprint claim (e.g.
      `ByteSlice.lean:141`'s `findFrom`) is _outside_ the check, not passing it.
- [ ] 6.8 **[S] Decompose the classifier's removals per pattern** and assert the tuple, so
      a pattern removing exactly one declaration (`eq`, `go`, `below`, `brecOn`) is a
      reviewed decision rather than a coincidence.
- [ ] 6.9 **[S] Extend `constantKindCensus`** to walk `axiomInfo`/`opaqueInfo` **globally**
      and allowlist the 12 known axioms by name. The repo's one authored `opaque`
      (`Codec.Bench.cRefByteMany`) currently sits outside the wire the census built.
- [ ] 6.10 **[S] Print the projection arm's decomposition**: `bare projections =
    listed + constant-headed`, two asserted numbers, so the `dec`-suffix exemption
      (`Axioms.lean:1930`) is a number rather than a clause of an `unless`.
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
