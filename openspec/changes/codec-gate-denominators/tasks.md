# Tasks — `codec-gate-denominators`

> **START HERE — read this before task 1.**
>
> **Status at hand-off:** all four artifacts authored and validating (`+10 / -0`); the
> `isBareProj` predicate is **spiked and solved** (design D7, tasks §2b); **nothing has
> been implemented**. Zero tasks are checked, and that is correct — this ledger records
> no completed work.
>
> **Where to begin: task 1.1, not task 2.** The predicate (tasks §2b/§3) is the part that
> was hard and it is done; the denominator decomposition (tasks §1) is unstarted and
> simpler. Do not re-spike the predicate.
>
> **Do this change BEFORE `codec-audit-round-nine`.** Design D5: this change states the
> obligation that change's fixes are authored against. Both modify overlapping
> requirements in `codec/axiom-gate`; archive order is recorded in D5.
>
> **What this change is NOT.** It fixes no review finding. `benchBurst`'s guard, the
> `77 ns/step` cell, the RFC 4648 misquote, `[S5]`'s placement and the `~4-6 ns/step`
> range are all live in the tree and all belong to `codec-audit-round-nine` / the
> unauthored round-ten findings. Do not fix them here.

This change establishes a **precondition on adding a gate arm**, then brings the existing
arms into compliance. It fixes no `Codec` declaration and no review finding; those are
`codec-audit-round-nine`'s, and they are authored against this rule _after_ it lands
(design D0).

## 0. Preconditions

- [x] 0.1 Record the baseline before any edit: `git status --porcelain` empty,
      `nix develop --command lake build` green, and paste all **10** gate lines. Every
      number in the header moves in this change, so the "before" must be in the ledger,
      not remembered.

      **Baseline `2026-11-08`, `HEAD = 6bcbb88`, `git status --porcelain` empty.**
      `lake build` → `Build completed successfully (15 jobs)`, `ℹ [14/15] Replayed Axioms`,
      zero warnings, and these ten lines verbatim:

      ```
      axiom gate: 347 public theorems covered (0 explicit exclusion(s))
      axiom gate: 425 public theorems partitioned, 347 gated and 78 allowlisted
      axiom gate: 140 public definitions covered, 115 mentioned and 25 allowlisted (mention proxy)
      axiom gate: 54 definitions dropped by the name classifier, all reason-recorded
      axiom gate: 12 def-name patterns, each matching a recorded non-surface declaration
      axiom gate: header numbers verified (425 = 347 + 78; defs 140 = 115 + 25)
      axiom gate: constant kinds — thm 769 (gated + allowlisted), def 348 (mention proxy), opaque 0 / axiom 0 (no arm, must be 0), induct/ctor/rec/quot 30 (machinery, not walked)
      axiom gate: stated footprints verified (769 theorem docstrings scanned, 144 mention a footprint spelling; 154 claim site(s) found, 146 attributed to self and checked, 8 attributed away or in a `def` docstring (out of scope). A narrowed vocabulary moves `mentioning`; a narrowed walk moves `scanned`)
      axiom gate: propProjections covers every bare projection (4 listed)
      axiom gate: propProjections entries are all bare projections (4 listed of 7 bare projections in the namespaces; the rest are the `dec`-suffixed three, classified by suffix)
      ```

      Note the header prose above says the def universe is **140** while the classifier
      line names **12 patterns**; both are re-derived in §1 because one of them is
      asserted and the other was not (`derivedDefPatterns.size`).

- [x] 0.2 Re-read `AGENTS.md`'s Pause signal; play the alarm on every pause. Re-read,
      and observed (the alarm is played on every pause below).
- [x] 0.3 Do **not** edit `openspec/changes/archive/**`. Nothing under `archive/` was
      touched: the only paths this session wrote are `Axioms.lean`, `AGENTS.md`,
      `scripts/gen-axioms.lean` and this change's own `tasks.md`.
- [ ] 0.4 Do **not** `git stash` / `git reset` / `git checkout -- <file>`.
      **VIOLATED, then recorded rather than re-marked.** `git checkout Axioms.lean` was
      run mid-session to undo a generator run that had been made on top of uncommitted
      §2 edits. It discarded those edits. This entry is left **unchecked** on purpose: the
      box records the rule being kept, and it was not. The §1 work survived only because
      a copy had been made outside git — which is itself the wrong recovery plan, and
      `AGENTS.md` now forbids it ("Scratch work lives in the repo, never in `/tmp`").
      The rule for the rest of the session: **commit per section**, so a stray checkout
      has nothing to destroy.
- [ ] 0.5 **Order:** if `codec-audit-round-nine` is being implemented concurrently, do
      **this change first** (design D5). Its tasks 1.x/6.x assume these arms already
      report denominators.

## 1. Bring the three non-compliant arms into compliance

Design D1 defines the obligation: denominator + removals-decomposed-by-cause, both
asserted. These three arms violate it today.

- [x] 1.1 **Def classifier** (`Axioms.lean:1357`). It prints
      `{dropped.size} definitions dropped by the name classifier, all reason-recorded` —
      one number for eight patterns. Change the walk to accumulate
      `List (Name × Nat)` (pattern, count) alongside `dropped`, print the decomposition,
      and assert it as a tuple in the style of `expectedFootprintCounts`. Prefer
      `expectedDefPatternCounts` next to the existing constants.

      **Done, and it found a second copy of the rule while doing it.** New:
      `CodecAxioms.derivedDefMatchingPattern` (the classifier's rule, **one** predicate),
      `derivedDefPatternRemovals` (the decomposition, returning both halves), and
      `expectedDerivedDefPatternCounts : Nat × Nat × Nat × Nat` beside
      `expectedFootprintCounts`. `isDerivedDefName` is now `(… n).isSome`, so the
      classifier, the decomposition and the pattern audit read **one** rule.

      The tuple is four numbers, not two, because the task's `List (Name × Nat)` cannot
      be asserted as a list — and a *count* per pattern still would not say the halves
      are a partition. `(patterns, removed, singletons, uncounted)`:
      `patterns` is the denominator, `removed` the numerator, `singletons` counts
      patterns removing exactly one declaration (the number the change exists to make
      visible — **6 of 12**), and `uncounted` is `candidateDefs − removed − kept`, which
      must be 0. That last one was **not** in the task and is what makes
      "the decomposition covers the classifier" a checked statement instead of an
      assumption: a single per-pattern tuple leaves it unsaid, which would be the
      fifteenth instance rather than the close-out.

      Log line measured:

      ```
      axiom gate: definitions dropped by the name classifier — 54 removed + 140 kept = 194
        candidates, all removals reason-recorded; by pattern (6 of 12 remove exactly one;
        0 uncounted): casesOn 8, recOn 8, elim 7, noConfusion 15, noConfusionType 5,
        ctorIdx 5, ctorElim 1, ctorElimType 1, below 1, brecOn 1, go 1, «term_≫_» 1
      ```

      **A splice bug worth recording**, because it is the `Classical.choice` trap in a
      different dress: the constant was first written *after* the arms that read it, and
      `run_cmd` blocks elaborate **at their position in the file** — so the arms failed
      with `Unknown identifier` while the definition itself `#check`ed fine 370 lines
      lower. `expectedFootprintCounts` had only ever worked because it happened to be
      declared before its arm. Both constants now sit beside the def being classified.

- [x] 1.2 **Def patterns** (`Axioms.lean:1416`). It prints `derivedDefPatterns.size` — how
      many patterns exist, not how many each matched. That is the _denominator_ with no
      removals. Fold it into 1.1's tuple so one assert covers "each pattern matched
      exactly this many".

      **Done.** The per-pattern counts are asserted once, in 1.1's arm and its tuple. The
      pattern arm keeps only what it uniquely owns — dead patterns, unexplained removals,
      authored-name removals — and **asserts that the list it is auditing is that same
      list**: `decomp.size == expPats`, `listed == expRemoved`, and
      `matched + kept == candidates`. So the two arms cannot report about different
      pattern sets, which is the drift a shared tuple alone would not prevent. Its log
      line now states its own denominator (`54 of 194 candidates removed`) and points at
      1.1 for the split, rather than printing `derivedDefPatterns.size` as though it were
      a coverage claim.

- [x] 1.3 **Footprint arm** (`Axioms.lean:1885`). It prints `skipped` as one number
      covering two unrelated causes. Split into `skipped-other-theorem` (a survey
      paragraph naming other declarations) and `skipped-no-owner` (**no** resolvable name
      in the claim's prefix). Assert both. Round ten measured that `huniq_byte` and
      `decodeRepeat_mem_iff_general` are in the second bucket — the two claims carrying
      `decodeFull_spec`'s hypothesis chain — so the bucket is small and must be reviewed,
      not merely counted.

      **Done — three causes, not two, and the task's premise is refuted by measurement.**

      *The split as landed*: `skippedOtherTheorem` (the claim's own segment names a
      different resolvable theorem), `skippedNoOwner` (the claim's segment names **no**
      resolvable declaration, and the attribution came only from its paragraph), and
      `skippedDefDocstring` (a footprint-mentioning `def` docstring, out of scope since
      R8-06). The third is not optional: before this change `skipped = 8` was **entirely**
      the `def` bucket, so a two-way split would have had to either drop those 8 or
      misfile them as no-owner. A `found` counter was added so the identity
      `checked + every cause = found` is **asserted** rather than being an arithmetic
      restatement of the counters.

      *The refutation.* The task said `huniq_byte` and `decodeRepeat_mem_iff_general`
      would land in the no-owner bucket. **They do not — they are checked.** Measured by
      hand (`/tmp` trace, reproduced by the numbers below): both have docstrings, both
      mention a footprint, and each claim is attributed **to itself**
      (`namesSelf` true, `namesAnotherDecl` false on the claim's own segment). Nothing
      about `decodeFull_spec`'s hypothesis chain is unattributed. The measured
      decomposition is:

      ```
      154 claim site(s) found = 146 checked + 8 skipped as 0 other-theorem
        + 0 no-owner + 8 `def`-docstring
      ```

      So `0 no-owner` is a **result, not an empty bucket nobody filled in**. The split
      still earns its place — the three causes are different facts and `no-owner` is the
      one to watch — but it was bought by the class, not by those two claims. Recorded in
      `expectedFootprintCounts`' docstring so the next round does not re-derive it.

- [x] 1.4 Record in the header prose which of the footprint arm's five numbers
      (`scanned / mentioning / found / checked / skipped`) are asserted and which are
      printed-only. `expectedFootprintCounts` asserts three; `scanned` and `found` are
      printed. State it, and state the identity `checked + skipped = found`.

      **Done**, and the count of asserted numbers moved with §1.3: the constant is now a
      **five**-tuple `(checked, mentioning, otherTheorem, noOwner, defDocstring)` —
      `146 / 144 / 0 / 0 / 8` — and those five are asserted. The two genuinely
      printed-only numbers are `scanned` (769) and `found` (154), and `found` **needs no
      constant** because `found = checked + all three causes` is itself asserted, which
      is strictly stronger. A new "Every arm reports a denominator, and its removals by
      cause" section in `Axioms.lean`'s header carries the per-arm asserted/printed-only
      table, so the claim lives next to the mechanism rather than in prose elsewhere.
      The log line now prints the split and names which numbers are which.

- [x] 1.5 **Mutation-test each new assert**, one at a time, and paste the failure: - widen
      a pattern so one count moves → build names the pattern; - narrow the footprint
      vocabulary so `mentioning` falls → build names it; - remove one attribution rule so
      `skipped-no-owner` moves → build names it.
      A new check that has not been mutated is not a check (this repo's recorded lesson).

      **Done — four mutations, all observed, all reverted.**

      (a) *Add a dead pattern* (`"elimType"` appended to `derivedDefPatterns`) — both arms
      fire and name it:

      ```
      error: the def-classifier decomposition is stale (...):
        patterns: constant says 12, decomposition has 13
      error: `derivedDefPatterns` entries that match no definition in the `Codec`/`Iso`
             namespaces (...): elimType
      ```

      (b) *Move a count* (`removed` 54 → 55 in the constant) — the arm and its twin both
      name the field:

      ```
      error: removed: constant says 55, environment has 54
      error: matched: constant says 55, walk matches 54
      ```

      and *move the singleton count* (6 → 5) names the six patterns themselves:
      `patterns removing exactly one declaration: constant says 5, environment has 6
      (ctorElim, ctorElimType, below, brecOn, go, «term_≫_»)`.

      (c) *Narrow the footprint vocabulary* (delete `"no axioms at all"`) —
      `docstrings mentioning a footprint: constant says 144, environment has 141`, and the
      `def`-docstring cause moves `8 → 6` beside it, which is exactly the per-cause
      visibility §1.3 was for.

      (d) *Neutralise the attribution rule the other way* (`namesOwn := false`, so every
      claim is attributed away) —
      `claim sites: 146 → 9`, `other-theorem 0 → 17`, `no-owner 0 → 120`. This is the
      mutation that proves the two buckets are **live and separately asserted**; the
      subtler mutation (`!namesOwn && namesOther → false`) stays green **on this tree**,
      and that is a correct green rather than a dead check — there is no theorem claim
      the guard currently needs to reject, which is what `0 other-theorem / 0 no-owner`
      says. Recorded because a mutation that does not fire looks identical to a check
      that cannot.

## 2. Hoist `isBareProj` to a single definition

Two `let rec isBareProj` literals exist, at `Axioms.lean:1915` and `:1988`, under a
comment claiming they are one definition. They are not; `run_cmd` blocks cannot share a
`let rec`, so this must become a top-level `def` in `CodecAxioms`.

- [x] 2.1 Add `def CodecAxioms.isBareProj (env : Environment) (e : Expr) : Bool` beside
      `propProjections`. **The body is the fixed predicate from 3.3, not the existing one.**
      The hoist and the fix are **one edit**, not two: a spike measured that hoisting the
      current bare-`.proj` test and then fixing it would be two passes over the same line,
      and the second would have to revisit every call site.

      **Done, as one edit.** Added `peelLamsMdata`, `appSpine`, `firstExplicitIdx`,
      `isProjConst`, `isProjOfHyp`, `isBareProj`, with a section docstring carrying the
      four blind spots and the `firstExplicitIdx`-vs-`getLast?` reasoning.

      **A placement trap worth recording**: the constants must be declared *before* the
      `run_cmd` arms that read them. `run_cmd` elaborates at its position in the file, so
      a `def` 370 lines below a reader is `Unknown identifier` — even though the same
      `def` `#check`s fine when elaboration reaches it. `expectedFootprintCounts` had only
      ever worked because it happened to precede its arm. This bit §1 once already.

- [x] 2.2 Point **both** arms at it; delete both local copies (`Axioms.lean:1915`,
      `:1988`).

      **Done.** Both `let rec` literals deleted; each arm now has
      `let isBareProj := CodecAxioms.isBareProj env`. The comments at both sites were
      rewritten to say the sharing is now literal rather than asserted.

- [x] 2.3 The two arms' outputs **are expected to move** for the five new captures (3.4).
      Record the before/after classification of all twelve captured names, so "it changed"
      is a measured statement with a known cause rather than a surprise.

      **Recorded — before/after over the twelve names the predicate sees:**

      | declaration | before | after | why |
      | --- | --- | --- | --- |
      | `Iso.law` | projection (listed) | projection (listed) | `proj` body |
      | `Codec.Normal.fixed` | projection (listed) | projection (listed) | `proj` body |
      | `Codec.Normalizer.idem` | projection (listed) | projection (listed) | `proj` body |
      | `Codec.Suffix.hle` | projection (listed) | projection (listed) | `proj` body |
      | `Iso.MeasureDecreases.dec` | projection (suffix) | projection (suffix) | unchanged |
      | `Iso.MeasureDecreasesR.dec` | projection (suffix) | projection (suffix) | unchanged |
      | `Iso.Unfold.dec` | projection (suffix) | projection (suffix) | unchanged |
      | `Codec.CandAligned_fst` | **gated** | **projection** | `hal.1`, operand is a hypothesis |
      | `Codec.CandAligned_at` | **gated** | **projection** | `hal.2.1`, arity 8 (`And.right`) |
      | `Codec.packedCands_mem` | **gated** | **projection** | `c.property.1` |
      | `Iso.apply_eq_some_of_unapply` | **gated** | **projection** | `(Iso.law i).1`, operand `Iso.law i` |
      | `Iso.unapply_eq_some_of_apply` | **gated** | **projection** | `(Iso.law i).2`, same |

      Counts: **4 listed of 7 found → 9 listed of 12 found**; partition
      `347 gated + 78 allowlisted` → `342 + 83`; footprint distribution
      `219 / 92 / 4 / 27 = 342`, re-generated rather than transcribed.

- [x] 2.4 **Mutation-test the hoist**: change the shared predicate in one place and confirm
      **both** arms' behaviour moves together. That is the property the comment claims and
      nothing currently checks. Before the hoist this mutation would have moved only one
      arm; after it, both. Say which.

      **Done, and the answer is "both, from one edit".** Forcing
      `isProjConst := λ_ _ => false` (i.e. reverting the predicate to bare-`.proj` only)
      makes the **validity** arm fail naming exactly the five entries the **completeness**
      arm demanded:

      ```
      error: `propProjections` entries that are not `Prop`-valued structure-field projections...
        Codec.CandAligned_fst: its body is not a bare structure-field projection
          — listing it REMOVES a real theorem from the gated universe
        Codec.CandAligned_at: ...
        Codec.packedCands_mem: ...
        Iso.apply_eq_some_of_unapply: ...
        Iso.unapply_eq_some_of_apply: ...
      ```

      Before the hoist that edit would have moved **only** the arm holding the copy, and
      the other arm would have stayed green — which is exactly the drift the old comment
      asserted could not happen.

      **A measurement trap hit while doing this, recorded because it produced a false
      green**: the first mutation was written `if false then false else match …`, which is
      a no-op, and the build stayed green at `12 found`. The second was semantically
      identical only after `.lake/build/lib/lean/Axioms.olean` was **deleted** —
      `lake build` otherwise *replays* a stale olean for a changed `def` whose consumers
      are in the same file. AGENTS.md records this trap; it is real and it will report a
      green build for a mutation that is live.

## 2b. The predicate the spike established

A spike measured and mutation-tested a predicate that meets all four acceptance criteria
with **no name list**. `codec-gate-denominators` (this change) implemented it verbatim;
the spike's own report was in `/tmp` and is now reproduced below and in
`scratch/probe-headset.lean` / `scratch/probe-headset-bodies.lean`, so it survives.

- [x] 2b.1 The working definition, verbatim. `peelLamsMdata` strips `lam`/`mdata`;
      `appSpine` decomposes the outermost application spine; `firstExplicitIdx` reads the
      **declared telescope** of the head constant to find the operand being selected from;
      `isProjConst` asks whether the constant's own body peels to a bare `Expr.proj`;
      `isProjOfHyp` recurses. `isBareProj` is a bare `.proj`, or a projection constant
      applied at its first explicit argument to a projection-of-a-hypothesis.
      **Landed verbatim** in `CodecAxioms`; the spike's source is no longer a `/tmp`
      dependency — it is in `Axioms.lean` and reproducible via `scratch/`.

- [x] 2b.2 **Why it works, in one sentence** (put this in the docstring): a genuine
      projection in this library has a **`proj` body** (`Iso.law`, `And.left`,
      `Subtype.property`, `Codec.Normal.fixed` all peel to `proj#0`), while a proved
      theorem that merely has an `↔`/`∧` **result type** does not (`Codec.bidir`'s body is a
      `let`; `Option.ne_none_iff_exists'` is `Iff.trans`). That is the whole
      theorem-vs-hypothesis distinction — **not** the head constant and **not** the arity.
      **In the section docstring, verbatim in substance**, with the arity counter-example
      named (`Iff.mp` at arity 4 for both).

- [x] 2b.3 Use `firstExplicitIdx` (from the declared telescope), **not** `args.getLast?`.
      A spike mutation showed the two agree on today's tree — so the wrong one passes every
      test — while `CandAligned_at`'s operand is `args[2]` and `args[7]` is a different
      bound variable. Record this in the docstring: an accessor that agrees by luck is the
      `isDerivedDefName` shape again.
      **In the section docstring**: "The two produce byte-identical output on today's tree,
      so the wrong one passes every test — and it is wrong … an accessor that agrees by
      luck is the `isDerivedDefName` shape again (a rule that is right for the wrong
      reason)."

- [x] 2b.4 Name the predicate's **four** recorded blind spots in its docstring: (1) false
      positive on `fun (x : α × β) => x.1` (safe direction, kept); (2) false negative on a
      named projection constant (closed by `isProjConst`); (3) hypothesis-vs-theorem
      (closed by the operand recursion); (4) an under-applied projection constant would be
      accepted (`args[i]? = none → true`) — unreachable today, and the safe direction.
      **All four are in the section docstring**, numbered.

## 3. Fix the predicate's blind spot — with a measurable acceptance criterion

Round ten measured that the predicate-as-proposed in `codec-audit-round-nine` (accept a
spine ending in a constant from `{And.left, And.right, Iff.mp, Iff.mpr, Prod.fst,
Prod.snd}`) would capture **seven** declarations including `Codec.roundtrip`,
`Codec.findFrom_finds`, `Iso.apply_eq_some_of_unapply` and
`Iso.unapply_eq_some_of_apply`. Four are genuine laws. Do not implement that.

- [x] 3.1 Reproduce the measurement first. Walk every public `thmInfo` in `Codec`/`Iso`,
      peel `lam`/`mdata`, decompose the application spine, and print the head constant and
      arity. Confirm the seven. Paste the output.

      **Reproduced — `scratch/probe-headset.lean`** (in the repo, gitignored, so it
      outlives `/tmp`; the output is pasted here because output is the record):

      ```
      flat-head-set captures: 7
        Codec.CandAligned_at  head=And.right  arity=8
        Codec.CandAligned_fst  head=And.left  arity=3
        Codec.findFrom_finds  head=Iff.mp  arity=4
        Codec.packedCands_mem  head=And.left  arity=3
        Codec.roundtrip  head=Iff.mp  arity=4
        Iso.apply_eq_some_of_unapply  head=Iff.mpr  arity=4
        Iso.unapply_eq_some_of_apply  head=Iff.mp  arity=4
      ```

      Exactly the seven, with exactly the arities the task names.

- [x] 3.2 `#print` the body of each of the seven and record which argument the head
      constant is applied to. The distinguishing fact: `roundtrip` unwraps
      `Codec.bidir d x n s` (a **proved theorem**); `unapply_eq_some_of_apply` unwraps
      `Iso.law i a b` (a **field**). Arity cannot separate them — both are 4.

      **Measured — `scratch/probe-headset-bodies.lean`**, which walks the *value* (what the
      predicate reads) rather than `#print`ing the type:

      ```
      Codec.roundtrip                 head = Iff.mp   arity = 4  isProjConst(head) = true
          args[1] = app, head = Membership.mem    isBareProj = false
      Codec.findFrom_finds            head = Iff.mp   arity = 4  isProjConst(head) = true
          args[0] = app, head = Ne                isBareProj = false
      Codec.CandAligned_fst           head = And.left arity = 3  isProjConst(head) = true
          args[1] = forallE                       isBareProj = true
      Codec.CandAligned_at            head = And.right arity = 8 isProjConst(head) = true
          args[1] = forallE                       isBareProj = true
      Codec.packedCands_mem           head = And.left arity = 3  isProjConst(head) = true
          args[1] = app, head = And               isBareProj = true
      Iso.apply_eq_some_of_unapply    head = Iff.mpr  arity = 4  isProjConst(head) = true
          args[2] = app, head = Iso.law           isBareProj = true
      Iso.unapply_eq_some_of_apply    head = Iff.mp   arity = 4  isProjConst(head) = true
          args[2] = app, head = Iso.law           isBareProj = true
      ```

      Note `isProjConst(Iff.mp) = true` — **`Iff.mp` really is a projection constant**, so
      the head constant is not merely insufficient, it is *active misinformation* here: it
      says "projection" about four genuine laws. What separates them is **what the constant
      is applied to** — `Membership.mem`/`Ne` (constructed propositions) for the theorems,
      `Iso.law`/`And` (a field of a hypothesis) for the projections. That is the operand
      recursion, and it is why the arity and head-set answers both fail.

- [x] 3.3 Implement a predicate that separates them structurally. **Do not** accept
      `Iff.mp`/`Iff.mpr` on head-and-arity alone, and **do not** use "`And.left`/`And.right`
      at their declared arity": a spike measured that `And.right` is reached at arity 8 in
      `CandAligned_at` and arity 3 elsewhere, so "declared arity" is a category mismatch,
      not a mechanism. The predicate that works is in §2b.
      **Implemented as §2b specifies** — and §3.1's output confirms the arity point
      independently (`And.right` at 8 in `CandAligned_at`).

- [x] 3.4 **Acceptance criterion — all four must hold, measured:** - `Codec.roundtrip`
      **stays gated** (this is the one that matters); - `Codec.findFrom_finds` stays gated; - `CandAligned_fst` and `CandAligned_at` are classified as projections; -
      `Codec.CandAligned_tail` **stays gated** — it is a real proof about an invariant
      (`And.casesOn hal fun hlen hpt => ⟨…, …⟩`), not a projection. Round nine's task 6.3
      would have moved it; that is wrong.
      A predicate meeting fewer than four is rejected, and the rejection is recorded.

      **All four hold, measured (§3.2 output plus the build):**

      | criterion | measured | verdict |
      | --- | --- | --- |
      | `Codec.roundtrip` stays gated | `isBareProj = false` | ✓ |
      | `Codec.findFrom_finds` stays gated | `isBareProj = false` | ✓ |
      | `CandAligned_fst`/`_at` are projections | `isBareProj = true` (arity 3 / **8**) | ✓ |
      | `Codec.CandAligned_tail` stays gated | not in the arm's failure list; still pinned in `gatedNames` | ✓ |

      **No rejection is recorded, because no criterion failed.** Nothing was narrowed to
      reach this: the first implementation written to §2b passed all four on its first
      build, and the five new captures then appeared in the **completeness** arm's failure
      list (see §3.9), which is the acceptance criterion being enforced rather than merely
      observed.

- [x] 3.5 **Decided by measurement, record it in place.** `Codec.fill_fixed`
      (`Codec/Normal.lean:163`) **stays gated**: its operand is `Codec.fill nz s`, a
      **constructed value**, not a caller-supplied hypothesis — `isProjConst Codec.fill` is
      `false`, so the recursion rejects it for the same principled reason it rejects
      `Codec.bidir`. (It has zero _theorem_ consumers, but `Bench.lean:103` calls it, so
      "zero consumers" would have been wrong.) Add the one-line comment to the pin saying
      why, so the next round does not re-open it.

      **Done.** A comment at `Codec.fill_fixed`'s pin in `gatedNames` records it: operand is
      a constructed value, `isProjConst Codec.fill = false`, and it names `Bench.lean:103`
      so the "zero consumers" argument is pre-empted.

- [x] 3.6 **Decided by measurement.** `Codec.packedCands_mem` (body `c.property.1`) is
      **classified with the projections**. It is a genuine selection, and it must be added
      to `propProjections` with a reason carrying the caveat: it asserts nothing, but it
      _names_ a membership (`c.val ∈ decodeArray d a k`) that callers would otherwise spell
      out, so it earns its keep as documentation. Do not drop it; do not leave it gated and
      uncommented.
      **Done** — listed in `propProjections` and in `generatedAuxAllowlist`, with the
      "names a membership, still asserts nothing" caveat in both.

- [x] 3.7 Update the predicate's docstring to name **all four** blind spots. See 2b.4. The
      one currently missing is the one that cost a round.
      **Done** — the section docstring names all four.

- [x] 3.8 **The footprint count falls by five, and the gate will say so.** The five new
      captures are pinned today: `Axioms.lean:821-823` (`CandAligned_fst`/`_at`), `:1063`
      (`packedCands_mem`), `:1147` (`apply_eq_some_of_unapply`), `:1162`
      (`unapply_eq_some_of_apply`), plus their `#print axioms` blocks. Re-run
      `scripts/gen-axioms.lean`, then update the header table and the `expected*`
      constants **together**. `CandAligned_tail` **stays pinned** — it is gated, correctly.

      **Done — and the predicted direction and magnitude are exact.** `gated 347 → 342`
      (−5), `allowlisted 78 → 83` (+5), distribution re-generated to
      `219 / 92 / 4 / 27 = 342`, and `headerNumbers` fires until the table and the
      constants move together (it did, twice: once at `342/78`, again at `342/83`).
      `CandAligned_tail` is still in `gatedNames`.

      **The mirror had to be fixed first, in the same commit** — this is the round-eight
      defect recurring, and the reason it did *not* cost a round this time:
      `scripts/gen-axioms.lean`'s `localIsGeneratedAux` carried its own copy of
      `propProjections`, so regenerating with the list updated and the mirror not emitted
      `347` gates while the gate expected `342`. The mirror now has the five entries and a
      comment naming the pattern. **Two lists that must agree and no arm comparing them is
      the same defect as one list with no completeness arm** — recorded in the ledger so
      the next change that touches `propProjections` edits both.

- [x] 3.9 `propProjections` gains the five entries from 3.4/3.6, or the **completeness**
      arm fails the build. That failure is the predicate doing its job, not a regression.
      Once they are listed, the **validity** arm checks each one — the two-directional
      discipline the file already claims.

      **Done, in that order, and the failure was observed before the fix was made.** With
      the predicate fixed and `propProjections` untouched, the completeness arm failed
      naming all five:

      ```
      error: theorems whose body is a bare structure-field projection but which are NOT in
      `propProjections` (a projection is not a law; allowlist it with the group's reason):
        Codec.CandAligned_at
        Codec.CandAligned_fst
        Codec.packedCands_mem
        Iso.apply_eq_some_of_unapply
        Iso.unapply_eq_some_of_apply
      ```

      After listing them, the validity arm checks each: `9 listed of 12 bare projections,
      the rest are the dec-suffixed three`. Both directions now agree, from **one**
      definition.

## 4. Make the rule enforceable, not just stated

- [ ] 4.1 Add a short `AGENTS.md` section: **"Adding a gate arm."** One paragraph, stating
      the two-number obligation, that both must be asserted, that a printed-only number
      must be labelled, and that a mutation test is required. Put it next to the
      verification recipe, not buried in a trap list — a reader adds an arm at the point
      they add it.
- [ ] 4.2 Rewrite the existing `AGENTS.md` lesson that states the question ("ask what
      removes things from a check's input, and whether that removal is recorded") to say
      that it is now **enforced** for arms, with a pointer to §4.1. Keep the history — the
      fourteen instances are worth reading — but stop presenting them as advice.
- [ ] 4.3 Correct `AGENTS.md`'s claim that all five footprint numbers are asserted (round
      ten measured three). This is the prose half of 1.4.
- [ ] 4.4 Correct `AGENTS.md`'s `native_decide` sentence: it says the token appears in
      `Bench.lean`; `grep -c` measures **0** there. The only occurrence is prose in
      `Axioms.lean`.

## 5. Gates

- [ ] 5.1 `nix develop --command lake build` — **10 gate lines**, zero warnings. The new
      asserts change the printed counts, so the header table and `expected*` constants
      must be updated **together**; the gate fails loudly until both are done.
- [ ] 5.2 `nix develop --command openspec validate --all` — 15+ items pass (14 before this
      change plus this one).
- [ ] 5.3 `nix build .#checks.aarch64-darwin.formatting` — the markdown gate. **Not
      `nix fmt`**: this dev shell has no prettier, `nix fmt` formats `*.nix` only and
      prints "0 changed" for markdown it never opened. The check reads the **git tree**, so
      commit first.
- [ ] 5.4 `nix build '.#checks.aarch64-darwin.lean'` — detached with `nohup`, polled, never
      foregrounded.
- [ ] 5.5 Run `scripts/gen-axioms.lean` and `diff` its output against the committed
      `Axioms.lean`. Round ten measured it byte-identical today; confirm it still is, and
      that nothing in this change made the generated regions drift from the generator.

## 6. Recorded, deliberately not in this change

- [ ] 6.1 Any fix for a round-nine or round-ten finding (`benchBurst`'s guard, the
      RFC misquote, the `77 ns/step` cell, `[S5]`'s placement, the `~4–6 ns/step` range).
      They are instances; this change is the class. They are authored against this rule
      afterwards.
- [ ] 6.2 The two other arms' _existing_ non-compliance, if any is discovered beyond the
      three named in §1. The requirement covers them; they are fixed when found, not
      enumerated here.
- [ ] 6.3 `basen-nat-iso` / `basen-uppercase-prepass` — PARKED by the owner.
- [ ] 6.4 A further review round. This change is the answer to "why does every round find
      another one", not a round.
