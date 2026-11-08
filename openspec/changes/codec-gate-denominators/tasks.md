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

- [ ] 0.1 Record the baseline before any edit: `git status --porcelain` empty,
      `nix develop --command lake build` green, and paste all **10** gate lines. Every
      number in the header moves in this change, so the "before" must be in the ledger,
      not remembered.
- [ ] 0.2 Re-read `AGENTS.md`'s Pause signal; play the alarm on every pause.
- [ ] 0.3 Do **not** edit `openspec/changes/archive/**`.
- [ ] 0.4 Do **not** `git stash` / `git reset` / `git checkout -- <file>`.
- [ ] 0.5 **Order:** if `codec-audit-round-nine` is being implemented concurrently, do
      **this change first** (design D5). Its tasks 1.x/6.x assume these arms already
      report denominators.

## 1. Bring the three non-compliant arms into compliance

Design D1 defines the obligation: denominator + removals-decomposed-by-cause, both
asserted. These three arms violate it today.

- [ ] 1.1 **Def classifier** (`Axioms.lean:1357`). It prints
      `{dropped.size} definitions dropped by the name classifier, all reason-recorded` —
      one number for eight patterns. Change the walk to accumulate
      `List (Name × Nat)` (pattern, count) alongside `dropped`, print the decomposition,
      and assert it as a tuple in the style of `expectedFootprintCounts`. Prefer
      `expectedDefPatternCounts` next to the existing constants.
- [ ] 1.2 **Def patterns** (`Axioms.lean:1416`). It prints `derivedDefPatterns.size` — how
      many patterns exist, not how many each matched. That is the _denominator_ with no
      removals. Fold it into 1.1's tuple so one assert covers "each pattern matched
      exactly this many".
- [ ] 1.3 **Footprint arm** (`Axioms.lean:1885`). It prints `skipped` as one number
      covering two unrelated causes. Split into `skipped-other-theorem` (a survey
      paragraph naming other declarations) and `skipped-no-owner` (**no** resolvable name
      in the claim's prefix). Assert both. Round ten measured that `huniq_byte` and
      `decodeRepeat_mem_iff_general` are in the second bucket — the two claims carrying
      `decodeFull_spec`'s hypothesis chain — so the bucket is small and must be reviewed,
      not merely counted.
- [ ] 1.4 Record in the header prose which of the footprint arm's five numbers
      (`scanned / mentioning / found / checked / skipped`) are asserted and which are
      printed-only. `expectedFootprintCounts` asserts three; `scanned` and `found` are
      printed. State it, and state the identity `checked + skipped = found`.
- [ ] 1.5 **Mutation-test each new assert**, one at a time, and paste the failure: - widen a pattern so one count moves → build names the pattern; - narrow the footprint vocabulary so `mentioning` falls → build names it; - remove one attribution rule so `skipped-no-owner` moves → build names it.
      A new check that has not been mutated is not a check (this repo's recorded lesson).

## 2. Hoist `isBareProj` to a single definition

Two `let rec isBareProj` literals exist, at `Axioms.lean:1915` and `:1988`, under a
comment claiming they are one definition. They are not; `run_cmd` blocks cannot share a
`let rec`, so this must become a top-level `def` in `CodecAxioms`.

- [ ] 2.1 Add `def CodecAxioms.isBareProj (env : Environment) (e : Expr) : Bool` beside
      `propProjections`. **The body is the fixed predicate from 3.3, not the existing one.**
      The hoist and the fix are **one edit**, not two: a spike measured that hoisting the
      current bare-`.proj` test and then fixing it would be two passes over the same line,
      and the second would have to revisit every call site.
- [ ] 2.2 Point **both** arms at it; delete both local copies (`Axioms.lean:1915`,
      `:1988`).
- [ ] 2.3 The two arms' outputs **are expected to move** for the five new captures (3.4).
      Record the before/after classification of all twelve captured names, so "it changed"
      is a measured statement with a known cause rather than a surprise.
- [ ] 2.4 **Mutation-test the hoist**: change the shared predicate in one place and confirm
      **both** arms' behaviour moves together. That is the property the comment claims and
      nothing currently checks. Before the hoist this mutation would have moved only one
      arm; after it, both. Say which.

## 2b. The predicate the spike established

A spike (`/tmp/spike-isBareProj.md`) measured and mutation-tested a predicate that meets
all four acceptance criteria with **no name list**. It is reproduced here so the
implementation does not have to re-derive it; it was independently re-run against the
five criteria before being written down.

- [ ] 2b.1 The working definition, verbatim. `peelLamsMdata` strips `lam`/`mdata`;
      `appSpine` decomposes the outermost application spine; `firstExplicitIdx` reads the
      **declared telescope** of the head constant to find the operand being selected from;
      `isProjConst` asks whether the constant's own body peels to a bare `Expr.proj`;
      `isProjOfHyp` recurses. `isBareProj` is a bare `.proj`, or a projection constant
      applied at its first explicit argument to a projection-of-a-hypothesis. See the
      spike report for the source; paste it rather than retyping.
- [ ] 2b.2 **Why it works, in one sentence** (put this in the docstring): a genuine
      projection in this library has a **`proj` body** (`Iso.law`, `And.left`,
      `Subtype.property`, `Codec.Normal.fixed` all peel to `proj#0`), while a proved
      theorem that merely has an `↔`/`∧` **result type** does not (`Codec.bidir`'s body is a
      `let`; `Option.ne_none_iff_exists'` is `Iff.trans`). That is the whole
      theorem-vs-hypothesis distinction — **not** the head constant and **not** the arity.
- [ ] 2b.3 Use `firstExplicitIdx` (from the declared telescope), **not** `args.getLast?`.
      A spike mutation showed the two agree on today's tree — so the wrong one passes every
      test — while `CandAligned_at`'s operand is `args[2]` and `args[7]` is a different
      bound variable. Record this in the docstring: an accessor that agrees by luck is the
      `isDerivedDefName` shape again.
- [ ] 2b.4 Name the predicate's **four** recorded blind spots in its docstring: (1) false
      positive on `fun (x : α × β) => x.1` (safe direction, kept); (2) false negative on a
      named projection constant (closed by `isProjConst`); (3) hypothesis-vs-theorem
      (closed by the operand recursion); (4) an under-applied projection constant would be
      accepted (`args[i]? = none → true`) — unreachable today, and the safe direction.

## 3. Fix the predicate's blind spot — with a measurable acceptance criterion

Round ten measured that the predicate-as-proposed in `codec-audit-round-nine` (accept a
spine ending in a constant from `{And.left, And.right, Iff.mp, Iff.mpr, Prod.fst,
Prod.snd}`) would capture **seven** declarations including `Codec.roundtrip`,
`Codec.findFrom_finds`, `Iso.apply_eq_some_of_unapply` and
`Iso.unapply_eq_some_of_apply`. Four are genuine laws. Do not implement that.

- [ ] 3.1 Reproduce the measurement first. Walk every public `thmInfo` in `Codec`/`Iso`,
      peel `lam`/`mdata`, decompose the application spine, and print the head constant and
      arity. Confirm the seven. Paste the output.
- [ ] 3.2 `#print` the body of each of the seven and record which argument the head
      constant is applied to. The distinguishing fact: `roundtrip` unwraps
      `Codec.bidir d x n s` (a **proved theorem**); `unapply_eq_some_of_apply` unwraps
      `Iso.law i a b` (a **field**). Arity cannot separate them — both are 4.
- [ ] 3.3 Implement a predicate that separates them structurally. **Do not** accept
      `Iff.mp`/`Iff.mpr` on head-and-arity alone, and **do not** use "`And.left`/`And.right`
      at their declared arity": a spike measured that `And.right` is reached at arity 8 in
      `CandAligned_at` and arity 3 elsewhere, so "declared arity" is a category mismatch,
      not a mechanism. The predicate that works is in §2b — a **projection constant** (its
      own body peels to a bare `Expr.proj`) applied, at its first explicit declared
      argument, to something recursively a projection of a hypothesis.
- [ ] 3.4 **Acceptance criterion — all four must hold, measured:** - `Codec.roundtrip` **stays gated** (this is the one that matters); - `Codec.findFrom_finds` stays gated; - `CandAligned_fst` and `CandAligned_at` are classified as projections; - `Codec.CandAligned_tail` **stays gated** — it is a real proof about an invariant
      (`And.casesOn hal fun hlen hpt => ⟨…, …⟩`), not a projection. Round nine's task 6.3
      would have moved it; that is wrong.
      A predicate meeting fewer than four is rejected, and the rejection is recorded.
- [ ] 3.5 **Decided by measurement, record it in place.** `Codec.fill_fixed`
      (`Codec/Normal.lean:163`) **stays gated**: its operand is `Codec.fill nz s`, a
      **constructed value**, not a caller-supplied hypothesis — `isProjConst Codec.fill` is
      `false`, so the recursion rejects it for the same principled reason it rejects
      `Codec.bidir`. (It has zero _theorem_ consumers, but `Bench.lean:103` calls it, so
      "zero consumers" would have been wrong.) Add the one-line comment to the pin saying
      why, so the next round does not re-open it.
- [ ] 3.6 **Decided by measurement.** `Codec.packedCands_mem` (body `c.property.1`) is
      **classified with the projections**. It is a genuine selection, and it must be added
      to `propProjections` with a reason carrying the caveat: it asserts nothing, but it
      _names_ a membership (`c.val ∈ decodeArray d a k`) that callers would otherwise spell
      out, so it earns its keep as documentation. Do not drop it; do not leave it gated and
      uncommented.
- [ ] 3.7 Update the predicate's docstring to name **all four** blind spots. See 2b.4. The
      one currently missing is the one that cost a round.
- [ ] 3.8 **The footprint count falls by five, and the gate will say so.** The five new
      captures are pinned today: `Axioms.lean:821-823` (`CandAligned_fst`/`_at`), `:1063`
      (`packedCands_mem`), `:1147` (`apply_eq_some_of_unapply`), `:1162`
      (`unapply_eq_some_of_apply`), plus their `#print axioms` blocks at `:2077`, `:2080`,
      `:2803`, `:3055`, `:3100`. Re-run `scripts/gen-axioms.lean`, then update the header
      table and the `expected*` constants **together**. `CandAligned_tail` **stays pinned**
      — it is gated, correctly.
- [ ] 3.9 `propProjections` gains the five entries from 3.4/3.6, or the **completeness**
      arm fails the build. That failure is the predicate doing its job, not a regression.
      Once they are listed, the **validity** arm checks each one — the two-directional
      discipline the file already claims.

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
