# Tasks — `codec-gate-denominators`

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

- [ ] 2.1 Add `def CodecAxioms.isBareProj (e : Expr) : Bool` beside `propProjections`, with
      the body of the existing predicate unchanged.
- [ ] 2.2 Point **both** arms at it; delete both local copies.
- [ ] 2.3 Confirm the two arms' outputs are unchanged by the hoist (same counts, same set)
      — a refactor that moves a number is a behaviour change wearing a refactor.
- [ ] 2.4 **Mutation-test the hoist**: change the shared predicate in one place and confirm
      **both** arms' behaviour moves together. That is the property the comment claims and
      nothing currently checks. Before the hoist this mutation would have moved only one
      arm; after it, both. Say which.

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
- [ ] 3.3 Implement a predicate that separates them structurally. Accept either:
      (a) `And.left`/`And.right` at their declared arity only, which round ten measured
      captures exactly the three true Prop-selectors; or (b) the above plus a **recursive**
      test for `Iff.mp`/`Iff.mpr` requiring the iff argument to itself be projection-headed
      on a bound variable.
      **Do not** accept `Iff.mp`/`Iff.mpr` on head-and-arity alone.
- [ ] 3.4 **Acceptance criterion — all four must hold, measured:** - `Codec.roundtrip` **stays gated** (this is the one that matters); - `Codec.findFrom_finds` stays gated; - `CandAligned_fst` and `CandAligned_at` are classified as projections; - `Codec.CandAligned_tail` **stays gated** — it is a real proof about an invariant
      (`And.casesOn hal fun hlen hpt => ⟨…, …⟩`), not a projection. Round nine's task 6.3
      would have moved it; that is wrong.
      A predicate meeting fewer than four is rejected, and the rejection is recorded.
- [ ] 3.5 Decide `Codec.fill_fixed` (`Codec/Normal.lean:163`) deliberately. Its body is
      `(fill nz s).fixed`, its docstring says "not a separate law", it has **zero
      consumers**, and it is gated. Classify it with the projections and extend the
      predicate to see a head constant whose own body is a projection — or keep it gated
      and record why. Either is defensible; silence is not.
- [ ] 3.6 Decide `Codec.packedCands_mem` (body `c.property.1`) deliberately. It is a
      projection but it _names_ a membership callers would otherwise spell out. Record the
      decision and the reason.
- [ ] 3.7 Update the predicate's docstring to name **all three** blind spots it has had:
      the false positive on `fun (x : α × β) => x.1`, the false negative on a named
      projection constant, and the new hypothesis-vs-theorem distinction. The docstring
      currently records two of the three, and the missing one is the one that cost a round.

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
