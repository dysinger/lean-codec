# Proposal — `codec-gate-denominators`

## Why

Ten adversarial review rounds have produced **zero soundness defects**. Round six's
502-constant sweep found no `Classical.choice` and no `sorry`; rounds nine and ten
re-measured 30+ footprints and found none. The library proves what it claims.

What the rounds _have_ produced — in every round from five onward — is **one recurring
defect class, fourteen times over**:

> **a check whose input has a filter that nothing audits.**

The instances, in the order they were found:

| #   | round | the check                       | what entered it silently                                         |
| --- | ----- | ------------------------------- | ---------------------------------------------------------------- |
| 1   | 5     | `isDerivedDefName`              | dropped `Iso.prod`, the paper's own `×`                          |
| 2   | 5     | def-coverage proxy              | satisfiable by an identity unfold                                |
| 3   | 6     | footprint enumeration           | `#print` sweep missed 15 of 26 claims                            |
| 4   | 7     | `nm.getPrefix == \`Codec`       | removed 139 declarations before the docstring was read           |
| 5   | 7     | status-sink `(…).length`        | folded the whole decode away — the withdrawn `3 ns/call`         |
| 6   | 7     | attribution rule                | a docstring naming its own ingredient had its claim thrown away  |
| 7   | 8     | `opaqueInfo`/`axiomInfo`        | matched by **no arm** of eight                                   |
| 8   | 8     | `propProjections` validity      | docstring said a bad entry "would fail"; nothing checked         |
| 9   | 8     | footprint denominator           | printed how many claims it _read_, never how many existed        |
| 10  | 8     | `gen-axioms.lean`'s mirror list | three entries to the real list's four; silently un-pinned a law  |
| 11  | 9     | `benchBurst`'s guard            | tested `sink == 0` against the _outer_ accumulator, not the sink |
| 12  | 9     | `isBareProj`                    | matched `Expr.proj`; `hal.1` elaborates to `And.left hal`        |
| 13  | 10    | two `isBareProj` copies         | a comment claims "one definition"; they are two `let rec`s       |
| 14  | 10    | `skipped = 8`                   | sums a survey paragraph with a claim that has no owner           |

Each was fixed individually. The class did not stop, because **fixing an instance does
not change the rule a new arm is written against.**

The repo's own spec already contains half the rule — `codec/axiom-gate`'s
"A gate name-list asserts the property it exists to represent". But it covers _lists_,
and only about half the instances were lists. #5 and #11 were a wrong _variable_; #9 and
#14 were an un-decomposed _total_; #13 was two copies of a _predicate_.

## What Changes

A **gate precondition**: every `run_cmd` arm in `Axioms.lean` SHALL report

1. **what entered it** — its denominator, the universe it claims to cover; and
2. **what was removed from that input, decomposed by the reason for removal.**

and both numbers SHALL be **asserted** (a build failure when they move), not merely
logged. An arm that cannot state a denominator SHALL say so and say why, in a recorded
allowlist, rather than printing a bare total.

Concretely, the three arms that violate this today:

- **def classifier** (`Axioms.lean:1357`) prints `dropped.size ... all reason-recorded` —
  one number for **eight** patterns. A pattern removing exactly one declaration (`eq`,
  `go`, `below`, `brecOn`) is one rename from matching nothing.
- **def patterns** (`Axioms.lean:1416`) prints `derivedDefPatterns.size` — how many
  patterns exist, not how many each matched.
- **footprint arm** (`Axioms.lean:1885`) prints `skipped` as one number covering two
  unrelated causes: a survey paragraph naming other theorems, and a claim with **no
  resolvable owner**. The two claims carrying `decodeFull_spec`'s hypothesis chain
  (`huniq_byte`, `decodeRepeat_mem_iff_general`) are in the second bucket, and nothing
  distinguishes them from a legitimate survey.

Plus the duplication the rule exposes: **`isBareProj` exists twice** in one file
(`Axioms.lean:1915` and `:1988`), under a comment asserting "one definition … so they
cannot drift apart." They can, and they are not one definition.

## Capabilities

### New Capabilities

None.

### Modified Capabilities

- `codec/axiom-gate`: the existing requirement on name-lists is generalized to **every
  arm**, and gains the denominator/decomposition obligation as a precondition on adding
  an arm. Two scenarios are added to the footprint requirement (skips reported by cause)
  and one to the partition requirement (per-pattern counts). Each affected requirement is
  restated in full in the delta so no live scenario is dropped — the archive hazard this
  repo has hit three times.

## Impact

- `Axioms.lean` — three arms gain decomposition; `isBareProj` hoists to one definition;
  the header table gains three asserted tuples.
- `scripts/gen-axioms.lean` — its own copy of `authored` is folded into the shared list.
- `AGENTS.md` — the lesson is rewritten from "ask what removes things from a check's
  input" (a question a reviewer may forget) to a **precondition on adding an arm** (which
  the build enforces).
- **No `Codec` declaration changes.** This change touches gate machinery and its prose.

## What this change deliberately does not do

It does not fix the fourteen instances. Every one of them is already closed. It
establishes the rule that would have prevented them, so that the fifteenth is a build
failure rather than a review finding — and so that the audit rounds can stop being the
mechanism by which the gate stays honest.
