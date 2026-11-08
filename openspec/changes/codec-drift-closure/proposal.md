# Proposal — `codec-drift-closure`

## Why

Ten review rounds have produced **zero soundness defects** and a gate whose arms are
mutation-tested. What they have also produced, unmistakably, is a **second defect class
that no arm is shaped to catch**: _a claim about the tree whose stated method is not its
code's method._

Late in round nine's own adversarial review (five passes, recorded in
`openspec/changes/codec-audit-round-nine/reviews/round-ten.md`) the gate axis went quiet
while the **prose axis did not**. Every one of the last six findings has the same shape:

- a header cell said `thmInfo 769 — the gated/allowlist partition`; the partition is
  `427` and `769`/`771` is the **census**. Two different numbers, one sentence.
- `round-ten.md` claimed to hold "every id" while missing three cited ones and letting
  three findings share one id.
- a table said "ordered longest-match-first" over a list that is not length-sorted.
- a check's docstring described a cross-file comparison the check does not make.
- a range was written by padding one run's value until it covered the other's — **four
  times in one session**, each time introduced while fixing the previous one.

The last of those is the sharpest statement of the class: **the fix for a drift is the
most likely source of the next drift**, because a fix is written in a hurry against a
measurement that is not re-run. A fifteenth gate arm will not close this. The closure is
**structural**: make the numbers that can be generated be generated, delete the numbers
that cannot be attributed, and turn every remaining "method sentence" into an assertion
or into nothing.

## What Changes

### Group A — the benchmark re-run that round nine could not take

Round nine changed `benchBurst`'s buffer (`i % 251`) and its guard (non-invariance, not
non-zero). **So every committed burst median is a measurement of a program that no longer
exists.** `tasks.md` 2.1/2.3 record this and the owner has deferred benchmarking; this
change is where the re-run lands.

- Two idle-host runs, the `python3` re-derivation of every cell, and the **restamp** of
  the three performance tables. This is a re-run, not a re-analysis: the analysis is
  already landed.
- The `P4-N3` item that round nine left open — `26.97–28.56` splices two lanes from two
  sessions — is closed by the same run rather than by another substitution.
- **BREAKING (measurement):** the old medians are deleted, not caveated. A median whose
  guard could not see a fold has no evidence behind it, and this repository has already
  withdrawn four performance figures on that basis.

### Group B — numbers become generated or deleted

- The `README` block that quotes the gate's output is **generated from a real build** by
  a script (`scripts/gen-readme-gate.lean` or a shell equivalent), the way the footprint
  distribution already is, so it cannot rot behind a green gate.
- Every remaining hand-written count inside `Axioms.lean`'s header, `README`'s law
  tables and `flake.nix` is either **derived at build time** or **deleted** in favour of
  a pointer to the log line. The rule to apply: _a number that a reader cannot re-derive
  from a command is a number that will be wrong within one change._
- `AGENTS.md` already says "quote the gate, never a number written in a file". This group
  makes that true of the files it was written in.

### Group C — the "method sentence" audit

A sentence that says _how_ a check works is a claim about code, and nothing checks it.
Round nine's review found five false ones. This group closes the class:

- For every arm in `Axioms.lean` and every `run_cmd`/`checks.*` in `flake.nix`, compare
  the prose to the code and either make the prose a **generated** statement or make the
  code **assert** what the prose says.
- Where a phrase describes an **ordering** ("longest-match-first"), assert the ordering's
  _effect_ (round nine already did this for the footprint vocabulary; the pattern is not
  yet applied elsewhere).
- Where a phrase describes a **scope** ("every `Codec`/`Iso` …", "`grep -rn … Codec/`"),
  either assert the scope from the environment or delete the scope word. Two round-nine
  findings were scope words whose stated path excluded the file that falsified them.

### Group D — round nine's residue and the parked items

- The five boxes round nine did not close (`2.1`, `2.3`, and §10's three records of
  exclusion) are resolved or explicitly re-deferred here.
- **`basen-uppercase-prepass` and `basen-nat-iso` are PARKED by the owner** pending the
  library-division decision. They are **not** in this change's scope and must not be
  started. This change does not guess that decision.

## Capabilities

### New Capabilities

- `codec/docs-conformance`: the repository's prose about its own tree is checked. Covers
  generated-vs-hand-written numbers, the "method sentence" rule, scope-word discipline,
  and the reviewer-id reconciliation that round nine introduced as a one-off flake check.

### Modified Capabilities

- `codec/axiom-gate`: two requirements are extended rather than rewritten.
  `A figure is committed only with the run that produced it` gains the **generated**
  case (a quoted gate output is a figure) and `A stated measurement is a measurement, or
it is a classification` gains the **padded range** scenario — a range that excludes its
  own derivation's endpoints is not a measurement. The delta restates both requirement
  blocks in full, carrying every live scenario, per the archive hazard this repo has hit
  three times.

## Impact

- **`Bench.lean`, `README.md`** — the re-run and the restamp (Group A). Measurements only;
  no `Codec` behaviour changes.
- **`Axioms.lean`, `scripts/`** — new generation step(s) and any arm that Group C adds.
  The pinned counts move and the header must be regenerated and re-asserted in the same
  commit.
- **`flake.nix`** — a generator check alongside the existing `checks.{lean,openspec,
formatting,bench,mirror,reviews}`.
- **`AGENTS.md`** — the "quote the gate" rule becomes enforceable; the lessons section
  gains the padded-range shape and the scope-word shape.
- **No `Codec` declaration's statement changes.** Every Lean edit outside `Axioms.lean` and
  `scripts/` is a docstring, so the axiom discipline is unchanged by construction.
- **Out of scope, by owner instruction:** `basen-*` (parked), cross-repo consistency with
  `../lean-basen` (deferred), and any eleventh review round.
