# Design — `codec-review-remediation`

## Context

Four adversarial reviews produced 74 findings across four lenses; `review.md`
holds the verbatim reports and an id-indexed table (`R1.1`…`R4.22`). This design
records only the _judgement calls_ — which findings to fix, how, and which to
decline — because the findings themselves are already evidence-backed.

The constraint set is unchanged from the library's own rules:

- **One source of truth per concern** (`AGENTS.md`). Several findings are
  _duplication_ defects (a fact in two places, one copy stale) and the fix is
  deletion, not addition.
- **`[propext, Quot.sound]`-only, zero `sorry`.** Two findings are about whether
  this is _enforced_; the fix must not introduce `Classical.choice` itself (e.g.
  by reaching for a classical lemma in the gate script — it is a shell script, so
  no risk, but the principle stands).
- **The quotations are correct; the derivations are not.** R1 found the paper
  citations verbatim-accurate and the _reasons_ wrong. So this change edits
  reasoning and leaves quotations alone.
- **Verified-clean claims stay untouched.** `review.md` lists what was tested and
  held (`Iso.law` has no escape hatch, zero `sorry` in the tree, all four C seams
  match on reachable inputs). Re-litigating those would be waste.

## This change reopens the two "complete" changes

`codec-normal-form-case-quotient` (16/16) and `basen-rfc-conformance-theorems`
(31/31) were marked complete on the strength of their own task lists, then the
review found 2 CRITICAL defects in that same work. A change is not complete while
its own docs and gate are defective, so:

- both carry a `STATUS: NOT COMPLETE — DO NOT ARCHIVE` banner in their `tasks.md`;
- both are reopened here;
- nothing is archived until §1–§4 of `tasks.md` is green.

This is a **correction of a completion claim**, not a new workstream. The 41 tasks
are the remainder of the previous two changes' work.

## Goals / Non-Goals

**Goals:**

1. Remove every finding that can cause a **wrong implementation** or a **false
   sense of assurance**: the `Bytes` contradiction, the unenforced gate, the
   incomplete leak catalogue, the unpinned seam, the unreachable seam check.
2. Make the documentation's _derivations_ as accurate as its quotations.
3. Leave exactly one home for each fact, and delete the duplicates rather than
   reconciling them in place.

**Non-Goals:**

- No theorem, proof, or `[D#]`/`[S#]` anchor change. No new mathematics.
- No rewrite of `README.md`'s structure. The anchors are cross-referenced by
  code and downstream repos; only the text under an anchor changes.
- No attempt to fix R2's INFO findings — they are verifications, kept in
  `review.md` so nobody re-runs them.
- No claim that the global skill file is fixed by this change; it lives outside
  the repo, so the task is recorded with the external path and performed last.

## Decisions

### D1 — The `Bytes` contradiction is a CRITICAL doc bug, and the fix is one line plus a pin

`CHANGELOG.md` says `abbrev Bytes := List UInt8`; `Codec/Codec.lean:68` says
`abbrev Bytes (n : Nat) : Type := Fin n → UInt8`. The README's whole
"Representations" section argues the `List` carrier was _the defect_ removed, and
the `Classical.choice`-leaking `Array.extract`/`toList` transport lemmas were the
reason. A reader implementing from the changelog reintroduces exactly that.

_Fix:_ correct the changelog entry, and add a row to `AGENTS.md`'s truth table
pinning `Bytes n := Fin n → UInt8` with a citation to the source line. The pin is
the durable half — a corrected changelog can drift again; a precedent saying
"the changelog is not the definition" cannot.

_Rejected:_ deleting the changelog entry. `CHANGELOG.md` is the record of what
landed; the entry's _existence_ is correct, only its type spelling is wrong.

### D2 — The zero-`sorry` gate becomes real via `-DwarningAsError`, not a grep

Two candidate enforcement mechanisms:

- **`grep` for `sorry`/`admit`.** Cheap, but it is a second source of truth about
  what counts as an incomplete proof; it misses `admit`, misses a generated
  `sorryAx` from a tactic, and needs its own tests.
- **`lake build -DwarningAsError=true`.** The compiler already emits
  `declaration uses 'sorry'`; promoting warnings to errors makes the _compiler_
  the authority. One flag, no parallel lint, and it also catches the other
  warnings a proof edit tends to introduce (unused simp args, deprecations),
  which is a bonus consistent with `AGENTS.md`'s "zero warnings" phrasing.

_Decision:_ `-DwarningAsError=true` on the `check` derivation. _Risk:_ if the tree
has pre-existing warnings, the flag fails the build for reasons unrelated to
`sorry`. Mitigation: the task's first step is to run the build with the flag and
enumerate any hits; each is then fixed or, if it is a deliberate deprecation the
toolchain emits for code we must keep, suppressed at that site with a comment.
Only a green run lands the flag (see `tasks.md` 1.3). **Verified at planning
time:** `lake build` in `lean-codec` emits **zero** warnings today
(`Build completed successfully (13 jobs)`, no `warning:` lines), so the flag
should land without pre-existing fallout. The only known deprecation warnings in
the ecosystem are `if_pos`/`if_neg` in `../lean-basen`'s new Base16 code — a
different repo, outside this gate.

_Rejected:_ asserting it in prose only. That is the status quo and the finding.

### D3 — The `Classical.choice` catalogue moves to the ergonomics section, and the history mention becomes a pointer

`AGENTS.md` currently has the two new shapes as a parenthetical inside the
`../lean-basen` 7.3 history block, and one shape (the original) in
"Lean proof ergonomics". A reader with a dirty law reads the ergonomics section;
so the catalogue belongs there, complete. The history block's copy is _reduced to
a pointer_, not kept in parallel — the file's own header forbids facts living in
two places.

The catalogue is ordered by _how you hit it_, not by severity: (1) dependent
elimination on a length equation, (2) disjunctive `omega` under `decide_eq_true`,
(3) `Bool` match in the goal. Each gets a probe and a clean spelling. Probe (2) is
two lines and reproduces deterministically; probe (3) needs the goal's shape, so
it is described rather than listed as a runnable snippet.

### D4 — `byteSlice_spec` is added because the seam's contract has no checkable referent

The C header says "the C matches the Lean body". For `blitBytes` and `findByte`
there is a theorem spelling out the body; for `byteSlice` there is only the body
and prose. So the trust argument is asymmetric for no reason:
`byteSlice` is the seam every comment calls "the specification", and it is the one
without a law.

_Fix:_ `byteSlice_spec`, a `rfl` identity (the reviewer verified it compiles), and
have `commitRemainder_spec` and the bench cite it. This is a _pure addition_ — no
statement changes.

_Note on axiom uniformity:_ `findByte_spec` reports `[propext]` while its siblings
report none, because `Array.findIdx?` goes through `DecidableEq UInt8`. The
reviewer's R2.6 asks for this to be stated per-law. It is a docstring fix, not a
proof fix — `[propext]` is inside the gate.

### D5 — The bench's seam checks move to the front; the crashing lane is fixed separately

R2.2 is two coupled defects: (a) the seam value-checks are sequenced last, and
(b) an earlier lane (`benchScalarIndexRead`) aborts at small sizes. The
_remediation_ is (a) — move the checks to the top of `main`, since they need no
scaling parameter and are cheap. That makes the seam evidence reachable regardless
of (b). (b) is fixed too, because a bench that crashes on a default invocation is
its own defect, but the ordering change is what restores the assurance the docs
claim, so it lands first and is not contingent on diagnosing (b).

_Rejected:_ fixing only (b). Any future lane that aborts would again silently
disable the seam evidence.

### D6 — `README.md`'s `[D2]` is refiled, not rewritten

R1.2 found `[D2]` sits under "Departures (observable-semantics changes)" while its
body says "`codec` keeps it that way". Two options: (i) rewrite the body to claim
a departure, (ii) move the entry. The true state is that `decode` returns the
_unfiltered_ pair list where the paper's `parse` filters to whole-string matches —
that is a **superset** of the paper's relation, i.e. a strengthening, not an
observable semantic change to `Rel` (which the README's own law states correctly).

_Decision:_ refile under `[S#]`, keeping the anchor id stable (the anchor is cited
by code and by `../lean-basen`), and add a one-line note that the id is retained
for continuity despite its new section. _Rejected:_ renumbering — it would break
every cross-reference for a classification fix.

### D7 — The global skill is split, and this change only tracks it

R4.2 found ~130 project-specific hits in a file whose own header promises "no
project names/paths". R4.3 found the file's precedence clause silently voids its
own stricter gate (the official `lean4` skill permits `Classical.choice`; this one
forbids it).

_Decision:_ the generic half stays in `SKILL.md`; the project-specific body moves
into this repo (an appendix referenced from the skill with one line). This is a
task with an external path (`~/.pi/agent/skills/lean/SKILL.md`), performed last,
and deliberately **not** part of this repo's `lake build` gate — a skill file
outside the tree cannot be gated here, and pretending otherwise would be the kind
of false assurance this change is removing.

### D8 — `Packed.lean`'s header is corrected toward `ByteSlice.lean`'s honest wording

`ByteSlice.lean` says plainly that `byteSlice` has no library-internal caller.
`Packed.lean` says the memcpy is "deferred to a `commitRemainder` at commitment
time", which is false — the proven decoder uses a list-materializing transport.
_Fix:_ copy the honest phrasing. Not wiring `commitRemainder` into the packed path
would be a proof/perf change (it needs an equality law between two transports),
which is out of scope here and would be its own change.

## Risks / Trade-offs

- **`-DwarningAsError` may surface latent warnings** → good, but it can fail the
  build for an unrelated pre-existing warning. Mitigation: run it first, fix or
  document each, and land the flag only when green.
- **Moving `[D2]` between sections changes the README's narrative order** →
  mitigation: keep the anchor id and add the continuity note (D6).
- **The skill split touches a file outside the repo** → it cannot be gated here.
  Mitigation: record it as an explicit external-path task so it is not forgotten,
  and do not claim the repo's gate covers it.
- **Fixing R1's derived reasoning risks re-litigating settled design** → the
  review's `Verified-correct` section pins what not to touch; the tasks cite it.
- **`byteSlice_spec` is a `rfl` and adds no assurance beyond the body** → true,
  and that is the point: it makes the body a _referenced_ specification, so the
  C's contract points at a theorem instead of at "read the def".

## Migration Plan

Additive and doc-only except for two code additions (`byteSlice_spec`, bench
reordering) and one build-flag change. No downstream change is required: no
declaration changes shape, no `[D#]`/`[S#]` id is removed, and
`../lean-basen` continues to compile untouched.

Order: (1) the three cross-lens-corroborated defects (substrate type, gate,
catalogue); (2) the code/seam items; (3) README derivations; (4) `AGENTS.md`
process defects; (5) the external skill.

## Open Questions

- Should `bench`'s crashing scalar-index lane be fixed or deleted? Decision
  deferred to the task: fix if the bug is local, delete the lane if it is a
  measurement that no longer earns its place. Either satisfies D5.
- Should `Iso.element`/`Iso.subset` (R2.5, dead API) be deleted or retained as
  public API? Leaning retain-with-a-note, since `[D8]`'s decidable-witness
  argument is about exactly these two, and `[D8]` is being corrected to cite them.
