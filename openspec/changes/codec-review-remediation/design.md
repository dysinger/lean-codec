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

## Goals / Non-Goals

**Goals:**

1. Remove every finding that can cause a **wrong implementation** or a **false
   sense of assurance**: the `Bytes` contradiction, the unenforced gate, the
   incomplete leak catalogue, the unpinned seam, the unreachable seam check, and
   (`R5.1`) the decode path's 588× recursion-scheme defect plus the "20–40×"
   claim that hides it.
2. Make the documentation's _derivations_ as accurate as its quotations.
3. Leave exactly one home for each fact, and delete the duplicates rather than
   reconciling them in place.

**Non-Goals:**

- No theorem, proof, or `[D#]`/`[S#]` anchor change. No new mathematics. **One
  narrow exception:** §6 may change `decodeFull`/`decodeRepeat`'s recursion
  scheme, because `R5.1` measures a 588× defect there. It must keep every
  theorem's statement, prove the new definition equal to the old, and preserve
  the axiom discipline — see D9.
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
_Fix:_ copy the honest phrasing. Wiring `commitRemainder` into the packed path
needs an equality law between two transports, a proof change of its own weight;
this change corrects the header and points the docs at the cursor path (task
6.3, option (a)) unless that turns out cheap.

### D9 — A measured CRITICAL joins the audit, and it earns the one shape-changing carve-out

R5.1 was found by **building and running** the binary, after the four reading
lenses had completed. It is a CRITICAL: `decodeFull`/`decodeRepeat` use
`WellFounded.fix` on `Sigma fun k => Bytes k`, which does not compile to a loop,
and an equivalent structural fold over the same types on the same inputs is
**588× faster at n=4096 with a bit-identical result**. Decode therefore runs at
~0.01 MiB/s, and the "20–40× off C" ceiling asserted in `README.md:515` and
`AGENTS.md:171` is false by ~4 orders of magnitude on the path it most obviously
describes.

_Decision:_ it goes into **this change**, as §6, and not into a separate one.
Three reasons:

1. **It is an audit finding.** The change's mandate is to remove false assurance
   from the docs and the code they describe. A documentation claim refuted by
   4 orders of magnitude is exactly that, and it is CRITICAL by the review's own
   severity key (a claim not upheld, at the level where it misleads an
   implementer).
2. **Splitting would recreate the defect.** §3 rewrites `README.md`
   §Performance and §4 rewrites the `AGENTS.md` bullet. If the numbers are
   corrected against a snapshot taken _before_ §6.1, the change would canonize
   the defect it just measured. The two edits must be in one change so the
   claims and the fix are reconciled together.
3. **`AGENTS.md`'s one-change-at-a-time rule** argues for this: a second,
   concurrently-open change in this repo is what the rule forbids.

_Consequence — the carve-out._ §6.1 changes a **definition's shape**, which the
tasks file previously forbade outright. That prohibition is amended, narrowly:
§6 may change the recursion scheme, but must keep every theorem's statement,
prove the new definition equal to the old (a `…_eq` bridge), and preserve
`[propext, Quot.sound]`-only with zero `Classical.choice`, zero `sorry`, and
`#eval`-ability. Nothing else in the change may change a declaration shape.

_Rejected:_ (i) a separate `codec-decode-fast` change — see reason 2, it
recreates the split this change exists to close; (ii) recording the finding
without a fix — that leaves a CRITICAL open in a change whose output the next
session will trust; (iii) fixing only the docs — that would make the docs honest
about a defect instead of removing it, which the owner's standing preference
("most correct, not most convenient") rules out.

_Ordering._ §6.1 lands before §6.2, and both before §3.x/§4.x, so the corrected
claims quote the **fixed** numbers rather than a snapshot of the defect.

## Risks / Trade-offs

- **§6.1 touches the recursion scheme of the two most-proved functions in the
  tree.** `decodeFull_some`, `decodeFull_ne_none`, `decodeFull_spec`,
  `decodeRepeat_eq`, `decodeRepeat_spec` and the `relRepeat` family all cite the
  current equations. → Mitigation: a `…_eq` bridge that states the new definition
  equals the old, then every existing proof is rewritten through it rather than
  re-derived. If a proof cannot survive the bridge, that is a signal the new
  definition is genuinely different and must be reconsidered, not patched.
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
