# Design — `codec-drift-closure`

## D0 — Why this change exists, stated as one measurement

Round nine's review ran **five passes** and tracked where the findings came from. The
last pass's verdict on the gate axis was _"NO FURTHER MUSTS FOUND"_ — and it was right:
the arms are mutation-tested, the vocabulary reconciles, the class table is probed in both
directions. What that same pass produced instead was:

> _"What the last four commits produce is prose-vs-code drift — six instances, all now
> under one id shape (**a claim whose stated method is not its code's method**). …
> That is a documentation failure mode, not a coverage one, and the fix for it is not a
> fifteenth arm: it is that **every number and every method sentence inside
> `Axioms.lean` / `flake.nix` / `round-ten.md` should either be generated or deleted.**"_

So the axis this change attacks is **not** "is there another escape route", it is "does
the sentence match the code". That is a different question and it needs a different tool.

**The measured evidence for the class, from round nine's own review:**

| instance            | the claim                                             | the code                                                      |
| ------------------- | ----------------------------------------------------- | ------------------------------------------------------------- |
| header cell         | `thmInfo 769 — the gated/allowlist partition`         | partition is `427`; `769`/`771` is a _census_                 |
| review file         | "holds every id"                                      | three cited ids missing, three findings sharing one id        |
| vocabulary          | "ordered longest-match-first"                         | list is not length-sorted; nothing asserted                   |
| a check's docstring | "the cross-file comparison is what `lake build` does" | the check compared two lists _inside itself_                  |
| scope word          | "`grep -rn Normalizer Codec/` finds none"             | `Bench.lean:61` constructs one; the **path** excluded it      |
| a range             | `26.97–28.56`                                         | not a cell of any table; `28.56` excludes a committed `28.70` |

Five of the six are the same shape: **a claim whose stated method (a path, an ordering, a
comparison, a run) is not the code's method.**

## D1 — Group A: the re-run, and why nothing less is acceptable

Round nine changed `benchBurst`'s **buffer** (`i % 251`, so a 512-byte window's multiset
changes per call) and its **guard** (non-invariance via `eraseDups`, not `sink == 0`).
Both changes make previously-committed medians measurements of a different program —
`bytesAt` is a different function, and `arrayRead` reads a strided index.

`tasks.md` 2.1/2.3 of round nine record the deferral (owner: _"we can't run benchmarks
yet. We will later."_) and the ledger states plainly that the rows are **pre-§1
measurements**. **Decision: this change takes the run, and deletes the old medians rather
than caveating them.** The reasoning is already on the record in design D1 of round nine
and applies unchanged: a median whose guard could not detect a fold has no evidence
behind it, and keeping it with a caveat reproduces the practice the caveat warns about.
Four performance figures have already been withdrawn here on exactly that basis.

**The run is the whole of Group A.** No analysis is repeated; every quotient and every
derived interval is already re-derivable from the printed medians by the `python3` recipe
in round nine's `tasks.md` §2.2/§2.8.

## D2 — Group B: generate, or delete. Never "remember carefully".

The repository already has one generated number: the footprint **distribution** table,
emitted by `scripts/gen-axioms.lean` into a marked region of `Axioms.lean`, with
`headerNumbers` asserting the counts in the same commit. That is the shape to extend.

**Decision: the README's gate-output block becomes generated.** Today it is a hand-pasted
copy of the check's `logInfo` lines. It went stale **six values out of ten** within one
commit (`8835519`), which is the whole argument: a quotation of an asserted output rots
while the thing it quotes stays green, because nothing connects them.

Two candidate mechanisms, to be settled at implementation by measurement:

1. **A marked region + a generator** — the same `BEGIN/END GENERATED` pattern the
   distribution table uses, written by a script that runs `lake build` and scrapes the
   gate lines. Familiar, and the marker makes the generated region visible in a diff.
2. **A check that regenerates and diffs** — the pattern `checks.mirror` already uses.
   Simpler (no markers in prose), and it fails loudly on drift.

**Prefer (2) if it can be made to work**, because it needs no new convention in a markdown
file and it reuses a mechanism this repo has already mutation-tested. (1) is the fallback
if scraping the build log proves fragile.

**Everything else:** a hand-written count that cannot be derived is **deleted** in favour
of a pointer ("the gate prints this; quote it"). The rule the change installs is
`AGENTS.md`'s existing one — _quote the gate, never a number written in a file_ — made
true of the files it was written in.

## D3 — Group C: the "method sentence" audit, mechanically

The audit has three passes over `Axioms.lean`, `flake.nix` and `Bench.lean`:

1. **Enumerate** every sentence that describes a method: search for the markers `every`,
   `all`, `only`, `in order`, `longest`, `first`, `before`, `grep`, a bare path, and
   `-rn`. That list is itself a vocabulary, so **it gets a denominator** (the count of
   comment lines scanned) in the spirit of round nine's §5.3a — otherwise the audit is a
   filter with nothing auditing it.
2. **For each**, decide: is the property _assertable_? If yes, assert its **effect** —
   the pattern `classifyFootprintClaim` already uses (each phrase must produce its own
   label, which catches a reorder without asserting the ordering itself). If the
   property is a **scope**, assert the scope from the environment the check walks, or
   delete the scope word.
3. **Record** what could not be asserted, in place, with the reason — never leave a
   method sentence that is merely believed.

**Why "assert the effect, not the rule":** round nine tried to assert
"longest-match-first" as a length monotonicity and it **failed on the correct list**
(`` `[propext]`-only `` at 14 precedes `` `[propext]` `` at 9, and the bare form _is_ a
substring of the `-only` form that precedes it, harmlessly). The effect-level assertion —
a segment containing exactly phrase _p_ classifies to _p_'s label — is both true and the
thing that matters. That is the pattern to generalise.

## D4 — Group D: round nine's residue

| open box                       | resolution here                                                                                               |
| ------------------------------ | ------------------------------------------------------------------------------------------------------------- |
| `2.1` (idle-machine run)       | Group A. Closes with the run.                                                                                 |
| `2.3` (restamp the tables)     | Group A. Closes with the restamp.                                                                             |
| `§10.1` (a tenth review round) | **Not commissioned.** This change is the closure of round nine's residue, not a new review.                   |
| `§10.2` (`basen-*` parked)     | **Stays parked.** Owner decision pending the library division. Not touched.                                   |
| `§10.3` (cross-repo)           | **Stays deferred.** Out of scope by owner instruction.                                                        |
| `P4-N3` (`26.97–28.56`)        | Closes with Group A's run — it is a range defect, and a re-run produces the range rather than a substitution. |

## D5 — Archive ordering

This change MODIFIES two requirements in `codec/axiom-gate`, both of which
`codec-gate-denominators` and `codec-audit-round-nine` have already rewritten. The
**live** text was measured against this delta at authoring time (2 requirements, `1 → 3`
and `5 → 6` scenarios, both strict supersets, no live scenario dropped).

**Order at archive time:** `codec-audit-round-nine` must archive **first** — it is the
change whose `tasks.md` this one closes, and it modifies the same two requirements.
Then re-run the scenario-count check on the live spec before syncing this delta. Record
the check in `tasks.md` at the time, do not trust this paragraph.

## D6 — What is deliberately not in scope

- **A tenth review round.** The ninth round's five-pass review is the input; commissioning
  another is the owner's call and is not this change.
- **`basen-*`.** Parked by the owner.
- **Any `Codec` statement change.** Every Lean edit outside `Axioms.lean` and `scripts/`
  is a docstring, so the axiom discipline is unchanged by construction — and the change
  is auditable on that basis.
- **`relRepeat`'s or `takeWhile`'s semantics.** Round nine corrected the prose about them;
  nothing here reopens the mathematics.
