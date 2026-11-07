# Design — `codec-audit-round-six`

## Context

`codec-audit-round-five` closed 46/46 and archived 2026-11-07. Round seven audited
the result with three read-only workers and found **33 defects, 10 refutations, zero
soundness failures**. Every MUST is a claim about the mathematics that measurement
contradicts.

All findings are `R7-nn` in the merged ledger `/tmp/r7-SYNTHESIS.md`; reports are
`/tmp/r7/{A,B,C}.md`. Note the numbering is off by one from the change name:
`round-six` is the **sixth** audit _change_, its findings come from the **seventh**
review round, so the ids are `R7-nn`.

## Goals / Non-Goals

**Goals**

- Close the footprint-prose class structurally, not with eleven edits.
- Make `basen`'s gate incapable of the two defects found: a dead branch and a count
  that can be evaded by formatting.
- Make the three documents that describe the bench lane agree with the lane.
- Repair every false claim in `README.md`, including one this project introduced
  while fixing the previous instance of the same class.

**Non-Goals**

- No statement weakened, no decoder/encoder behaviour changed.
- No bench lane re-timed.
- Not re-auditing; acting on round-seven findings.
- The 12 `native_decide` bench uses stay (the lemma that would convert them still
  does not exist).

## Decisions

### D1 — The footprint check is a gate arm, and it lands first

**Measured.** Eleven docstring sites state a footprint `#print axioms` contradicts,
in **both** directions (six "Axiom-free" claims that are not; one
`[propext, Quot.sound]`-only claim that is stronger than truth; one "No axioms at
all" that is `[propext]`; plus two restatements). `Axioms.lean`'s six `run_cmd`s
assert theorem-set _counts_ and pin _membership_ and never compare a stated
footprint with `collectAxioms`'s answer.

**Decision.** Add a def-side-style audit arm over `Codec`/`Iso` docstrings: extract
each stated footprint, compare with `collectAxioms`, fail naming declaration, stated
and measured. Run it in `lean-codec` and port the pattern to `basen`.

**The hard part is attribution, and it is the design.** A's prototype oracle produced
29 mismatches, most of them false positives, because a docstring that surveys several
declarations (`def LengthDet` carries the whole four-way table) is read as claiming
its own footprint. Three options were considered:

1. **Require the claim to name its declaration in backticks in the same sentence.**
   Chosen. It is a small, checkable convention, it forces the docstrings to be
   unambiguous, and it makes a misattributed claim _visible_ rather than silently
   filtered. The eleven existing sites mostly already name the theorem in prose; the
   ones that do not are corrected as part of §1.
2. Restrict the check to the last paragraph of a docstring. Rejected: an arbitrary
   positional rule, and the surviving case is exactly the surveyed table.
3. Parse which declarations a docstring "is about" by matching identifiers to the
   environment. Rejected: it is the same heuristic as (1) with more failure modes,
   and its failures are silent.

**Rejected alternative considered and worth recording:** making every docstring
footprint claim a `#guard_msgs`-checked comment instead of prose. That would be
stronger than a `run_cmd`, but it puts a machine block in every docstring and the
projection onto reader-facing prose is lost.

### D2 — The check runs in both directions

A claim that is **too strong** is a false statement; a claim that is **too weak**
understates a result. Round seven found both (`relUnambiguous_of_relAligned` and
`relUnambiguous_not_implies_relAligned` are axiom-free while claimed
`[propext, Quot.sound]`-only — and those are the strongest possible evidence for the
four-way diagram, so the understatement hides the file's best result). Both fail.

The one exemption is a lower bound written as a lower bound: `[propext]`-or-cleaner
phrasing is not a claim of an exact set, and the check SHALL treat a hedged claim as
satisfied by any footprint within the hedge. `Normal.lean`'s "`[propext]` or no
axioms" is the model and is verified correct.

### D3 — `[S1]`'s number is right and its sum is wrong; do not "fix" the number

**Measured** (my own environment walk, not relayed): **19** `Iso`-valued public
defs, and the list includes `Codec.uniqSeqIso` and `Codec.uniqSeqUnitIso`.

The README says "finds **19** …: the 13 above, plus `foldl`, `foldr`, `counterIso`
and `counterIsoR`" — 13 + 4 = 17. The total is right; the decomposition is wrong,
because two witness isos in `Codec/Sound.lean` are in neither part. Reviewer B
reported this as "should be 21"; that is **refuted** — B counted the 13
parameterised isos as missed. Recorded in §9 so it is not re-derived.

**Decision.** Repair the sum and the "two counterexample witnesses" → four. Do not
change the 19.

### D4 — `basen`'s bench lane: fix the code, not the documents

Three documents describe a `main` that runs work; the code is `pure ()`. Two fixes
are possible:

- (a) make `main` actually assert the vectors — keeps the documents true, costs a
  runtime lane for checks that already fail at elaboration;
- (b) delete the execution and rewrite the prose — accurate to today's tree.

**Decision (b).** The checks are _compile-time_ by nature (`rfl` and
`native_decide` both fire during elaboration), so executing the binary adds nothing
and the `installPhase` run is ceremony that has already misled three documents.
Making `main` do redundant work to justify a sentence is the wrong direction. The
`AGENTS.md` bullet is rewritten to say the checks fail at **build** time.

**But the `nix build '.#bench'` check stays**, and its purpose is restated honestly:
it is the proof that the lane _builds_ in the sandbox, which is a different claim
from "the values were checked at runtime".

### D5 — `derivedDefPatterns`' sibling: fix the escapes, do not delete the check

`nativeDecideCount` compares whole lines. A trailing comment, an inline `by`, or two
on one line are all invisible. Measured: adding a trailing comment moves the count
`12 → 11`.

**Decision.** Truncate each line at `--`, strip both ends, and additionally assert
`uses ≥ tacticLines` so a comment-inflation is caught too. Keep the check: deleting
it would restore exactly the drift it exists to catch, and the prose sentence it
guards is one this change is otherwise correcting.

### D6 — base16: prove the link, and scope the README row

RFC 4648 §8 is met by `decodeHexFold`, which has case-folding laws but **no**
roundtrip. Every base16 law (roundtrip, canonical, `_char`, `decode_encode_inverse`,
`encode_injective`) is stated over the strict `hexElem`.

**Decision.** Prove `decodeHexFold (encodeHex bs) = some bs`. The pieces exist:
`foldList_hexBlockUnapply` gives the fixed-point hypothesis and `decodeHexFold_of_fixed`
consumes it. If it proves awkward, the fallback is to scope the README's §8 row to
"§8 _canonical encoder_; lowercase acceptance is an opt-in decode wrapper with no
roundtrip" — recorded here so the decision does not return.

### D7 — The dead branch is replaced by the identity the table needs

`basen`'s definition check has `defs.size - allow.size + allow.size != defs.size`,
which is false for all inputs (verified by exhaustive enumeration). It reads like the
live theorem-side `gated + allow != pub.size`.

**Decision.** Replace with `mentionedCount + allow.size != defs.size`. The three
`expected*` equalities already do the real work; this restores the sum check the
comment claims.

### D8 — The `Rab` family is strengthened, aliased, and de-orphaned

`Rab_fails_huniq` is the `¬∀`-over-lists form; the prose citing it claims
`LengthDet` + productivity. `uniqCounterexampleRel` has the `∃`-form
(`huniq_not_derivable_full`); `Rab` does not, even though `Rab` is the _stronger_
witness.

**Decision.** Add `Rab_fails_huniq_full` (a one-liner on four existing theorems),
and record in `Rab`'s docstring that it is deliberately the same relation as
`uniqCounterexampleRel` — renamed so the round-five retraction reads independently.
Deleting `Rab` instead was considered: rejected because the round-five prose cites
`Rab` by name in three places and a second name for a witness is cheap; the defect
was that the _prose contrasted_ them as if they differed.

### D9 — Performance caption: state the span per row

Table 4's caption says "512 steps per burst (the window every row here decodes)",
but its `idealCursor` row is `10532 / 4096 = 2.57`. This is the R6-26 defect,
reintroduced in a newer table while the older one was being fixed.

**Decision.** Give the span per row, as table 1 already does. Do **not** re-run the
lane: the figure is correct for its own span and only the caption is wrong.

## Risks / Trade-offs

- **[The new arm is noisy]** → it must be, or it is not checking. Attribution is by
  the backticked-name convention (D1), so noise means a docstring that does not say
  whose footprint it states; the fix is in the docstring.
- **[The arm cannot see a docstring that names no declaration]** → it treats the
  absence as "no claim", which is the safe direction: silence is not a false claim.
- **[D6 may not close]** → the fallback is a scoped README row, recorded.
- **[D4 changes a Nix derivation]** → `nix build '.#bench'` must still pass; it
  builds the lane in the sandbox, which is the claim that survives.

## Migration Plan

1. **§1 the footprint arm** first — it is the mechanism, and its build failure _is_
   the list of docstrings to fix.
2. **§2 `basen`'s gate** — dead branch, two stale figures, escapes, exclusions arm.
3. **§3 the `Rab` family** — strengthen, alias, orphan.
4. **§4 base16** — the §8 roundtrip, or the scoped row.
5. **§5 README** — `[S1]`'s sum, the phantom name, the caption, the dead links.
6. **§6 the rest** — pin lag, CHANGELOG SHAs, template prose.
7. **§7 regenerate** `Axioms.lean` once, at the end.
8. **§8 gates and commit.**
