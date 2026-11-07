# Design — `codec-audit-round-five`

## Context

`codec-audit-round-four` (52/52) archived 2026-11-07 and closed three classes:
a refuted predicate-ordering claim, four advertised-but-absent laws, and a shipped
`basen` gate port. Round six audited the result and found that **the gate's filter
had no audit arm** — the same weakness round four identified for _theorems_ and fixed
with `partition`, still open on the _definitions_ side. Three of the seven MUSTs are
instances.

This document records only decisions taken on the new evidence. All findings are
`R6-nn` in the merged ledger (`/tmp/r6-SYNTHESIS.md`); the reports are
`/tmp/r6/{A,B,C}.md`.

## Goals / Non-Goals

**Goals**

- Close the gate's last silent escape: a name-based declination that removes a
  definition from the universe with nothing failing.
- Make every completeness claim in the documentation checkable, and correct the three
  that are false.
- Correct one measurably false mathematics sentence.
- Bring `basen`'s pin and its sanctioned-construct count back onto the record.

**Non-Goals**

- No statement weakened; no decoder/encoder behaviour changed.
- No re-timing of any bench lane.
- Not settling R6-15 (`relFunctional` derivability) — see §D6.

## Decisions

### D1 — The def-side audit arm is the change, and it is one `run_cmd`

**Measured.** `publicDefs` filters through `isDerivedDefName`, so a name that matches
the suffix list is removed from the universe _before_ `silent` is computed. Measured
this round, with `Axioms`' own definitions:

```
publicDefs = 141;  Iso.prod in publicDefs: false;  Iso.prod in allowlist: false
Iso.commute in publicDefs: true
```

`Iso.prod` is the paper's `×` and appears in `README [S1]`'s "full unconditional-iso
list". It is public, has no law, and is invisible to a green gate.

**Decision.** Add a def-side arm mirroring the theorem-side `partition`: every name
`isDerivedDefName` drops must appear in an allowlist with a reason, and the pattern
list itself must be justified — an entry matching nothing, or matching authored API,
is a build failure. This is the highest-leverage item because it is the _mechanism_
behind R6-01/02/03 rather than three separate prose fixes, and it is the same shape as
round four's theorem fix.

**Rejected alternative:** delete `"prod"` from the suffix list and leave the rest. That
fixes `Iso.prod` and leaves the next `def` whose last component happens to match a
machinery word equally invisible.

### D2 — `Iso.prod` gets a law, not an allowlist reason

`Iso.prod` is the paper's `×` and is in the anchor's unconditional list. Its `law` is
proved at the definition site (it is a structure-field literal), like `Iso.commute` and
`Iso.associate` — but those two are _mentioned_ by theorems and it is not. The honest
resolution is a theorem naming it, not an allowlist entry: an allowlist reason for the
one member of a list the reader is told is complete would be the "dumping ground" the
allowlist docstring forbids.

### D3 — The three `Prop`-field projections move to the allowlist

`Iso.law`, `Normal.fixed`, `Normalizer.idem` are gated; `MeasureDecreases.dec`,
`MeasureDecreasesR.dec`, `Unfold.dec` are allowlisted as "part of the type a caller
supplies, not a theorem proved about it". Both groups are `Prop`-valued structure-field
projections. Measured: the three gated ones are `fun … => self.1`/`self.2` and report
no axioms.

**Decision.** Move the three into the allowlist group whose reason already covers them.
The file cannot argue in one place that gating a projection "proves nothing" and gate
one in another; the allowlist's reason is the correct description and the counts move.

**Rejected alternative:** delete the two prose passages and keep them gated. That makes
the file consistent but keeps three non-laws inside a count a reader is told is a law
count — the over-claim `R5-10`/`R6-03` are about.

### D4 — The "axiom-free ⇒ restatement" diagnostic is deleted, not repaired

Measured: `decodeWholeOneBytes_eq` is `[propext, Quot.sound]`, not axiom-free, so the
diagnostic fails on one of its own two named examples. It also over-flags
`commitRemainder_spec`/`byteSlice_spec`/`blitBytes_spec`, which are honest identities
_of a definition_ and load-bearing referents for the Layer-2 C contract.

**Decision.** Delete the diagnostic. Name identities by `#print`ing their bodies.
Axiom-freeness is neither necessary nor sufficient, so no repair is available that keeps
the sentence true.

### D5 — `Iso.subset`/`Iso.element` get domain laws

The allowlist's "correctness is the `law` field" is **vacuous** for these two because
they are _partial_: `subset p` is `if p x then some x else none`. For a partial iso the
field holds by construction and what a caller needs is the domain. The file already
treats the folds this way (`Iso.foldl`/`foldr` get their own group and README `[S1]`
strength (ii)), so its taxonomy has three shapes where the library needs four.

**Decision.** State `(subset p).apply x = some x ↔ p x` and
`(element x).unapply b = some () ↔ b = x`, so the mention proxy sees them and a reader
has the domain. If either proves awkward, the fallback is a fourth allowlist group with
the "partial iso: field holds by construction, domain unstated" reason — recorded here
so the decision need not return.

### D6 — R6-15 is recorded as an open question with a proof attempt, not acted on

`README [S3]` says `relFunctional` is "conditional in **every** case" for the six
`_of_decode` laws. The round-six reviewer argued it is _derivable_ for `takeWhile` and
`sepBy` (both are `relRepeat`-shaped over `ConsumesByte` steps, so each value list's
string length is pinned by the list's own length), leaving only `chainl1`/`chainr1` as
genuine obligations — and explicitly flagged the claim as **inferred, not proved**, after
five failed proof attempts.

**Decision.** Do not change the prose on an unproved inference — that is the defect
class this change exists to fix. The task is to _attempt_ the proof: if it closes, the
prose becomes a two-row table (obligation vs derivable) and the theorem lands; if it does
not, the reviewer's inference is refuted and recorded as such in the ledger. **Either
outcome ends in a tick**; this is the same "the result is open, the procedure is fixed"
shape round four used for its `basen` port.

### D7 — The performance figure is re-derived, and the lane is not re-run

`README` derives "~25 ns/step" from `52.4 − 27.4`. `52.4` appears nowhere else in the
document; the adjacent table gives `54.9 − 28.5 = 26.4` (run 1) and `51.1 − 27.5 = 23.6`
(run 2). Three bullets later the same section states the rule that both terms must be
"the same lane in the same run".

**Decision.** Re-derive from the adjacent table and present it as a range with the run
number. Do **not** re-run the bench: this is a documentation inconsistency between
committed figures, and `AGENTS.md` forbids quoting a figure without running its lane
_in the same session_ — which is satisfied here by quoting only the table the reader can
see, not by producing a new number.

### D8 — The `basen` pin is bumped, and the lag class is gated

`basen` pins `codec` at `a12ac65`; the sibling tree is `d86132b` — 10 commits, 7 library
files, +370/−70. Round six _proved the gap is benign_ by rebuilding `basen` against
HEAD in `/tmp` (all 25 jobs green, the 486-theorem gate and the 443-pin prose assertion
included), so this is staleness, not breakage.

**Decision.** Bump and re-run all three `basen` gates, recording actual output. Then
add the prose arm from §D8's spec delta, because the drift was invisible to every check
and nothing in `basen`'s docs named the validated revision at all.

## Risks / Trade-offs

- **[The def-side arm will fire on the current tree]** → expect it to name the dropped
  set first; classifying those is the bulk of §1, and the counts move in lockstep. This
  is by design (the gate catching its own tree), not a regression.
- **[Moving three projections out of the gated set looks like lost coverage]** → it
  loses none: they were never laws. The counts drop and the header says why.
- **[R6-15 may not close]** → then the finding is refuted and the prose stays; recorded
  either way.
- **[`basen`'s `native_decide` count is now 13 and the claim said 3]** → correcting the
  sentence does not reduce the count; §8's tracked item grows. Delete the sentence and
  state the real number, or gate it as §D8 requires.

## Migration Plan

`tasks.md`'s section numbers are authoritative; this is the ordering rationale only.

1. **§1 the gate arm** first — it is the mechanism, and everything else in `Axioms.lean`
   is a classification decision against the list it prints.
2. **§2 the classifications** (`Iso.prod`'s law, the three projections, the dead entries,
   the domain laws for the partial isos) — all in `Axioms.lean` + `Codec/Iso.lean`.
3. **§3 the mathematics sentence** in `Sound.lean` (one witness theorem + prose).
4. **§4 `basen`** — pin, sanctioned-count, pseudo-signatures.
5. **§5–§6 the documentation claims** — README completeness/derivation/signature, then
   the nitpick sweep — after the code, so every corrected sentence points at something
   that now exists.
6. **§7 regenerate** `Axioms.lean` once, at the end.
7. **§8 gates and commit.**

## Open Questions

- **Does R6-15's inference hold?** (§D6.) The task settles it either way.
- **Should the def-side arm's pattern list be derived from the environment instead of a
  string list?** Deriving companion status is possible (an inductive's `recOn`/`casesOn`
  are recoverable from the inductive's info) and would remove the classifier entirely.
  It is more work than this change's scope; recorded as the follow-on if the arm proves
  noisy.
