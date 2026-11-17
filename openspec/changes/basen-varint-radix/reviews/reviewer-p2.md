# Reviewer pass 2 — the fixes to pass 1

Run 2026-11-15, same reviewer, against the four artifacts after pass 1's MUSTs were
addressed. This is the pass that matters most in this repo's history, because every prior
round found defects **introduced by the fix for the previous round** — three of five in
round nine, per `AGENTS.md`.

**Verdict as returned: 4 MORE MUSTs.** All inside the change's own files; none touch
`../lean-basen`.

## Closed by pass 1's fixes (verified)

- **V-1 — CLOSED.** The witness arithmetic now checks out; the reviewer re-derived
  `[0x80,0x80,0x01]` independently and confirmed the disagreement at 1 vs 16384.
- **V-4 — CLOSED.** Counts now 5 and 3 as measured.
- **V-5 — CLOSED.** 77 reproduces.
- **V-7 — CLOSED.** One `## MODIFIED` header.
- **V-11 — CLOSED.** Both ADDED requirements under 500 chars.

## New MUSTs (introduced or exposed by the fixes)

### W-1 — MUST — "a function cannot take a `Prop` witness without becoming dependent" is FALSE

design.md D2's cost table justified keeping `digitVal`'s `Nat` signature partly with:

> "**a function cannot take a `Prop` witness without becoming dependent**, which breaks the
> `digitVal_eq` equation lemma"

The reviewer measured it the other way:

```lean
def dv' (r : Nat) (h : IsRadix r) (c : UInt8) : Option Nat := digitVal r c
theorem dv'_eq (r : Nat) (h : IsRadix r) (c : UInt8) : dv' r h c = digitVal r c := rfl
```

> "Measured false. `dv'_eq := rfl` closes at a variable radix … a `Prop` argument is
> proof-irrelevant, so it does not make the function dependently typed in any way that
> breaks `rfl`."

**ACCEPTED.** The claim was mine, unmeasured, and doing argumentative work in the very table
that decides D2. The decision (keep `Nat`) still stands on its other leg — 77 binder
re-elaborations — but the stated reason must go.

### W-2 — MUST — the `MODIFIED` block for requirement 11 DROPPED a live obligation

The live requirement 11 contains:

> "The layer SHALL consist of a digit-value function, a fold from a digit sequence to a
> `Nat`, and **its inverse producing canonical digits**."

The delta's restatement omitted that sentence. A `MODIFIED` block replaces the requirement
wholesale, so **archiving this delta would delete a live `SHALL`** — precisely the hazard
`AGENTS.md` documents and the exact failure mode this change's own D4 warns about, committed
in the block D4 describes.

> "This is the archive hazard, in the change that cites the archive hazard."

**ACCEPTED, and this is the worst of the four.** `openspec validate` did not catch it
(scenario counts matched; a dropped _sentence_ is invisible to it).

### W-3 — MUST — 128 makes the normaliser silently meaningless; "the type is the guard" overstates what is guarded

`ServesDigits 128` cannot be passed where `IsRadix` is required — true. But `trimFor`,
`normF`, `isBlank`, `isZeroDigit` do **not** take `IsRadix`; they take a bare `Nat` radix.
So nothing type-prevents a caller passing 128 and getting a normaliser whose notions of
"blank" and "zero digit" are properties of an ASCII window 128 does not have.

> "only `numeralIso` is type-gated, but 'the type is the guard' is written as if it covers
> the machinery."

**ACCEPTED.** The claim needs scoping to what is actually gated.

### W-5 — MUST — `tasks.md` §8 still calls V-8 an open question, contradicting the design's decision

design.md now says the requirement-7 repair "rides in this change" as a decision; tasks.md
§8 still says "Open question for the owner (not a task)".

> "The two now contradict."

**ACCEPTED.** A fix that landed in one of two files.

## SHOULD / NITPICK (recorded, to fix)

- **W-4** — a scenario clause is vacuous (needs re-reading at fix time).
- **W-6** — design/ledger shape mismatch.
- **W-9** — "the run layer" is **two** layers in `codec` (`takeWhile p` derived run, and
  `relRepeat`/`decodeRepeat`/`encodeRepeat`), and **no `Run`-then-terminator composition
  exists**; tasks 4.2 is aspirational. **This one matters for implementation.**
- **W-10** — the two ADDED requirements disagree on the fold's domain.
- **W-11** — `iff` vs `if` wording.
- **W-12** — the proposal's "Impact" fork is stale against the design's decision.

## Refuted / clean

- **W-7 — REFUTED.** `ServesDigits` with `ofRadix : IsRadix r → …` does **not** make `cases`
  useless and is not a subsingleton problem; the reviewer closed the destructuring in two
  lines. The constructor choice is fine.
- **W-8 — REFUTED.** `c % 128` **is** the low seven bits for all 256 `UInt8` values. No
  defect; the arm is as designed.
- **CLEAN** — nothing in the change contradicts `codec`'s "Runs are derived, not
  constructors". The only issue is W-10's internal fold-domain disagreement.

## Addendum — a process finding about the count

The reviewer reported "4 MUST", listed W-1, W-2, W-3 and W-5, then wrote a narrative table
with the same four. Self-consistent. But it numbered its sections **W-1 … W-12 across four
severities while calling only four MUST**, and two of the "SHOULD" items (W-9, W-10) are
described in prose as things that would mislead an implementer. I am treating W-9 and W-10 as
**blocking in substance** even though the reviewer classified them SHOULD — recorded here
because the severity label is the reviewer's judgement and the prose is the evidence, and
`AGENTS.md`'s rule is that a finding's class is about what you can re-derive, not about the
heading it arrived under.

---

## Disposition — what I did with each, 2026-11-15

| id                       | sev             | disposition                                                                                                                                                                                                                                                                                                                                                                                                                                 |
| ------------------------ | --------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| **W-1**                  | MUST            | **FIXED.** Reproduced the reviewer's counter-example myself (`dv'_eq := rfl` compiles — only an unused-variable lint). D2's cost table now says the `Prop`-witness objection is **falsified**, and the cost is the 77 re-elaborations alone. My claim was unmeasured and was doing argumentative work in the table that decided D2.                                                                                                         |
| **W-2**                  | MUST            | **FIXED.** The live sentence _"The layer SHALL consist of a digit-value function, a fold …, and its inverse producing canonical digits"_ is restored to the `MODIFIED` block, scoped to positional radices. Confirmed by `grep` that it was genuinely absent, so archiving as-written would have deleted a live `SHALL`. **`openspec validate` did not catch it** — scenario counts matched; a dropped _sentence_ is invisible to the tool. |
| **W-3**                  | MUST            | **FIXED.** The "the type is the guard" claim is scoped: it covers `numeralIso` and the positional laws; `trimFor`/`normF`/`isBlank`/`isZeroDigit` take a bare `Nat` and are **not** type-guarded. `tasks.md` 9.1 carries the follow-up.                                                                                                                                                                                                     |
| **W-5**                  | MUST            | **FIXED.** `tasks.md` §8 is now "Decided during review", not an open question.                                                                                                                                                                                                                                                                                                                                                              |
| **W-9**                  | SHOULD→blocking | **RECORDED**, `tasks.md` 9.2: the "run layer" is two layers and **no `Run`-then-terminator composition exists**. Implementation must budget for writing it.                                                                                                                                                                                                                                                                                 |
| **W-10**                 | SHOULD→blocking | **FIXED.** The fold's domain now says **members _followed by_ the terminator**, with a scenario and the measured witness `[0x81,0x01]`=129 vs `[0x81,0x00]`=1 (verified: members-only folding gives 1 for both).                                                                                                                                                                                                                            |
| **W-4, W-6, W-11, W-12** | SHOULD/NITPICK  | W-12 fixed (the proposal's stale Impact fork is now marked superseded by D2). W-4/W-6/W-11 are wording; left for the implementation pass, recorded here.                                                                                                                                                                                                                                                                                    |
| **W-7, W-8**             | REFUTED         | Accepted as refuted. `ServesDigits`' constructor shape and the `c % 128` arm are both fine.                                                                                                                                                                                                                                                                                                                                                 |

### The fix-eats-itself event, this pass

Fixing **W-10** pushed the ADDED requirement back over `openspec`'s 500-character limit —
**regressing V-11, which pass 1 had fixed.** Caught by re-running `--strict` rather than
assuming. Detail moved into a new scenario, `--strict` green again. That is the repo's
standing lesson one more time: _the fix is the most likely source of the next defect_, and
here the fix for W-10 undid the fix for V-11 in the same file.

### Verified after all fixes

```
$ openspec validate basen-varint-radix --strict   ->  valid
scenario counts   req 7: live 5 -> delta 5      req 11: live 3 -> delta 4
call sites        cases hr with 4 | isRadix_le64 6 | IsRadix 77
```
