# Reviewer pass 1 — the change itself

Run 2026-11-15 by a read-only reviewer subagent against the four artifacts of
`basen-varint-radix`, with `../lean-basen` as ground truth. Findings as returned;
my triage and the fixes are in `../../basen-varint-radix/tasks.md` §9 and in the
artifacts themselves.

**Verdict as returned: NOT ready to implement as written.** The structural thesis
survived (R-1); three load-bearing statements did not (V-1, V-2/V-3, V-4).

---

## Critical

### V-1 — MUST — design.md D3's arithmetic argument is self-contradictory; the "divergence" it names does not exist

The reviewer computed both folds:

```
[0x81,0x01]        toNat128([1,1])     = 129     varint = 129     equal
[0x81,0x81,0x01]   toNat128([1,1,1])  = 16513   varint = 16513   equal
[0x80,0x80,0x01]   toNat128([0,0,1])   = 1       varint = 16384   DIVERGE
```

> "design.md's chosen witnesses are **both non-witnesses**, and the reason it gives is
> the wrong reason… a proof attempt that follows it will reach for `[0x81,0x81,0x01]` and
> prove agreement."

**ACCEPTED — this is the finding that matters most.** It would have produced a theorem
claimed to distinguish the folds whose concrete witness actually proves them equal.

### V-2 — MUST — the 128 arm has three incompatible definitions

| artifact       | arm                                                           |
| -------------- | ------------------------------------------------------------- |
| `design.md` D2 | `digitVal 128 c = some (c.toNat % 128)` — total, never `none` |
| `tasks.md` 3.1 | `if c < 128 then some c else none` — partial                  |
| spec delta     | alphabet is "raw 7-bit groups `0x00`–`0x7F`" — partial        |

> "D2's own justification for excluding 128 from `IsRadix` depends on the `% 128` version
> … which is false of the version tasks.md 3.1 actually specifies."

**ACCEPTED.** Three files, three functions.

### V-3 — MUST — under either arm the delta's restated rejection sentence is vacuous or contradicted

> "under D2's prose arm the alphabet is all 256 bytes and the sentence's antecedent is
> empty at 128 (vacuous); under tasks.md 3.1's arm it is satisfiable but the 'alphabet'
> then excludes the very continuation bytes the varint mechanism relies on… Only the
> `% 128` arm makes the composition coherent, and only the `% 128` arm makes the restated
> rejection sentence vacuous."

**ACCEPTED**, and it resolves V-2 in a direction I had not seen: the `% 128` arm is the
one that composes, which means the _spec sentence_ must be scoped, not the arm changed.

### V-4 — MUST — requirement 11 has three scenarios, not four

```
$ sed -n '530,586p' openspec/specs/basen/spec.md | grep -c '^#### Scenario:'
3
```

> "design.md D4 states 'Requirement 11 has **four** scenarios' and tasks.md 5.3 says
> 'keeps all three scenario names and gains exactly one' — the two task/design files
> disagree with each other and the design agrees with neither the live spec nor tasks.md.
> … This is precisely the class AGENTS.md calls out, recurring in the very change that
> cites it."

**ACCEPTED, and the sharpest of the four in one respect:** I cited audit A-5 ("a number
nobody re-derives") in D4 and then asserted an un-derived count two paragraphs later. I had
the number in front of me — I ran `grep -nE '^#### Scenario:'` on requirement 11 earlier in
this session and got **3**, then wrote **4**.

---

## Warnings

### V-5 — SHOULD — "139 `IsRadix` use sites" is 77

`grep -o 'IsRadix' -r BaseN/ Axioms.lean | wc -l` → 77 (RadixCodec 37, Radix 22,
RadixTie 15, Axioms 3).

> "139 is unreproducible from any reasonable reading … it is doing argumentative work
> ('139 vs zero'), and it is roughly 1.8× the truth."

**ACCEPTED.** Delete the number; the qualitative point ("a signature change re-elaborates
every binder") stands without it.

### V-6 — SHOULD — tasks 3.1's "the equation lemma stops matching" is true, but it is a compile error, not silent drift

`digitVal_eq` ends `:= rfl`. Adding an arm to `digitVal` without mirroring it in
`digitVal_eq` makes that `rfl` **fail to typecheck**.

> "which is strictly better news than the task implies."

**ACCEPTED.** The risk is smaller than I wrote it.

### V-7 — SHOULD — the delta declares `## MODIFIED Requirements` twice

```
3:## MODIFIED Requirements
75:## MODIFIED Requirements
151:## ADDED Requirements
```

Valid today, but a Markdown shape the tool tolerates rather than expects.

**ACCEPTED.** Merge.

### V-8 — SHOULD — the change is doing two unrelated jobs (varint + repairing req 7)

> "Leaving the sequencing unresolved ('Open question for the owner') while the delta
> already ships the block is the worst of both — either decide, or drop it from this delta."

**ACCEPTED in substance, but I am keeping the block** and now state it as a decision rather
than an open question: requirement 7's repair rides here because this change already opens a
`MODIFIED` block and the archive-ordering hazard argues against a third change touching the
same requirement. The owner can still split it; what is not acceptable is shipping the
question.

---

## Suggestions

- **V-9** — `byteOfDigitNat`'s fallback is `48 + d` at radix 128, so 128 has **no emitter**;
  the spec's "raw 7-bit groups" phrasing is aspirational. **ACCEPTED** — says so now.
- **V-10** — `[0x80,0x80,0x01]` is LEB128's canonical 16384 and is the one vector where the
  conventions differ maximally; it is 4.6's natural witness. **ACCEPTED**.
- **V-11** — the ADDED requirement trips the >500-char warning. **ACCEPTED** — split.

## Refuted

- **R-1** — "`ServesDigits` perturbs the four exhaustive-match sites." **Refuted.** `IsRadix`
  is unchanged; a `ServesDigits` witness cannot be passed where `IsRadix` is required.
- **R-2** — "the five deleted declarations still exist." **Refuted** — 0 hits each. Audit
  A-2 confirmed.
- **R-3** — "the delta cites declarations that do not exist." **Refuted** — 31 backticked
  ids, 0 missing.
- **R-4** — "tasks 3.4's counts 4 and 6 are wrong." **Refuted** — both exact.

## Could not confirm

1. That the four exclusive-match sites and 20 `digitVal_eq` sites still compile after an
   eighth arm (read-only audit; no build). **`digitVal_byteOfDigit_zero` is the site to
   compile first.**
2. Whether `openspec archive` accepts a duplicate `## MODIFIED` header at sync time.
3. The baseline gate figures (`698 = 646 + 52`) — not re-run.
4. Other dangling citations in the live spec — but audit R-2 already swept all 100.
