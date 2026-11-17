# Audit — `basen` live spec, after two archive syncs in one day

**Audited 2026-11-15**, immediately after `basen-radix` and `basen-uppercase-prepass` were
synced and archived. `openspec/specs/basen/spec.md`, 16 requirements, 858 lines.

**Why this audit exists.** Two changes appended three requirements each to the same
capability within one day, and the second one's central finding was that an obligation the
first one's text assumed (case-insensitivity "required" by RFC 4648 §8) **does not exist**.
`openspec validate --all` reported 12/12 passing at every step: it compares structure, not
consistency between requirements. So the risk was a document that says two contradictory
things, with no check that could see it.

**Headline verdict: the risk was real, and worse than predicted.** Requirement 7 is a live
normative requirement that (a) asserts the withdrawn RFC obligation as binding, and (b)
cites **five declarations that no longer exist** in the package. It was synced before the
change and never revisited, so the spec now describes a deleted implementation as
mandatory.

---

## Summary counts

| severity                                              | count | ids         |
| ----------------------------------------------------- | ----- | ----------- |
| MUST                                                  | 5     | A-1 … A-5   |
| SHOULD                                                | 6     | A-6 … A-11  |
| NITPICK                                               | 4     | A-12 … A-15 |
| Refuted                                               | 1     | R-1         |
| Raised as unverified, then **resolved by running it** | 1     | R-2         |

---

## MUST

### A-1 — Requirement 7 asserts the withdrawn RFC obligation as binding, in direct contradiction with requirement 16

**Location.** `openspec/specs/basen/spec.md:409-418` (requirement 7) against `:804-830`
(requirement 16).

Requirement 7, first sentence, unchanged since it was authored before `basen-radix`:

> "The Base16 decoder SHALL accept hex digits in **either** case, **as RFC 4648 §8
> requires**, and SHALL return the same value for a block and its case-folded form."

Requirement 16, added by `basen-uppercase-prepass` this session:

> "A conformance claim SHALL NOT rest on an unsourced paraphrase: the package's
> documentation of an external standard SHALL be traceable to the standard's text."

and its scenario:

> "**THEN** it cites RFC 4648 §8's own wording — that base 16 encoding **does not require**
> case insensitivity and that decoders **may** accept lowercase — and describes lowercase
> acceptance as an optional convenience rather than a requirement it is obliged to meet."

The RFC text, verified in `codec`'s `README` and `lean-notes.md` (corrected in
`codec-audit-round-eight` M-1):

> "Base 16 encoding does not require case insensitivity; however, Base 16 decoders **MAY**
> accept lowercase letters."

**Two live requirements now state opposite things about the same obligation, and one of
them is normative `SHALL` resting on a `MAY`.** A reader implementing from the spec cannot
tell whether rejecting `6f` is a conformance failure (requirement 7) or conformant
(requirement 16).

**Verdict: MUST.** This is not a wording preference — requirement 7's `SHALL` is the exact
obligation the change deleted 29 pins to refute.

**Fix.** Rewrite requirement 7's opening to state the permission, drop "as RFC 4648 §8
requires", and make explicit that the strict decoder is conformant without the fold. Keep
the acceptance as a **should-offer** convenience, or state it as the package's own choice
rather than a conformance duty. Requirement 7's later paragraphs ("The conforming decoder
SHALL carry the roundtrip law…", the per-decoder ownership rule) are **sound and should be
kept verbatim** — they are what makes the tolerant decoder a decoder rather than a folding
function.

---

### A-2 — Requirement 7 cites five declarations that do not exist

**Location.** `openspec/specs/basen/spec.md:433-472`, requirement 7's four scenarios.

Measured against `../lean-basen/BaseN/*.lean` today:

```
  MISSING decodeHexBlockFold_case_insensitive
  MISSING foldByte_idem
  MISSING foldList_idem
  MISSING foldList_hexBlockUnapply
  MISSING decodeHexFold_both_cases
  MISSING foldByteBytes          (and foldByte / foldList / foldNormalizer / hexBlockIsoF)
```

The scenarios that cite them:

| scenario                              | cites                                                              | status            |
| ------------------------------------- | ------------------------------------------------------------------ | ----------------- |
| _Both cases decode to the same value_ | `decodeHexBlockFold_case_insensitive`, `foldList`, `foldByteBytes` | all three deleted |
| _The encoder emits a normal form_     | `foldList_hexBlockUnapply`                                         | deleted           |
| _The fold is upward, and idempotent_  | `foldByte_idem`, `foldList_idem`                                   | both deleted      |

**The archived `basen-uppercase-prepass` deleted these and added replacements, but never
touched requirement 7** — because its delta was purely `ADDED`, so the sync appended
requirements 14–16 and left 7 alone. That is the archive hazard this repo documents for
`MODIFIED` blocks; here it fired through a different door: **a change that should have
modified an existing requirement didn't, because it had no `MODIFIED` section at all.**

**Verdict: MUST.** A normative requirement whose every proof obligation names a deleted
theorem is not a requirement about the shipped package.

**Fix.** Rewrite the three scenarios against what exists:

| should cite                         | instead of                            |
| ----------------------------------- | ------------------------------------- |
| `decodeHexFold_lowercase_eq`        | `decodeHexBlockFold_case_insensitive` |
| `upperBytes_of_encodeHex`           | `foldList_hexBlockUnapply`            |
| `upperByte_idem`, `upperBytes_idem` | `foldByte_idem`, `foldList_idem`      |
| `upperBytes`                        | `foldByteBytes` / `foldList`          |

**And the generalisation, which is the durable finding:** the `findings` check that would
have caught this is that **a spec must not name a declaration the package does not
export**. Nothing checks it. `grep` did, in one command.

---

### A-3 — Requirement 7's "Both cases decode to the same value" scenario states a theorem shape that no longer exists

**Location.** `openspec/specs/basen/spec.md:437-441`.

> "**THEN** both produce the same value: `decodeHexFold s = decodeHexFold (foldList s)` for
> one block (`decodeHexBlockFold_case_insensitive`) and `decodeHexFold s = decodeFull hexRun
(foldByteBytes s)` at whole-input level."

The second equation was `rfl` only because `decodeHexFold` _was_ `decodeFull hexRun ∘
foldByteBytes`. It is now `decodeFull hexRun ∘ upperBytes`, so the stated equation is
**false as written** — `foldByteBytes` does not exist, and substituting `upperBytes` makes
the right-hand side `decodeFull hexRun (upperBytes s)`, which equals `decodeHexFold s` by
`rfl` but is not the equation the sentence claims (it claims `decodeHexFold s = strict
(fold s)`, and the current definition makes that the _definition_, not a law).

**Verdict: MUST**, folded into A-2's fix. Restate as the equality that carries content —
`decodeHexFold_lowercase_eq`, which relates _two inputs_, not an input to its own
definition.

---

### A-4 — The spec has no requirement that lowercase acceptance is _optional_, only that its citation be honest

**Location.** `openspec/specs/basen/spec.md:804-830`.

Requirement 16 constrains **how the package documents** the obligation ("cites the
specification's own wording", "describes lowercase acceptance as an optional
convenience"). It never states the substantive fact as a requirement, so a reader of the
requirement list alone learns a rule about citation and not the fact being cited.

Combined with A-1 (requirement 7 asserting the obligation), the spec's position is: the
package must accept both cases (7), and must not claim §8 requires it (16) — which is
coherent only if 7's `SHALL` is re-read as the package's own choice.

**Verdict: MUST** because the fix for A-1 depends on it: A-1 cannot be repaired by deleting
"as RFC 4648 §8 requires" while leaving a bare `SHALL accept either case`, because that
re-asserts the obligation unsourced, which requirement 16 forbids. The two requirements
must be edited **together** so the operative sentence carries both facts: _the strict
decoder is conformant without case tolerance; the package offers tolerance anyway, as its
own choice._

**Fix.** Either (a) fold the substantive statement into requirement 7's rewrite and leave
16 as the citation rule, or (b) add one sentence to 16 stating the permission outright.
(a) is preferred — it puts the fact where a reader looks for behaviour.

---

### A-5 — `openspec validate --all` cannot see any of this, and the session treated it as if it could

**Location.** Every sync this session ended with "`openspec validate --all`: 12/12" as the
verification statement.

That figure is true and is **not evidence that the spec is consistent**. `validate` checks
per-requirement structure (headers, scenario hashtag count, description length); it does
not compare requirements to each other, does not read cited identifiers, and cannot see
that requirement 7 contradicts requirement 16 or names five deleted theorems. A-1 through
A-4 all landed under a green `validate`, twice.

**Verdict: MUST**, as a process finding rather than a spec edit. This repo's `AGENTS.md`
already says _"an arm that reports no count cannot be told from an arm that reads nothing"_
and _"a check is only as good as what enters it"_. `openspec validate` is that shape: it
reports a count (13 passed) that says nothing about the property being relied on.

**Fix.** Stop citing `validate` as the verification of a spec sync. The checks that
actually verify a sync are the ones already used ad hoc in this session — requirement
counts before/after, prefix-unchanged, scenario-completeness per requirement — **plus the
two this audit had to add**: cross-requirement contradiction, and cited-identifier
existence. Record those as the sync recipe.

---

## SHOULD

### A-6 — Requirement 7's title still says "(RFC 4648 §8)"

**Location.** `:409`. The title `### Requirement: Base16 decoding accepts both cases (RFC
4648 §8)` attributes the behaviour to the RFC. Under the corrected reading it is the
package's choice. Rename to drop the parenthetical, or to `(a package choice, not an RFC
requirement)`.

### A-7 — Requirement 14 says a base "SHALL NOT gain a bespoke case-folding tier", which reads as a rule about future code rather than observable behaviour

**Location.** `:752-756`.

> "A base SHALL NOT gain a bespoke case-folding tier of its own where the core already
> supplies the general mechanism…"

**Observed behaviour cannot distinguish "a bespoke tier" from "a tier"**, so this is a rule
about how to write the code, not a behaviour contract — the shape `AGENTS.md` says to
delete or make assertable. The assertable version is already present in the same
requirement ("a decoder of the form `decodeNormal normalizer strictIso` requires only the
normaliser's idempotence proof and the encoder-emits-a-normal-form obligation"). Prefer the
effect; drop or subordinate the prohibition.

### A-8 — Requirement 16's own title generalises beyond case folding, but every scenario is about Base16

**Location.** `:804-830`. Title: _"A stated conformance obligation cites the specification's
own wording"_. Scenarios: both about `MUST`-vs-`MAY` and Base16. That is fine as far as it
goes, but the requirement now binds _every_ external-specification claim in the package
(RFC 4648 §4/§6/§10 vectors, §3.5 pad bits), and none of those citations has ever been
checked against its text. State the requirement's scope as system-wide, or narrow the title
to Base16.

### A-9 — Requirement 13's "measured, the bases split two ways" table is a measurement without a command

**Location.** `:643-740` (the block-iso tie requirement). It states:

> "base 2's eight bits, base 4's four quartets and base 16's two nibbles each reach exactly
> `255` … Base 8's three octal digits reach `511` and base 10's three decimal digits reach
> `999`"

All true, and all arithmetic a reader can redo (4^2−1, 8^3−1, …), so this is borderline.
But the requirement also asserts the exhaustively-verified iff ("over all 512 octal digit
triples", "all 1000 decimal ones") without naming the theorem that carries it —
`octBlockApply_domain_iff` / `digBlockApply_domain_iff` exist and should be cited by name,
as the rest of the spec cites its laws.

### A-10 — Requirement 11's empty-sequence paragraph now duplicates `toNat_nil`'s docstring almost verbatim

**Location.** `:530-560` vs `BaseN/Radix.lean:150-160`. Two copies of one claim, and this
repo has paid five times for duplicated statements that can drift. Either cite the docstring
or state the requirement and let the docstring point at it.

### A-11 — The spec is 858 lines across 16 requirements with no table of contents and no grouping

Requirements 1–10 are the RFC 4648 bases; 11–13 are the numeral layer; 14–16 are pre-passes.
Nothing separates them. A reader arriving to answer "is lowercase required?" has to find
requirement 7 _and_ 16 to get a consistent answer, and there is no index. Not a correctness
defect; a real cost, and the direct cause of A-1 being missed (nobody re-read 7 when 16
landed).

---

## NITPICK

### A-12 — `:441` has an unbalanced parenthesis in a scenario

`"…(`decodeHexBlockFold_case_insensitive`) and\n  `decodeHexFold s = …"` — the line break
falls inside a parenthetical, which renders oddly and suggests the text was hand-edited
around a deleted name.

### A-13 — Requirement 15's title says "where case is not data"; the body's operative test is alphabet membership

Nowhere in the requirement does "data" get defined; the body says "containing no lowercase
symbols". The title is prose, the body is checkable. Minor, but the checkable one is the
requirement.

### A-14 — `:752` "…where the core already supplies the general mechanism" is ambiguous about _which_ core

`codec`'s `Normal`/`Normalizer`. Elsewhere the spec says "the core package". Consistency.

### A-15 — The two most recent requirements use "SHALL" three and four times per sentence-group, where one per requirement would do

Requirement 14 has `SHALL supply`, `SHALL run`, `SHALL NOT be folded`, `SHALL NOT be
relaxed`, `SHALL NOT gain` in ~10 lines. Normative density is not normative clarity.

---

## Refuted / could not confirm

### R-1 — Refuted: "requirement 12's quotient statement conflicts with `basen-radix`'s `[S7]`"

Hypothesis formed from requirement 12 saying "the inverse law holds **unconditionally on
the quotient**" while requirement 16 mentions `[S7]` in `README.md`. Checked: requirement
12 states the `[S7]` strengthening correctly and in the same terms `README.md`'s `[S7]` uses
(a canonical representative, not an `Eq` parameter). **No conflict.**

### R-2 — **RESOLVED after the audit, and the answer was good.** Whether requirements 1–10 (and 11–13) have dangling citations

I initially left this unverified, reasoning that ~40 more names were too many to check by hand. It is one command, so I ran it rather than leave the gap — extracting **every backticked identifier in the whole spec (100 of them)** and testing each as a word against `BaseN/*.lean` plus `Codec/Normal.lean`:

```
backticked identifiers: 100
not found: 6
  _char                          -- a NAME SUFFIX, not an identifier (`decodeFull_B16_char`)
  decodeHexBlockFold_case_insensitive   -- genuinely deleted
  foldByte_idem                         -- genuinely deleted
  foldList_hexBlockUnapply              -- genuinely deleted
  foldList_idem                         -- genuinely deleted
  reject_first_invalid                  -- a NAME SUFFIX (`decodeFullB32_reject_first_invalid`)
```

**So the damage is confined to requirement 7, exactly as A-2 said, and nothing else in the
spec cites a missing declaration.** Four real hits out of 100 — all in one requirement.

Two transferable facts. (a) **The gap I was willing to leave unverified was closed in one
command and 30 seconds**; "roughly 40 more names" was an estimate of effort, not a
measurement, and it was wrong by an order of magnitude. That is the same padded-estimate
shape this repo records elsewhere. (b) **A naive identifier-existence grep produces false
positives from name _suffixes_** (`_char`, `reject_first_invalid`), so the check needs the
"is it a fragment?" filter or it will report noise — two of six hits were noise here.

**This makes A-5's proposed check concrete and cheap enough to be mandatory:** the
identifier sweep over the spec is ~20 lines of Python and it found every real defect.

---

## What this audit changes about the `basen-varint-radix` plan

The proposal being written alongside this audit inherits two constraints it did not know:

1. **Its delta MUST use `MODIFIED`, not just `ADDED`.** `basen-uppercase-prepass` proves
   that an `ADDED`-only change cannot repair an existing requirement, and requirement 7 is
   broken precisely that way. `basen-varint-radix`'s stated intent is to narrow requirement
   11's scope ("serves these radices") — that is a `MODIFIED` block or it will not happen.
2. **A-5's check belongs in it.** If the change adds `ServesDigits` and a varint run, the
   spec will cite new names, and nothing verifies they exist. Either the proposal carries a
   "cite only what is exported" obligation, or the next audit repeats this one.

And one constraint it can _relieve_: if requirement 11 is rewritten to distinguish digit
recognition from positional structure, that is the same split A-2's fix needs — so the two
edits should be authored together rather than sequentially.
