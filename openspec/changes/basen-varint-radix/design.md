# Design — `basen-varint-radix`

See `proposal.md` for motivation and the measured facts (`digitVal` is a seven-arm dispatch
chain ending in `else none`; `IsRadix` is a closed inductive with four exhaustive-match
sites and six `isRadix_le64` uses). See `specs/basen/spec.md` for the requirements. This
document covers **how**, and records the two questions the proposal deliberately left open.

## Context

Three facts shape everything here, all measured on `../lean-basen` at `a06998b`.

**1. `digitVal` is alphabet dispatch, not arithmetic.** `BaseN/Radix.lean:90-113` is a
chain `if radix = 2 then … else if radix = 4 then … … else none`. At radix 128 it returns
`none` for **every** byte — `digitVal 128 0x30 = none`, measured. There is no width-generic
path.

**2. `IsRadix` carries two meanings.** It is used for two different claims:

- _alphabet recognition_ — `digitVal`/`byteOfDigit` need to know which byte windows belong
  to which radix;
- _positional structure_ — `digitVal_byteOfDigit` (`Radix.lean:540`) proves an emitter
  round-trips through its own alphabet, `digitVal_some_byteOfDigit` (`RadixCodec.lean:536`)
  proves a readable byte names itself, `digitVal_lt_of_some` (`:214`) proves digit values
  are bounded by the radix, `digitVal_byteOfDigit_zero` (`:943`) proves the zero digit is
  readable.

The second group is **only** true of a fixed-width positional radix. `isRadix_le64`
(`Radix.lean:535`) is the type-level expression of that, and it is used at six sites.

**3. Varint is not a fixed-width numeral.** `codec`'s spec already prescribes its shape
under _"Runs are derived, not constructors"_: _"it is `takeWhile highBitSet` + an `iso`
folding the 7-bit groups — the terminator is the first byte with the high bit clear,
expressed as a run, not a per-byte lookahead."_ A varint's width is determined by its
terminator, so it has no `radix ^ (width-1-i)` weighting and no fixed digit count.

## Goals / Non-Goals

**Goals:**

- Radix 128 usable _for digit recognition_ without perturbing any positional proof.
- The widening provably additive: every existing `IsRadix` consumer compiles unchanged.
- Varint delivered as a **run**, per `codec`'s spec, not as an eighth radix.

**Non-Goals:**

- An open predicate (`2 ≤ r` as a side condition) replacing the inductive. Every existing
  proof would have to be re-stated over a variable radix, which the dispatch chain cannot
  support, and `Radix.lean` would need seven new hypotheses at each site.
- `numeralIso` at 128. See D2 — this is the choice the proposal's Shape A would have made,
  and it is **wrong** for varint.

## Decisions

### D1 — `ServesDigits` is a new closed inductive; `IsRadix` is untouched

**Decision.**

```lean
inductive ServesDigits : Nat → Prop
  | ofRadix : IsRadix r → ServesDigits r
  | b128    : ServesDigits 128
```

`ServesDigits` is what `digitVal`'s **recognition** lemmas take. `IsRadix` keeps seven
constructors and every positional lemma keeps its signature.

**Why an inductive and not a predicate.** A `Prop` with two constructors cannot be
accidentally satisfied by arithmetic: `ServesDigits 7` is unprovable, exactly as
`IsRadix 7` is. A side condition `2 ≤ r` would admit radix 7 and force every proof to
handle a radix with no alphabet.

**Why `ofRadix` as a constructor rather than `IsRadix r → ServesDigits r` as a theorem.**
A constructor makes the implication available to `cases`, so a consumer can go _from_ an
`IsRadix` without naming a lemma at each site; a theorem would need `servesDigits_of_isRadix`
imported at six call sites for no benefit.

**Alternative considered and rejected:** adding `| b128` to `IsRadix` directly. Rejected
because the four exhaustive matches are positional proofs; `b128` would force four arms that
are either vacuous (prove nothing) or false (`isRadix_le64` at 128). A type that says "this
is a positional radix" must not grow a non-positional case.

### D2 — `digitVal` keeps its `Nat` signature; only the _lemmas used by varint_ take `ServesDigits`

**Decision.** `digitVal : Nat → UInt8 → Option Nat` is **unchanged**.

**Why.** Two candidate shapes were weighed:

| shape                                           | cost                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    |
| ----------------------------------------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| change `digitVal` to take `ServesDigits`        | every `IsRadix` binder re-elaborates (measured: **77** occurrences across `BaseN/` + `Axioms.lean` — an earlier draft said 139, which pass 1 (V-5) could not reproduce). **Measured against**: pass 2 (W-1) falsified the further claim that "a `Prop` witness makes the function dependent and breaks `digitVal_eq`" — `def dv' (r) (h : IsRadix r) (c) := digitVal r c` followed by `dv'_eq : dv' r h c = digitVal r c := rfl` **compiles**. Proof irrelevance means a `Prop` argument does not block `rfl`. So the cost is the 77 re-elaborations, and nothing else. |
| leave `digitVal` total, add an eighth chain arm | zero signature churn; the arm is `else if radix = 128 then …`. Proofs that need "this radix has an alphabet" take `ServesDigits`.                                                                                                                                                                                                                                                                                                                                                                                                                                       |

**The second, decisively.** `digitVal` is _already_ total in its radix argument — it returns
`none` for radix 7, for radix 0, for every unserved radix. Radix 128's current `none` is
not a gap in its type; it is a missing **arm**. Adding the arm is one `if`, and the
`ServesDigits` predicate is then only needed by lemmas that must _know_ the radix is served,
which for varint is a small set.

This also means **the proposal's "Impacts" section is wrong as written** — it predicted a
possible signature change and flagged it as the thing most likely to be false. It is
resolved here: no signature changes, so "no existing declaration's statement changes" holds.

**The 128 arm, decided once — pass 1 (V-2/V-3) found three incompatible definitions.**

| artifact said                 | arm                                             | verdict      |
| ----------------------------- | ----------------------------------------------- | ------------ |
| design D2 (as first written)  | `digitVal 128 c = some (c.toNat % 128)` — total | **KEPT**     |
| tasks 3.1 (as first written)  | `if c < 128 then some c else none` — partial    | **REJECTED** |
| spec delta (as first written) | alphabet "`0x00`–`0x7F`"                        | **REJECTED** |

**The `% 128` arm is the decision, and the reason is V-3's: it is the only one that
composes.** Radix 128's "alphabet" is **every byte**, with the value being the low seven
bits. That is not an arbitrary choice — it is what makes `digitVal 128` total, which is what
the varint run needs, because a run's members are precisely the **high-bit-set** bytes
`0x80`–`0xFF`. A `c < 128` arm puts those bytes outside the alphabet, so `digitVal 128` would
reject the continuation bytes the run is made of — the arm and the run would contradict each
other.

**Consequence for the spec (V-3), which must be edited rather than the arm.** The live
requirement's sentence

> "A digit byte that is not in the radix's alphabet SHALL yield `none`"

is **vacuous at 128** under a total arm, and the delta must say so rather than assert it
universally. The repaired sentence scopes the claim: an alphabet may be a **proper window**
(the seven positional radices, which reject) or **total over bytes** (128, whose value is the
low 7 bits); the rejection obligation applies to the former. Stated that way it is true of
both, and the varint requirement's "the run's members are the high-bit-set prefix" is
consistent with it.

**And 128 has no emitter.** `byteOfDigitNat`'s fallback is `48 + d`, so at 128 it emits ASCII,
not a 7-bit group — so `digitVal 128 (byteOfDigit 128 d) = some d` is **unprovable** and
`tasks.md` 3.3 correctly forbids stating it. A total alphabet with no emitter is coherent for
a _run_ (whose "digits" are chosen by the data, not emitted) and incoherent for a positional
radix, which is exactly the distinction `ServesDigits` vs `IsRadix` encodes.

### D3 — Varint is a run with a terminator, and its fold is _not_ `toNat 128`

**Decision.** `BaseN/Varint.lean` defines:

```lean
-- a maximal run of high-bit-set bytes, then one terminator byte
def varintRun  : Run ...                       -- takeWhile highBitSet + the terminator
def varintValue (bs : List UInt8) : Option Nat -- fold the 7-bit groups, LSB first
theorem varint_roundtrip ...
```

and **does not** claim `varintValue = toNat 128`.

**Why not `toNat 128`.** `toNat b ds` is `Σ dᵢ · bⁱ` in most-significant-first order with
the _last_ digit carrying weight `b⁰`. LEB128 is the opposite: least-significant group
first, each group shifted by `7k`, and the terminator is a _byte property_ (high bit clear),
not a position.

**An earlier version of this paragraph named two witnesses that both AGREE, and the
reviewer's pass 1 (V-1) caught it.** Measured, for the 7-bit groups of a byte list:

```
[0x81,0x01]         groups [1,1]     toNat 128 = 129      LEB128 = 129      AGREE
[0x81,0x81,0x01]    groups [1,1,1]   toNat 128 = 16513    LEB128 = 16513    AGREE
[0x80,0x80,0x01]    groups [0,0,1]   toNat 128 = 1        LEB128 = 16384    DIVERGE
[0xFF,0xFF,0xFF,0x7F] groups [127,127,127,127]  = 268435455 both           AGREE
```

So the two folds agree whenever the group list is **palindromic** (including all-equal),
which is why the "obvious" witnesses prove equality. The correct witness, and the one
`tasks.md` 4.6 must use, is **`[0x80,0x80,0x01]`**: LEB128's canonical encoding of 16384
(`16384 = 0b100_0000_0000_0000`, groups LSB-first `0,0,1`), where `toNat 128` over the same
three groups gives **1**. The two functions are not merely "different by a convention" —
`toNat` reads a _fixed-width_ digit string left-to-right and LEB128 reads a _terminated_
run right-to-left, and the divergence shows at the first vector where the leading group is
zero.

**This is the decision the proposal's Shape A got wrong**, and it stands on the corrected
witness: `numeralIso 128` would give a bijection `Nat ↔ canonical base-128 numeral`, and a
varint is _not_ that object — it is a byte string whose **length encodes a continuation
structure**. The honest composition is: varint run → list of 7-bit groups → `Nat`, where
the middle step is a shift-fold, and only the final `Nat` is shared with the numeral layer.

### D4 — The delta uses `MODIFIED`, and edits requirement 11 (and 7) rather than only appending

**Decision.** `specs/basen/spec.md` carries:

- `## MODIFIED Requirements` — requirement 11 (_A numeral denotes a number_), whose
  `2 ≤ b ≤ 64` sentence must become a statement that distinguishes **digit recognition**
  (which now includes 128) from **positional structure** (which remains the seven).
- `## MODIFIED Requirements` — requirement 7 (_Base16 decoding accepts both cases_),
  repaired per the sibling audit `reviews/spec-audit-basen.md` A-1/A-2/A-3/A-4: it currently
  asserts the withdrawn RFC obligation as `SHALL` and cites **five deleted declarations**.
- `## ADDED Requirements` — one new requirement: a terminator-delimited numeral is served
  as a **run**, not as a positional radix.

**Why requirement 7 is in scope.** It is not decoration: it is the requirement
`basen-uppercase-prepass` should have modified and did not, because that change had an
`ADDED`-only delta. Leaving it broken while touching its neighbour is how a spec acquires
two architectures.

**Risk this creates, stated because it is the archive hazard `AGENTS.md` documents.** A
`MODIFIED` block replaces the live requirement wholesale. Requirement 7 has **five
scenarios** today; the delta must restate **all five** (repaired) or they are dropped at
sync. Requirement 11 has **three**, and this paragraph said "four" until pass 1 (V-4)
caught it — the same defect audit A-5 was written to close, recurring in the paragraph that
cites A-5. Counted, not remembered:

```
$ awk 'NR>=409 && NR<476' openspec/specs/basen/spec.md | grep -c '^#### Scenario:'   # req 7
5
$ awk 'NR>=530 && NR<587' openspec/specs/basen/spec.md | grep -c '^#### Scenario:'   # req 11
3
```

Scenario **names** are also identity: `openspec validate` reports "omits scenario(s) the
current spec still has" for a renamed one — measured twice while authoring, on three of
requirement 7's scenarios and one of requirement 11's.

## Risks / Trade-offs

- **A `MODIFIED` block silently dropping scenarios.** → Every `MODIFIED` requirement's
  scenario count is asserted before/after (**5 → 5** for requirement 7, **3 → 4** for 11),
  not eyeballed. This is the failure that has fired twice in this repo's history.

- **`ServesDigits` becoming the dumping ground `IsRadix` was.** → It gets two constructors
  and a stated rule: a radix joins `ServesDigits` only if `digitVal` has an arm for it. It
  is not "any radix we might support".

- **The 128 arm making `digitVal` lie about positional structure.** → `ServesDigits 128`
  carries no `IsRadix` evidence, so it cannot be passed where a **positional proof** is
  needed. **But "the type is the guard" covers only what takes `IsRadix`.** Pass 2 (W-3)
  found the scope error: `trimFor`, `normF`, `isBlank` and `isZeroDigit` take a **bare
  `Nat` radix**, so nothing type-prevents a caller passing 128 and getting a normaliser
  whose notions of "blank" and "zero digit" are properties of an ASCII window that radix 128
  does not have — silently, with no false theorem. The honest statement is that the type
  guards `numeralIso` and the positional laws, and **everything else about radix 128 is
  guarded only by the code never constructing a `ServesDigits 128` in those positions**.
  `tasks.md` 5.5 states the review obligation that follows.

- **Varint's fold drifted from LEB128's actual definition.** → The first thing proved is
  the RFC 4648-adjacent test vector (`[0x81,0x01]` ↔ 129, `[0x80,0x80,0x01]` ↔ 16384), by
  `#eval` **before** any theorem, per this repo's standing rule about evaluating a
  canonical-form construction on boundaries first.

- **The proposal's "Impact" section is stale** (pass 2 W-12): it predicted a possible
  `digitVal` signature change and flagged it as _"the thing this change is most likely to be
  wrong about"_. D2 resolved it — no signature change. The proposal is left verbatim as the
  record of what was believed when the change was opened; **D2 overrides it**, and a reader
  who stops at the proposal will expect a signature change that is not coming.

- **Requirement 7's repair changing observable behaviour.** → It does not: both cases still
  decode. The edit is to the _justification_ and the _citations_, which is why it can ride
  in this change rather than needing its own.

## Migration Plan

Library-only; no deployed surface. Deleted: nothing. Added: `ServesDigits`,
`servesDigits` lemmas, `BaseN/Varint.lean`. `CHANGELOG` states the split so a reader who
learned `IsRadix` as "the seven" is not surprised by a second predicate.

## Open Questions

**None on the design.** The two the proposal left open — the `digitVal` signature and
`numeralIso 128` — are resolved in D2 and D3 respectively, with the alternatives recorded.

**None on siting either, after pass 1 (V-8).** Requirement 7's repair **rides in this
change**, and that is now a decision rather than an open question. The reasoning: this
change already opens a `MODIFIED` block on requirement 7's neighbour, and `AGENTS.md`'s
archive-ordering rule is easiest to keep when one change owns both edits — a third change
touching the same requirement would need its own ordering note. If the owner prefers a
separate change, this delta loses its first `MODIFIED` block and the scenario-count
assertion for requirement 7 with it; what is not acceptable is shipping the question
unresolved while the block is already written.
