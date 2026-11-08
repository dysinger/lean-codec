# Design — `codec-gate-denominators`

## Context

This change is not driven by a defect. It is driven by **fourteen consecutive
occurrences of one defect class**, in which each was fixed individually and the class
survived because nothing enforced a shape on a new arm.

The class: _a check whose input has a filter that nothing audits._

The repo's own spec already generalizes one half of it —
`A gate name-list asserts the property it exists to represent`. But that requirement is
scoped to **lists**, and only about half the fourteen instances were lists. So the
change is a **generalization**, not a new idea: the same obligation, stated for every
arm rather than for name lists.

## D0 — Why this is the correct fix and the other two options are not

Three options were on the table.

**Option 1 — implement the open fixes.** Closes the fourteen instances (already closed)
and the round-nine/round-ten findings. Leaves the generator untouched, so instance
fifteen is found the same way: by a reviewer, eventually.

**Option 2 — this change.** State the precondition. Does not fix anything, because
nothing needs fixing; changes what a _new_ arm must look like.

**Option 3 — stop reviewing.** Settles nothing.

**Dependency, which is why 2 comes first:** option 1's fixes are themselves arms and
prose corrections. Landing them _before_ the precondition means the precondition is
written after the code it should govern, and the round that installs the rule then has to
retrofit fourteen sites. Landing it first means each fix in option 1 is authored against
the rule, and can be mutation-tested as it lands.

**The correct answer to "which of the three" is therefore 2, then 1, then stop** — and
"stop" is then a consequence rather than a judgement call, because after 2 the remaining
findings are all of a shape the build now rejects.

## D1 — The rule, stated precisely

For every diagnostic arm, two numbers:

- **denominator** — the universe the arm's claim is about, and
- **removals** — what it took out of that universe, decomposed by cause.

Both asserted. A printed-only number is allowed but must be _labelled_ printed-only
wherever the gate enumerates its own numbers.

Why "decomposed by cause" and not just "removals": instance 14 was `skipped = 8`, which
was not a missing denominator — the denominator was present (`146 + 8 = 154`). What was
missing was the _split_: two of the eight were a survey paragraph and two were claims
with no resolvable owner. One total could not distinguish them, so the arm looked
healthy while excluding the two claims that carry `decodeFull_spec`'s hypothesis chain.

Why "asserted" and not just "printed": `AGENTS.md:37` presented five footprint numbers as
though all were asserted; `expectedFootprintCounts` asserts three. A printed number rots
silently. That is instance 9.

## D2 — Why the rule is worded without naming the current arms

The delta deliberately does **not** say "three arms violate this". It states the
obligation. Task 1 identifies the violations and fixes them; if the implementation
discovers a fourth, the requirement already covers it. A requirement that enumerates its
own violations is a to-do list wearing a spec's clothes, and this repo has already hit
the archive hazard three times by writing deltas against the tree instead of against the
behaviour.

## D3 — `isBareProj` hoists to one definition (and what that implies)

`Axioms.lean:1915` and `:1988` are two separate `let rec` literals five lines apart,
under a comment asserting "one definition … so they cannot drift apart". `run_cmd`
blocks cannot share a `let rec`, so the fix is a top-level
`def` in the `CodecAxioms` namespace, called by both.

**This is a precondition for the round-ten finding, not a cosmetic move.** Round ten
measured that a flat head-constant set would capture `Codec.roundtrip`,
`Codec.findFrom_finds`, `Iso.apply_eq_some_of_unapply` and
`Iso.unapply_eq_some_of_apply` — four genuine laws, including `roundtrip`. The predicate
that must replace it has to distinguish "unwraps a caller-supplied hypothesis" from
"unwraps a proved theorem", which means inspecting _what the head constant is applied
to_ and recursing. Getting that right in two independently-maintained copies is how the
two directions end up disagreeing.

**Deliberately not decided here:** the exact predicate. That is task 3, and its acceptance
criterion is measurable and stated there — `Codec.roundtrip` must stay gated, the three
true Prop-selectors must move, and `CandAligned_tail` must stay gated because it is a
real proof. Any predicate that cannot meet all three is wrong, and the tasks say so.

## D4 — What "correct, not brute force" means for this change

The temptation is to make the rule a giant arm that greps `Axioms.lean` for `logInfo` and
demands a denominator in a comment. That is a brute-force check: it would pass on a
comment and fail on a correctly-written arm that prints its counts in a different shape.

The correct form is: **each arm asserts its own numbers**, using the machinery the file
already has (`expectedFootprintCounts`, the `headerNumbers` pattern, `throwError`).
There is no new framework. The rule is a convention plus three small additions to existing
arms, and its enforcement is that each arm already knows its own denominator.

The one genuinely new mechanism is the **per-pattern count**, because
`derivedDefPatterns` currently has no way to say how many declarations one pattern
removed. That needs a `List (Name × Nat)` built by the same walk that already computes
`dropped`, and an asserted tuple — the pattern `expectedFootprintCounts` establishes.

## D5 — Archive ordering

`codec/axiom-gate` is modified by **three** open changes: `codec-audit-round-nine`
(authored, unfixed), `codec-gate-denominators` (this one), and the round-ten findings if
they are authored. All three touch overlapping requirements.

**Required order: this change first**, because it states the obligation the other two's
fixes are then authored against. Re-run `openspec validate --all` after **each** archive,
and compare the live scenario count against the delta's before syncing — the hazard this
repo has hit three times. Measured at authoring time: `+10 / -0` across four
requirements.

## D6 — Scope boundary

Not in this change:

- Any fix for the round-nine or round-ten findings. A `benchBurst` guard, a `77 ns/step`
  cell, an RFC misquote and a `relRepeat` paragraph are all _instances_, and this change
  is about the class.
- Any `Codec` declaration. This change touches gate machinery, `AGENTS.md`, and the
  spec.

## D7 — The spike: the predicate is solved, and it corrected three of my tasks

A worker spiked task §3 against the real environment before any implementation. Full
report at `/tmp/spike-isBareProj.md` (**not durable — the result is transcribed here and
in tasks §2b so it survives a reboot**).

**Result: implementable, with no name list.** The predicate is three parts:

1. peel `lam`/`mdata`;
2. decompose the outermost application spine;
3. accept a bare `.proj`, **or** a constant whose own body peels to a bare `Expr.proj`
   (a _projection constant_) applied, at its **first explicit declared argument**, to
   something recursively a projection of a bound/free variable.

**Why it separates a hypothesis from a theorem — the thing D3 could not state.** Measured:
every genuine projection in this library has a `proj` body (`Iso.law`, `And.left`,
`Subtype.property`, `Codec.Normal.fixed` all peel to `proj#0`), while every proved theorem
that merely has an `↔`/`∧` **result type** does not (`Codec.bidir`'s body is a `let`;
`Option.ne_none_iff_exists'` is `Iff.trans`). So the discriminator is **the head constant's
own body**, not its name and not the arity.

Independently re-run against the five acceptance criteria before being written down:

```
Codec.roundtrip              false   <- the one that matters
Codec.findFrom_finds         false
Codec.CandAligned_fst        true
Codec.CandAligned_at         true
Codec.CandAligned_tail       false   <- a real proof; stays gated
Codec.fill_fixed             false
Codec.packedCands_mem        true
Iso.apply_eq_some_of_unapply true
Iso.unapply_eq_some_of_apply true
```

Exactly **five** new captures, all genuine; nothing already allowlisted moves.

**Three tasks I had written were wrong, corrected in place:**

| task | what I had written                                        | measured                                                                                                                                   |
| ---- | --------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------ |
| 3.3  | offer "`And.left`/`And.right` at their declared arity"    | `And.right` is reached at arity **8** and **3**; "declared arity" is a category mismatch, not a mechanism                                  |
| 2.1  | hoist "with the body of the existing predicate unchanged" | the hoist and the fix are **one edit**; splitting them edits the same line twice                                                           |
| 3.5  | `fill_fixed` "has **zero** consumers"                     | `Bench.lean:103` calls it. It still stays gated, but for the _principled_ reason: its operand is a **constructed** value, not a hypothesis |

**A trap worth carrying forward:** `args.getLast?` produces **byte-identical output** to
the correct `firstExplicitIdx` accessor on today's tree. It passes every test and is
wrong — `CandAligned_at`'s operand is `args[2]` while `args[7]` is a different bound
variable. This is the `isDerivedDefName` shape (a rule that agrees by luck) and is now a
docstring requirement (task 2b.3).

## D8 — What the spike did NOT prove, and the first thing the next session must do

The spike proves **task §3** (the predicate). It does **not** touch **task §1**, which is
where the _denominator_ half of the rule actually lives:

- 1.1/1.2 — the per-pattern decomposition of the def classifier, and
- 1.3/1.4 — splitting the footprint arm's `skipped = 8` by cause.

Those are unspiked. They are also the simpler half: both are "accumulate a
`List (Name × Nat)` alongside an existing walk and assert the tuple", the pattern
`expectedFootprintCounts` already establishes. The risk there is not _whether_ it works
but whether the asserted counts are stable — i.e. whether the walk is deterministic. A
spike is not required, but **the first implementation step is to print the decomposition
before asserting it**, so the numbers are observed rather than guessed.

**Stated plainly for the next session: the predicate is solved; the decomposition is not
built.** Start at task 1.1, not task 2.
