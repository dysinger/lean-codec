# Proposal

## Why

A third hypercritical audit (2026-11-05, three independent read-only reviewers;
full reports in `/tmp/r3-a-codec.md`, `/tmp/r3-b-basen.md`, `/tmp/r3-c-cross.md`)
went over `lean-codec`, `lean-basen` and `lean-nix-flake-template` after
`codec-audit-round-two` closed. Rounds one and two hardened the axiom gate's
**mechanism** and corrected prose; both did what they claimed. What neither did is
enumerate the `def`s and ask, for each one, **where is its law?** — and that
enumeration is where this round's largest findings live.

The pattern behind them is one thing, not nine: **the gate's universe is
theorems.** `Axioms.lean` walks `Environment.constants` keeping only `thmInfo`, so
a `def` with no law is in _neither_ `gatedNames` nor `generatedAuxAllowlist` —
outside the partition entirely, in the one place nobody looks. Round two closed
the "an authored law the classifier silently dropped" hole; this is the same class
of defect one level up. Every finding below is an instance of a `def` standing
outside every gate.

Measured, not read:

1. **Five of the eight `Codec` values README tells a porter to reproduce have no
   theorem — or only a degenerate one.** `grep -c "\`Codec.<name>" Axioms.lean`gives`0`for`seqRight`, `seqLeft`, `between`, `maybe`and`manyUpTo`;
`count`'s only law is `Rel_count_zero`, the `n = 0`case, so the inductive step
is unproved.`between` is the paper's own §6.1 combinator. README:359 lists all
   eight as part of "the bounded eight … a porter must have".
2. **`Codec/Combinators.lean:92-100` claims every derived combinator's `Rel`
   characterization is a definitional consequence and that the full
   `decode_spec`/`bidir`/`roundtrip` laws "hold unconditionally via
   `Codec.Sound`".** That cannot be true of `count n p` at a variable `n`: those
   laws are structural inductions on the `Codec` value, and the `count n p` case
   has no `Rel` characterization to rewrite through. The claim is false for all
   eight, and the missing step is exactly finding 1.
3. **`btake` (`Codec/Codec.lean:112`) is dead public surface** — zero theorems,
   zero callers, a single `grep` hit (its own definition) — while its sibling
   `bdrop` has 19 lemmas. `Suffix.consumed` (`:134`) is the same shape, one size
   smaller.
4. **`sepBy` and `takeWhile` lack the decode→encode half that `chainl1`/`chainr1`
   have.** `encodeChainl1_ne_none` and `encodeChainl1_of_decode` exist;
   `encodeSepBy_of_decode` and `encodeTakeWhile_of_decode` do not. README:343
   describes them as "the same relation-then-two-directions shape every other
   combinator has", which is false for exactly the two triples presented as the
   complete replacement for `many`.
5. **`RelAligned`'s docstring is false, and it is refuted in 30 lines.**
   `Codec/Sound.lean:1119-1129` says "there is no relation that is unambiguous and
   not aligned, and no such witness is worth hunting for". Measured: let
   `S a t := (a = true ∧ m = 1) ∨ (a = false ∧ m = 2)`; then `relUnambiguous S`
   holds (`[propext, Quot.sound]`-only) and `RelAligned S` fails
   (`[propext]`-only). The two predicates are **incomparable**. The paragraph's
   advice — "don't bother proving `RelAligned`, prove `relUnambiguous`" — is
   therefore unsound, since `decodeArray_unique` needs `RelAligned` and
   `relUnambiguous` will not supply it.
6. **`lean-basen` has no mechanism that fails the build on an un-gated theorem.**
   `grep -cE 'run_cmd|Lean\.Elab|Environment|partitionInto|getEnv' Axioms.lean`
   → `0`. 437 theorems and 440 pins agree **today, by maintenance discipline
   only**; one added law and the gate silently shrinks. This is the same hole
   `codec-audit-round-one` found in codec, still open in the dependency's
   consumer.
7. **The template does not enforce zero-`sorry` and its README says it does.**
   `warningAsError` count: template `0`, codec `5`, basen `3`. The template's
   `README.md:50` claims "a build that encounters a `sorry` fails". Every project
   scaffolded from it starts with a non-enforcing proof gate _and_ a false README.
   Its `README.md:134` also tells forkers `@ "main"`; codec's branch is `master`.
8. **`lean-basen/CHANGELOG.md` contradicts itself 33 lines apart**: `:42` says the
   toolchain "upgraded to Lean 4.35.0"; `:75` says "Moving to 4.35.0 was declined".
   Both cannot be true, and the repo's own `AGENTS.md` names exactly this shape as
   a legitimate defect.
9. **`rejects_bad_arity` in the five fixed-width bases is an `n = 1` probe named
   like the general law** that base32/64 actually prove (`n % 8 ≠ 0 → none`), and
   `Base16.rejects_lowercase` proves odd-arity rejection — uppercase `'F'` at
   `n = 1` is also `none` — so the "lowercase" label is carried by nothing.

**One reviewer claim was refuted on inspection and is _not_ part of this change.**
Their F15 said `Axioms.lean`'s footprint table was "197 claimed, 195 in the body";
re-derived from the generated body, the table is exactly `197 / 61 / 4 / 30 = 292`,
matching the header. Their parser truncated at the `?` in
`attach_getElem?_corr` — a tooling artifact they acknowledge in their own F16. The
real residual behind it is that _nothing mechanically re-derives the header_, so a
future drift would be silent; that is task 1.6, not a correction.

## What Changes

Ordered, because the second half's claims are worthless if the first half has not
made the laws exist.

**Part 1 — close the `def`-level hole (findings 1, 2, 3, 4, 6 first).**

- **`lean-basen` gate parity first.** Give `lean-basen`'s `Axioms.lean` the
  mechanism codec has: a `partitionInto`-shaped classifier plus the two `run_cmd`
  checks, so forgetting to gate a law is a build failure rather than a silent
  shrink. This goes first because every later basen law is then safe by
  construction, and because it is the same fix already proven in codec.
- **Laws for the eight bounded `Codec` values.** `seqRight`, `seqLeft`,
  `between`, `maybe`, `manyUpTo` get their `Rel` characterizations; `count` gets
  its inductive step (`Rel (count (n+1) p)`), not only the `n = 0` case.
  `optional`/`choice` gain the missing `Rel` directions.
- **Laws for the two under-covered triples.** `encodeSepBy_of_decode` /
  `encodeSepBy_ne_none` and the `takeWhile` twins, mirroring
  `encodeChainl1_of_decode` / `encodeChainl1_ne_none`.
- **Delete or law `btake` and `Suffix.consumed`.** Dead public surface is a
  porter trap; either give each its one-line law or remove it.
- **Correct `Combinators.lean:92-100`** to the true statement: which families are
  proven, for which values, and that the three "full laws" are structural
  inductions that do **not** close at a variable-`n` `count` without the new step
  law.
- **Add a definition-coverage check to the gate** so a public `def` with no law
  is a build failure, not an invisible omission. This is the structural fix that
  makes findings 1–3 unrepeatable.

**Part 2 — prose and the remaining gaps (findings 5, 7, 8, 9, plus drift).**

- **Refute the `RelAligned` claim with the theorem, not a deletion.** Land
  `relUnambiguous_not_implies_relAligned` (the `S` witness) and replace the
  docstring's ordering claim with the measured one: the predicates are
  incomparable, and `decodeArray_unique` needs `RelAligned` specifically.
- **Template: enforce zero-`sorry` and fix the branch name.** Add
  `warningAsError` to the template's `lakefile.lean` so its `check` gate does what
  its README already claims, and correct `@ "main"` → `@ "master"`.
- **`lean-basen` CHANGELOG** — remove the "declined" sentence that the same
  section contradicts.
- **`rejects_bad_arity` / `rejects_lowercase`** — prove the general arity
  rejection for the five fixed-width bases, and restate the base16 lowercase
  theorem so it is about lowercase rather than arity.
- **Prose drift**: `CHANGELOG.md`'s deleted `Codec.Buffer` entry; README:380's
  `Encode.lean` misattribution; the `[D3]` "leak's growth is in the result list"
  sentence that no measurement supports; the unmarked quote splice at README:222.

## Capabilities

### Modified Capabilities

- `codec/axiom-gate`: the gate's coverage requirement currently makes the gated
  set a partition **of the public theorems**. The audit shows a public `def` with
  no law is outside that universe entirely, so the requirement must extend the
  partition to public _definitions_ — every public `def` is either used by a gated
  law or explicitly recorded as surface-without-a-law.
- `codec/review-remediation`: "A proof ergonomics rule SHALL be recorded where it
  is consulted, once" and "Documentation SHALL distinguish quoted from derived
  claims" are both directly implicated — the `RelAligned` paragraph stated an
  ordering as fact with no theorem, and the `[D3]` sentence presents the README's
  own hypothesis as the paper's. The requirement must cover "an ordering claim
  between two predicates SHALL be a theorem or explicitly marked unproven".
- `basen`: "The conformance laws are gated like the roundtrip laws" currently
  says the new theorems are gated; it does not say the _mechanism_ makes
  forgetting a build failure. It must, matching what codec already requires. The
  arity and base16-lowercase requirements gain the general form.
- `template`: "The skeleton builds and verifies with zero sorry" must state that
  the zero-`sorry` check is **enforced** (`warningAsError`) rather than observed,
  and the dependency-injection requirement must name `master`.

### New Capabilities

- `codec/law-coverage`: every public definition is either exercised by a gated law
  or explicitly recorded as surface-without-one — with the derived-combinator
  inventory as the worked enumeration, so a downstream author is never told a
  combinator has "free theorems" it does not have.

## Impact

- **`Codec/Combinators.lean`**: laws for `seqRight`/`seqLeft`/`between`/`maybe`/
  `manyUpTo`, the `count` step, the `Rel` directions for `optional`/`choice`, and
  the decode→encode halves for `sepBy`/`takeWhile`.
- **`Codec/Codec.lean`**: `btake` / `Suffix.consumed` — law or delete.
- **`Codec/Sound.lean`**: `relUnambiguous_not_implies_relAligned`, and the
  `RelAligned` docstring replaced with what the theorems say.
- **`Axioms.lean`** (+ `scripts/gen-axioms.lean`): the definition-coverage
  check; regenerated counts.
- **`../lean-basen`**: `Axioms.lean` gate mechanism, `Base2/4/8/10/16` general
  arity rejection, `Base16` lowercase theorem, `CHANGELOG.md`.
- **`../lean-nix-flake-template`**: `lakefile.lean` (`warningAsError`),
  `README.md` (`main` → `master`, and the gate claim becomes true).
- **`README.md`** / **`CHANGELOG.md`** (codec): the `[D3]` measurement caveat, the
  `Encode.lean` law attribution, the `Codec.Buffer` removal, the quote splice.
- **No statement is weakened.** Every finding here is satisfied by adding a
  theorem, removing dead surface, or correcting prose to match the code.
