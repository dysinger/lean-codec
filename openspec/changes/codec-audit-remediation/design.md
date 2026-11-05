# Design

## Context

A four-reviewer hypercritical audit (2026-11-05) of `Codec/` produced the findings
this change closes. The audit is the evidence; this document records the decisions
taken on that evidence and the constraints they must respect.

Measured baseline, so the change has a falsifiable starting point:

- **242 of 243** public theorems report `[propext, Quot.sound]`-only.
- **One** does not: `Codec.findByte_spec` →
  `[propext, Classical.choice, Quot.sound]`.
- **0 of 243** are covered by any machine-enforced gate. There is no `Axioms.lean`
  in this repository, and `grep -rn '#print axioms\|#guard_msgs' --include=*.lean .`
  returns only prose.
- All five structural laws (`encode_rel`, `decode_spec`, `bidir`/`roundtrip`,
  `encode_ne_none`, `decodeArray_eq`) are proved for **all seven** constructors.
  No asymmetry. Mutation testing (`decode`'s `Suffix.drop 1` → `2`; `encode`'s
  `single x` → `single (x ^^^ 1)`) breaks the build, so the laws constrain the
  implementation and are not vacuous.

## Goals / Non-Goals

**Goals:**

- Make a `Classical.choice` regression a **build failure**, in this repository.
- Make every axiom-footprint statement in prose match `#print axioms`.
- Remove or correct every docstring that asserts a fact which is not true of the code.
- Close the coverage gaps that cost downstream authors real work.

**Non-Goals:**

- No weakening of any theorem statement to make a gate pass.
- No new formats, no `[S3]` violation: `takeWhile` stays the only derived
  byte-run combinator and no named format enters core.
- Not a performance change. The bench figures corrected here are documentation
  consistency, not re-measurement; no lane is re-run as part of this change.

## Decisions

### D1 — The gate is `Axioms.lean`, a `@[default_target]` lib, mirroring `lean-basen`

`../lean-basen` already ships `Axioms.lean` as a `@[default_target]` lib whose
`#guard_msgs` blocks fail the build on a footprint regression. That shape is proven
in the sibling repo and is the one to copy, for three reasons: it rides on the
library so every consumer inherits it; `#guard_msgs` makes the assertion exact rather
than a scan; and it puts the evidence where a reader already looks.

Rejected alternative: a `grep`-based CI scan for `sorry`/`Classical.choice` in
sources. A `grep` cannot see a footprint — `Classical.choice` enters through a
_cited definition_, not through the text of a theorem. The audit's P0 is precisely a
case a text scan would miss, because `findByte_spec`'s body is `rfl`.

### D2 — `findByte` is reimplemented constructively, not excluded

Two candidate fixes were considered for `findByte_spec`:

- **(A) Exclude it.** State the measured footprint and list it as an exclusion.
- **(B) Make it clean.** Replace the `Array.findIdx?` scan with an explicit
  `Nat`-recursion over the array, so no `Decidable` instance with a classical route
  is consulted.

Take **(B)**. `findByte` is a `memchr`-shaped bulk seam, and `byteSlice_spec` and
`blitBytes_spec` are already axiom-free; leaving one seam law outside the gate
because of an avoidable `findIdx?` is the drift `AGENTS.md` names explicitly. (A) is
the fallback only if (B) turns out to cost an unreasonable proof, and if (A) is taken
the docstring must say _excluded_, never _clean_.

Note the honest limit of (B): `#print axioms` sees the Lean body, not
`Codec/ByteSlice.c`. Making the law witness-clean does **not** make the C proven. The
Layer-2 trust contract stands unchanged, and its prose must keep saying so.

### D3 — `decodeOne`: prove the composition, do not delete the claim

`DecodeOne.lean`'s header promises that the two uniqueness lemmas "together … pin
`decodeArray` to at most one result, and the committed decoder then _equals_ the
unique result". As written that is false: `decodeArray_functional_count` takes
`x₁ = x₂` as a hypothesis and `decodeArray_unambiguous_value` takes `c₁ = c₂`, so each
consumes the other's conclusion and neither is combined.

Take **prove it**. The audit's reviewer closed the `Codec.byte` instance in six lines
(`decodeOne_byte_eq`), and the general form under `Functional d ∧ Unambiguous d` is
the obvious consumer of the two already-proved halves. Where a stated claim is
reachable, the correct action is to make it true, not to delete the sentence. If the
general form proves genuinely hard, the fallback is to state and prove the byte
instance, note the general form as open, and correct the header — but the header
**must not** keep advertising an unproved result.

### D4 — `relUnambiguous_of_relAligned` is written, or the docstring is deleted

`Sound.lean:910` cites it as "proved". It does not exist. Prefer writing it: the
predicates `relFunctional`/`relUnambiguous` exist, `RelAligned` exists, and the
transport is the kind of lemma the `_of_decode` laws already need. If it turns out the
implication is **false** (a real possibility — an aligned relation need not be
unambiguous), then the correct action is the repo's standing preference: prove the
true statement, refute the false one, and fix the docstring to say what is actually
provable. Never leave the citation.

### D5 — `empty`'s `ConsumesByte` witness is added because its absence contradicts a shipped claim

`Sound.lean:126-147` presents `seqConsumesByte`/`isoConsumesByte` as the fix for
"every composed codec proved productivity by hand". `empty` is the one constructor
with no witness, so a downstream `d | empty`-shaped codec still hand-proves at that
node. It is vacuous and costs one line. Add it for uniformity with the claim.

### D6 — `MeasureDecreases` gets a supplier because the repo's own standard demands it

The tree proves `Unambiguous`/`Functional` are satisfiable _precisely because_
nothing had established them for any `d` (`Sound.lean:733-742` states this as the
reason those sections exist). `MeasureDecreases` fails that same test — 19 uses, all
hypotheses, zero suppliers — while being satisfiable in ~20 lines (the audit's
reviewer did so, `[propext, Quot.sound]`). By the repository's own standard it needs
a witness; a two-state counter codec suffices.

### D7 — README corrections are factual edits, not rewrites

Each is a claim the audit falsified against the code. The anchor structure
`[D1]`–`[S6]` is unchanged; several entries already carry "an earlier revision said
X, which was wrong" passages whose _current_ text the audit verified as correct, and
those stay. Specifically:

- `[S3]`: add `takeWhile` to the inventory. It ships, it is `UInt8`-specialised, and
  its docstring names `varint`/UTF-8 as intended uses. Say what core ships.
- `[S4]`: the actual types are `foldl : Iso (α × β) α → Iso (α × List β) α` and
  `foldr : Iso (β × α) α → Iso (α × List β) α`. The README attributes
  `Iso ([α], β) β` to the dual, which is not the code. The thesis survives; the
  premiss must be corrected.
- `packedCands`: two tables give 86/106 and 75/95 for the same lane. One is stale.
  Keep one table, or label each with its run conditions.
- `[D4]` lay-terms paragraph: it reinstates the "unapply cannot choose" diagnosis that
  the `[D4]` block above it explicitly disavows. Correct it to the
  `↔`-quantified-over-every-`a` form.
- `[D7]`: `chainl1` needs four things, not three — `MeasureDecreases` is a separate
  argument from `Iso.foldl`.
- Scope: `lean-binary` is stale; the downstream repo is `lean-basen`.

## Risks / Trade-offs

- **[The gate could be satisfied by an exclusion list that grows]** → the gate lists
  exclusions by name with reasons, and the `review-remediation` delta forbids
  describing an excluded law as clean. Growth is visible in the diff.
- **[Rewriting `findByte` may perturb the C contract]** → it must not. The C symbol
  contract is `memchr`-shaped and unchanged; only the Lean body and its law move.
  Verify the emitted IR still calls the symbol.
- **[`decodeOne` completeness may be harder than the byte case]** → D3 states the
  fallback explicitly: prove what is reachable, correct the header to match, never
  leave an unproved claim advertised.
- **[`relUnambiguous_of_relAligned` may be false]** → D4 states the fallback: refute
  it and fix the docstring. A refutation is a successful outcome.

## Migration Plan

1. `Axioms.lean` gate first, with the _current_ tree including the known exclusion —
   so the gate's first run documents today's true state.
2. Fix `findByte` (D2); re-run the gate; the exclusion disappears from the list.
3. Docstring truths (D3, D4), coverage (D5, D6).
4. README corrections (D7).
5. Gates: `lake build` (zero `sorry`/warnings), the new `Axioms.lean` green,
   `lake build bench`, `nix flake check`, `openspec validate --all`.

## Open Questions

- None blocking planning. D2's fallback (A) and D3/D4's fallbacks are recorded above
  so implementation does not need to return for a decision if a proof turns out
  hard or false.
