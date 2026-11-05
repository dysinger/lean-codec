# Design

## Context

`codec-audit-round-two` acts on the 2026-11-05 second audit (`/tmp/audit-a.md`,
`audit-b-coverage.md`, `audit-c-basen.md`). The previous change,
`codec-audit-remediation`, is archived and its findings are closed. This document
records only the decisions taken on the _new_ evidence, and the constraints they
must respect.

Everything below marked **measured** was re-run in this repository before being
written down; the probes are recorded so they can be re-derived rather than
trusted.

## Goals / Non-Goals

**Goals:**

- Make the axiom gate **sound**: no authored law can be silently un-gated.
- Make every §3.5 obligation in `lean-basen` either **proved** or **honestly
  declared open** — never a correct behaviour guarded only by a false docstring.
- Record which predicate families compose, as proved facts, with the measured
  non-congruences named.
- Bring the three load-bearing README anchors in line with the code.

**Non-Goals:**

- No weakening of any existing theorem statement.
- No new formats in core (`[S3]`), no `many` `Codec` node (`[S6]`).
- Not a performance change; no bench lane is re-timed. `lean-basen`'s new bench
  vectors are _value_ checks, not measurements.
- Not a rewrite of `README.md`; each edit is a claim the audit falsified.

## Decisions

### D1 — The gate becomes a partition, not a filter

**Problem.** `Axioms.lean`'s `isGeneratedAux` decides coverage by matching the
last name component against eight strings. Measured: `Codec.Nat.eq_irrel`
(`Codec/Codec.lean:389`) is an authored theorem with a docstring explaining what
it is for, and it is dropped — `grep -c 'Codec.Nat.eq_irrel' Axioms.lean` is `0`.
Three `Iso.MeasureDecreases*.dec` projections drop the same way. The docstring's
justification, "None is a law a human wrote", is therefore false.

**Decision.** Keep the suffix heuristic as the _default classifier_, but remove
its authority: add `generatedAuxAllowlist : Array Name`, and a build-time check
that for every public `thmInfo` in `Codec`/`Iso`, the name is in **exactly one**
of `gatedNames` or `generatedAuxAllowlist`. A name in neither fails the build with
the name printed. A name in both also fails (that is a contradiction).

This is the same shape as `exclusions`, which already exists for the _gated_ set
and was never consulted for the _dropped_ set — the audit's precise observation.
`Codec.Nat.eq_irrel` moves from dropped to gated, because it is a law.
`Iso.MeasureDecreases.dec` and its two siblings stay allowlisted, with the reason
recorded in place: they are `Prop`-valued **structure fields**, i.e. part of the
type a caller must supply, not theorems proved about it.

**Rejected alternative:** drop the heuristic entirely and gate all 352
`thmInfo`s. That gates `inj`/`injEq`/`sizeOf_spec`/`congr_simp` for every
structure — hundreds of entries that pin nothing a reader cares about, and a gate
nobody reads is a gate that rots. The partition keeps the gate legible while
removing the silent path.

**Honest limit.** The allowlist is still a list a maintainer must maintain. What
changes is that forgetting to maintain it is a **build failure** rather than a
silent hole. That is the strongest property a name-based gate can have, and it
should be stated as such rather than as "sound".

### D2 — base32 §3.5: prove the shapes, do not delete the claim

**Measured.** `Base32.lean:2653-2655` says the 2/3/4/5-byte tails "have none [no
spare bits]". `b32BlockUnapply` (`Base32.lean:215-231`) encodes the 2-byte tail's
fourth character as `(v1 % 2) * 16` — one payload bit, **four** spare. 3-byte:
`(v2 % 16) * 2` — three spare. 4-byte: `(v3 % 4) * 8` — three spare. Behaviour,
measured through `decodeFullB32`:

```
MZTA==== -> some [102,102]            MZTR==== -> none
MZTGM=== -> some [102,102,102]        MZTGN=== -> none
MZTGMZQ= -> some [102,102,102,102]    MZTGMZR= -> none
```

**Decision.** Take the option that makes the prose true. Prove, in the style of
the existing `b64Tail1_pad_bits`/`b64Tail2_pad_bits` family:

- `b32Tail2_pad_bits` / `b32Tail3_pad_bits` / `b32Tail4_pad_bits` — the encoder
  fact (the last character's value is the stated multiple);
- `decodeFullB32_reject_MZTR` / `_MZTGN` / `_MZTGMZR` — the whole-input rejection,
  the three-shape mirror of `decodeFullB32_reject_MZ`;
- and add the three vectors to `Bench.lean`, so the behaviour is also
  value-checked and cannot regress without a failing build.

Then replace the docstring with the true statement. **Do not** merely reword it:
a correct behaviour with no theorem is the defect, and rewording alone leaves it.

**Preferred longer-term form, if cheap:** a general
`b32Tail_canonical_of_rel` (any accepted tail is one the encoder writes) subsumes
all four vectors. Attempt it after the vector forms; if it costs more than the
vectors, keep the vectors and record the general form as the intended upgrade.
Either way the enumeration is a _fallback_, not the goal.

### D3 — `Unambiguous` does not compose under `seq`: record the refutation

**Measured.** With `bIso : Iso UInt8 Bool` (`apply a = if a = 0 then some true
else none`), `bt := iso bIso byte`, `bo := alt bt (pure false)`,
`whole := seq bo (pure ())`:

```lean
#eval! (whole.decodeArray #[0] 0)   -- [((true, ()), 1), ((false, ()), 0)]
```

Two **distinct** values from one 1-byte input, while each half is unambiguous
(`pure ()` is trivially so; `bo`'s two branches consume 0 and 1 bytes
respectively). So `Unambiguous d₁ → Unambiguous d₂ → Unambiguous (seq d₁ d₂)` is
**false**. The root cause is that `seq`'s split point is existentially
quantified: two results may agree on the string and disagree on where it was cut.

**Decision.** Do not prove it, and do not plan it. The audit suggested
`unambiguous_seq` as a "strongest fix"; the measurement refutes it, and the
standing preference is to prove the true statement rather than the convenient one.
What this change does instead:

1. States the composition law that **is** true and that the tree already needs:
   `decodeArray_unique`'s premises (`Functional d ∧ RelAligned (Rel d)`) are the
   pair that closes, and `RelAligned` is exactly the hypothesis that kills the
   counterexample (`false ↦ ""` is not a prefix-extension of `true ↦ "\x00"` in
   a way `RelAligned` tolerates — i.e. `bo` is **not** `RelAligned`).
2. Records the counterexample in `Codec/Sound.lean` beside the
   `Unambiguous`/`Functional` definitions and in `Codec/DecodeOne.lean` beside
   `decodeArray_unique`, so the next reader does not re-derive the naive lemma.
3. Corrects the framing: the `_byte` suppliers make the predicates
   **satisfiable**, not **congruential**, and no composed codec inherits
   uniqueness.

**Consequence to state plainly.** Every uniqueness-gated law
(`encode_of_decode`, `encode_injective_of_unambiguous`, `decodeArray_unique`,
`decodeFull_spec`) is a **leaf-only** law in this tree. That is not a bug to fix
in this change — it is a scope fact the documentation currently obscures, and the
change's job is to stop obscuring it.

### D4 — `MeasureDecreasesR` gets a witness, closing an asymmetry this repo created

Measured: `grep` for any theorem constructing `MeasureDecreasesR` returns
nothing, while `counterMeasureDecreases` supplies the left fold. Every `chainr1`
law is therefore conditional on an uninhabited premise.

**Decision.** Add `counterMeasureDecreasesR : Iso.MeasureDecreasesR counterMeasure
counterIsoR`, mirroring the left witness. Note for the implementer, so a cycle is
not burned rediscovering it: `Iso.inverse counterIso` has type
`Iso Bool (Bool × Unit)`, **not** `Iso (Unit × Bool) Bool`; the needed
construction goes through `Iso.commute` (or an explicit `Iso`). State it whichever
way typechecks most directly and record which.

### D5 — README anchors: three load-bearing corrections, fourteen factual ones

Each was checked against `PAPER.md` and the code by the audit, and the three below
were re-verified here.

- **`[S3]` cites a declaration that does not exist.** `#check @Codec.takeWhile` →
  `Unknown constant`. The triple is `relTakeWhile`/`decodeTakeWhile`/
  `encodeTakeWhile`. Fix the name, and complete the inventory: `count`,
  `manyUpTo`, `optional`, `maybe`, `choice`, `seqRight`, `seqLeft`, `between` are
  `Codec` values in core (`Codec/Combinators.lean`) that `[S3]` does not mention,
  and `[S6]` relies on `optional` without having introduced it.
- **`[D2]` is filed under "Strengthenings (… without changing its meaning)"**
  while its own body says `codec` "exposes the relation rather than only its
  fully-consuming slice". Those are different observable behaviours, and
  `README.md:50-52` defines a strengthening as "no observable-semantics change".
  Refiling it as a departure is the honest fix. Additionally: the paper has
  **two** values — `parse :: Parser α → … → [α]` and
  `data Rel α = Rel [(α, String)]` — so `codec` replaced an `[α]`-interpreter
  rather than extending a `Rel`; the relation to `parse` is a theorem
  (`decode_spec` filtered at `Suffix.empty`), not a definitional identity.
- **`[D3]` is under-scoped in two ways.** (i) Core ships a committed-choice
  decoder, `Codec.decodeOne` (`Codec/DecodeOne.lean:80`), whose `alt` is
  `orElse` — `[D3]`'s claim holds for `Rel`/`decode`/`encode` and must say so.
  (ii) `decode (d₁ | d₂) s = decode d₁ s ++ decode d₂ s` is a **list**
  concatenation, so `decode (d | d) s` returns its result twice while
  `Rel (d | d)` is idempotent `∨`. A porter told the two "agree by construction"
  may model `|` as set union and diverge on multiplicity.

The remaining fourteen (paper micro-quotation in `[D4]`, the `Normal` layer
framing, `[D7]`'s missing terminal-seed obligation, `[D1]`'s unverifiable runtime
claim, the `decodeWhole` signature that is not a type, `[S1]`'s `◦`-for-`≫`,
`[S2]`'s `print → encode`, and the stale `[S1]` iso list) are factual edits with
no design content — they go in `tasks.md` with the audit's citations.

### D6 — Docstring accuracy: "every constructor has a witness" is false for `pure`

`Codec/Sound.lean:138-141` says "every `Codec` constructor now has a
`ConsumesByte` witness", then lists `byte`/`satisfy`/`alt`/`empty`/`seq`/`iso`.
`pure` is a constructor (`Codec/Codec.lean:43`) and is **refuted**
(`not_productive_pure`, `Sound.lean:641`). The list is complete and silently
omits it. Correct to "every _consuming_ constructor; `pure` is refuted by
`not_productive_pure`" — the sentence then becomes true and the omission becomes
information.

The same pass fixes `Codec/DecodeOne.lean`'s presentation of
`decodeArray_functional_count`/`decodeArray_unambiguous_value` as "the hypothesis
that makes the committed `decodeOne` complete": `decodeArray_unique` proves the
composition directly and **does not use** either lemma, whose own docstrings are
therefore advertising a role they do not fill.

## Risks / Trade-offs

- **[The allowlist could become a dumping ground]** → the build fails on a name
  in _neither_ set, and each allowlist entry carries a reason. Growth is visible
  in the diff and provably deliberate, which is the whole point.
- **[Proving three base32 rejections may be more work than estimated]** → the
  `decodeFullB32_reject_MZ` proof structure is already in the file to copy, and
  the pad-bit lemmas are pure `Nat`. If they are not, fall back to the general
  `b32Tail_canonical_of_rel` (D2) rather than weakening the claim.
- **[`RelAligned` may itself not compose under `seq`]** → not assumed. Its `seq`
  status is to be _determined_ (attempt, then record `proved` or `refuted` with a
  witness). If refuted, that is a successful outcome and the documentation says
  so; the predicates are then all leaf-only and the README says that plainly.
- **[`lean-basen` is a separate repo with its own gate]** → base32 work lands
  there, and its `Axioms.lean` gate must be regenerated to cover the new
  theorems. Its `flake.lock` pin needs no update because no consumed statement
  changes.

## Migration Plan

1. Gate partition (§1) first — it is the mechanism every later step leans on.
2. Congruence honesty (§2): the recorded counterexample, and the `RelAligned`
   composition question decided one way or the other.
3. Coverage (§3): `counterMeasureDecreasesR`, the `pure` docstring.
4. `lean-basen` base32 §3.5 (§4), in that repo, with its gate regenerated.
5. README corrections (§5).
6. Gates: `lake build`, `lake build bench`, `openspec validate --all`,
   `nix flake check` here; `lake build`, `lake build bench`, `nix build '.#bench'`
   in `../lean-basen`.

## Open Questions

- None blocking. The two places a fallback is pre-authorized are D2 (general law
  vs vectors) and D3 (the `RelAligned`-at-`seq` outcome), both of which are
  recorded above so implementation does not need to return for a decision.
