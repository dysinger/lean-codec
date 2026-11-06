# Proposal — `codec-audit-round-four`

## Why

A fifth round of read-only adversarial review ran over three repositories on
2026-11-06 (three workers, `/tmp/r5-a-vacuity.md`, `/tmp/r5-b-departures.md`,
`/tmp/r5-c-cross.md`; synthesis in `/tmp/r5-SYNTHESIS.md`). It found **37 distinct
defects**, in three classes:

1. **One mathematical claim that is false.** `LengthDet → RelAligned` is recorded in
   four places as "open — neither proved nor refuted". It is **refuted**, by two
   witnesses that were already in the tree when the claim was written. Reproduced
   `[propext]`-only by the main agent, twice, independently.
2. **A family of over-stated uniqueness/necessity claims.** Nine docstrings say some
   variant of "this is the only X", "the full list", "none has a caller" or "sound
   only when", and each is false or mis-scoped. This is the same defect class that
   rounds two and three each retired a batch of; it survives because these instances
   are about _why a choice was made_, not about whether a theorem holds, so no gate
   can see them.
3. **Two gate asymmetries and one stale pin across the ecosystem.** `basen` never
   received codec's definition-coverage check (and has eight provably dead public
   `def`s as a result), and its `codec` pin is **27 commits stale** — so its 484-theorem
   gate has been validating an older dependency's proof surface.

Additionally the audit **confirmed correct**, with evidence, the things this repo is
most likely to get wrong: the four core laws, basen's format correctness on every
RFC 4648 vector, and the C discipline. Those are recorded as passes, not tasks.

## What changes

- **One new theorem family** in `Codec/Sound.lean`: `LengthDet` is _incomparable_ with
  both `relUnambiguous` and `RelAligned`, with witnesses for every non-implication.
  Three existing claims become theorems; four prose sites become accurate.
- **Two laws that were advertised but absent**, both proofs supplied here:
  `decodeWholeBytes` at the caller's own index (`decodeWholeBytes_spec`) and the
  general `decodeRepeat_mem_iff_general`.
- **`huniq_not_derivable` restated in the form its prose cites it for** (an `∃ R` over
  a relation that is unambiguous _and_ productive).
- **Nine necessity/uniqueness docstrings corrected** in `Codec/`, each to state what
  is proved and why the over-claim was wrong.
- **`README.md` anchors corrected**: `[D4]`'s title (the substantive one — the anchor
  claims a losslessness it does not implement for the paper's only use case), `[S1]`'s
  "full list", `[S3]`'s "no caller" and its inventory table, `[S2]`'s `print` reason,
  plus eight nitpicks.
- **`basen`**: port the definition-coverage check, resolve the eight dead `*Run`
  values (law or delete), restate the stale prose counts, and **bump the pin**.
- **`basen`'s bench lane**: pin the encoder values it currently only implies.
- **Two Axioms improvements**: the def-counts table's wording, and extending
  `headerNumbers` to guard the prose paragraph it currently cannot see.

## Non-goals

- **No theorem is weakened.** Every change to a statement makes it _stronger_ or makes
  it match what was already claimed.
- **No behaviour change** in `codec`'s decoders or encoders. The two new laws are
  additive; `decodeWholeBytes_spec` is a statement about an existing wire path.
- **Not a performance change.** No bench lane is re-timed. The README's throughput
  figures were explicitly **not** re-measured by the audit and are not touched here.
- **Not a re-audit.** This change acts on the round-five findings; it does not go
  looking for new ones.
- **`[D4]`'s missing length-changing carrier is not built.** The anchor is corrected to
  say the whitespace case is _not_ reproduced, because building a
  `Bytes m → Bytes n` normalizer is a design change, not a prose fix, and would need
  its own change.

## Impact

- Affected specs: `codec/law-coverage`, `codec/review-remediation`, `codec/axiom-gate`,
  `basen`.
- Affected code: `Codec/Sound.lean`, `Codec/Combinators.lean`, `Codec/Packed.lean`,
  `Codec/Codec.lean`, `Codec/DecodeOne.lean`, `Codec/Iso.lean`, `Codec/Normal.lean`,
  `Axioms.lean`, `README.md`, `AGENTS.md`, `scripts/gen-axioms.lean`;
  `../lean-basen/{Axioms.lean, Bench.lean, BaseN/Base16.lean, flake.lock}`.
- Every new law is gated: the def-coverage check and `headerNumbers` both fire, so the
  counts in `Axioms.lean` must move in lockstep (§7.6).

## Evidence base

- `/tmp/r5-a-vacuity.md` (910 lines) — vacuity, over-selling, core-law soundness.
- `/tmp/r5-b-departures.md` (1658 lines) — every `[S*]`/`[D*]` anchor vs `PAPER.md`.
- `/tmp/r5-c-cross.md` (521 lines) — `basen` correctness, cross-repo consistency,
  ecosystem rules.
- `/tmp/r5-SYNTHESIS.md` — the merged, severity-ranked ledger.
- Main-agent verification probes: `/tmp/verify/*.lean` (M1 refutation, S2 fix, S3 fix,
  B-3 general form).

**Every MUST and SHOULD item was independently re-derived by the main agent.** Items
recorded as _predicted but not run_ are marked as such in `tasks.md` — there is one
("basen still builds on codec HEAD").
