# Proposal — `codec-audit-round-six`

## Why

A seventh round of read-only adversarial review ran over the three repositories on
2026-11-07 (three workers: A on `lean-codec` mathematics, proof honesty and theorem
coverage; B on `README.md` against `PAPER.md`, anchor by anchor; C on `lean-basen`
conformance and `lean-nix-flake-template`; reports `/tmp/r7/{A,B,C}.md`, merged
ledger `/tmp/r7-SYNTHESIS.md`). It produced **33 findings** and **refuted 10**
suspected ones.

**No finding is a soundness defect.** No law is vacuous, no gate false-passes
today, no `native_decide` appears in any library, and the `basen` pin is a clean
fast-forward ancestor. An exhaustive 502-constant sweep reports **zero**
`Classical.choice` and **zero** `sorry`. The mathematics is sound. Every MUST is a
**claim about the mathematics that is false**.

That is the finding, and it is now the fifth consecutive round whose top result has
the same shape: _a claim about the gate is itself ungated_.

1. **An ungated class, not eleven typos.** Eleven docstring sites across four files
   state an axiom footprint that `#print axioms` contradicts — and they run in
   **both** directions, so this is not a lazy-shortcut bias. Four of them are
   `codec-audit-round-five`'s own additions; one literally reads "**No axioms at
   all** (measured)" and is `[propext]`. The gate asserts theorem-set _counts_ and
   pin _membership_ but has never compared a docstring's stated footprint with the
   `collectAxioms` answer. Round six found the gate's classifier unaudited; round
   seven finds its only prose claim about footprints unaudited.
2. **A payload-side field is also case-sensitive.** RFC 4648 §8 requires a base16
   decoder to accept both cases. `basen` meets that only through an opt-in wrapper
   that has **no roundtrip law**, while every base16 law in the package is stated
   over the lowercase-**rejecting** strict decoder. The RFC-conforming reading is
   real and tested, but no theorem connects it to the encoder.
3. **Three documents describe a mechanism that does not exist.** `basen`'s bench
   `main` is `IO Unit := pure ()`. `default.nix`, its `installPhase`, and the repo's
   `AGENTS.md` all say the lane must be _run_ or it "verifies nothing". The checks
   in fact fire at elaboration, so nothing is unsound — but the operating
   instructions teach future agents the inverse rule for a lane whose `main` is
   `pure ()`.
4. **Two provably dead or stale gate lines.** `basen/Axioms.lean` carries a
   definition-count branch of the form `a - b + b ≠ a`, which is false for every
   input and therefore can never fire; and one prose paragraph states `440 / 437`
   where the tree measures `443 / 440`.
5. **A completeness claim whose arithmetic does not close.** `README [S1]` says an
   environment walk finds "**19** …: the 13 above, plus `foldl`, `foldr`,
   `counterIso` and `counterIsoR`" — 13 + 4 = 17. The total is right and the sum is
   wrong, because two `Iso`-valued witness definitions in `Codec/Sound.lean` are in
   neither the 13 nor the four. This is round five's R6-04 fix, still built from one
   file.

The round also **refuted ten** suspected defects, and those are recorded as
refutations so they are not re-derived. The most consequential: an axiom-free claim
is _not_ predictable from whether the statement mentions `Bytes` (25 axiom-free
theorems manipulate `Bytes` directly), so no syntactic rule can replace measuring.

## What changes

- **One new gate arm**, and it is the change: a declared footprint in a docstring
  SHALL be checked against `collectAxioms` on every build. This is the mechanism
  behind finding 1, so it lands before the eleven edits — otherwise the next round
  finds eleven fresh instances.
- **`basen`'s gate**: delete the dead branch; make the definition-count identity the
  one that can actually fail; fold the `443 / 440` prose figures into the gate;
  close the `nativeDecideCount` parsing holes; give `exclusions` the stale-entry arm
  its sibling allowlist already has.
- **`basen`'s bench lane**: pick one story about `main` and make the three
  documents agree with the code.
- **`Rab` family**: carry the `∃`-form the prose already cites, record the alias, and
  resolve the orphan whose docstring declares its predecessor unnecessary.
- **`README`**: repair `[S1]`'s arithmetic and witness count, the phantom
  `Codec.Sound.uniqSeq_not_congruent`, the reintroduced burst-count caption defect,
  and four dead intra-document links.
- **base16**: connect the RFC-4648 §8 reading to the encoder, or scope the README row
  down to what is proved.
- **`basen` pin and CHANGELOG**: bump or record the 14-commit lag with its reason;
  resolve or drop two SHAs that name no object.
- **Template**: stop describing `basen`'s `bench` package, and scope the
  git-tracked-snapshot claim to the flake path.

## Non-goals

- **No theorem is weakened and no statement is relaxed.** Every change makes a claim
  match what is proved, or adds a proof for a claim already made in prose.
- **No behaviour change** in any decoder or encoder. The seven bases keep their
  semantics; base16's change is a _law_, not a different decoder.
- **Not a performance change.** No bench lane is re-timed. The one performance item
  is a caption defect, corrected by matching the caption to the row's own step
  count.
- **Not a re-audit.** This change acts on the round-seven findings.
- **The 13 `native_decide` bench uses stay.** Converting them still needs a
  `b32TailApply_b32MZTA_chars`-shaped lemma that does not exist (confirmed still
  absent).

## Impact

- Affected specs: `codec/axiom-gate`, `codec/review-remediation`, `basen`,
  `template`.
- Affected code: `Axioms.lean`, `scripts/gen-axioms.lean`, `Codec/Sound.lean`,
  `Codec/Decode.lean`, `Codec/DecodeOne.lean`, `Codec/Combinators.lean`,
  `README.md`; `../lean-basen/{Axioms.lean, Bench.lean, BaseN/Base16.lean, README.md,
AGENTS.md, CHANGELOG.md, default.nix, flake.lock}`;
  `../lean-nix-flake-template/{AGENTS.md, lakefile.lean, README.md}`.
- The new gate arm fires on the current tree until the eleven claims are corrected,
  so the build is expected RED from §1.1 until §1.4 — that is §1 doing its job.

## Evidence base

- `/tmp/r7/A.md` (822 lines) — mathematics, footprint sweeps, predicate matrix.
- `/tmp/r7/B.md` (1192 lines) — every `[D*]`/`[S*]` anchor against `PAPER.md`.
- `/tmp/r7/C.md` (814 lines) — `basen` conformance, gates, template, pin lag.
- `/tmp/r7-SYNTHESIS.md` — the merged ledger this change's `tasks.md` is built from.

**Provenance only.** Every finding a task fixes is stated in full in `tasks.md`, and
the measurements the tasks depend on were re-derived by the main agent, not relayed:
one reviewer figure was **refuted** and corrected before authoring (see `tasks.md`
§9).
