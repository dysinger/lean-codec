# Proposal — `codec-audit-round-five`

## Why

A sixth round of read-only adversarial review ran over the three repositories on
2026-11-07 (three workers: A on Lean mathematics, B on `README.md` vs `PAPER.md`
quote-by-quote, C on `lean-basen` conformance and `lean-nix-flake-template`; reports
`/tmp/r6/{A,B,C}.md`, merged ledger `/tmp/r6-SYNTHESIS.md`). It found **38 distinct
defects** in three classes, and **refuted 26** suspected ones.

1. **The gate still has an unaudited escape hatch, and this round found three
   instances of it.** Round four ported `codec`'s theorem partition to definitions and
   closed "a public `def` that no theorem mentions". This round measured that the
   _filter feeding that partition_ has no audit arm: `isDerivedDefName` drops a name
   by suffix string, the name then leaves the universe entirely, and nothing fails. It
   is already dropping **`Iso.prod` — the paper's own `×`**, listed in `README [S1]`'s
   "full unconditional-iso list" — which is public, has no law, and is in neither
   `publicDefs` nor the allowlist. Two sibling findings are the same shape: three
   `Prop`-valued structure-field projections are gated _as laws_ while their three
   twins are allowlisted _as not-laws_, in the same file, which argues both ways in
   its own prose; and two allowlist entries are dead API, the "dumping ground" the
   allowlist's own docstring forbids.
2. **Three completeness claims that a gate cannot see.** `[S1]` says there are
   "exactly two other `Iso`-valued definitions" (there are four, and the stated method
   was `grep '^def'`, which misses multi-line signatures); `[S3]` says "every
   `Codec`-valued definition in the tree is one of these fifteen" (four public
   `uniqSeq*` values are omitted); and `Axioms.lean`'s defs table states that
   axiom-freeness is "the signature of a restatement", which is false for one of the
   two examples it names and over-flags three Layer-2 laws it elsewhere defends.
3. **One mathematics claim, measurably false.** `Sound.lean` says the list-length
   index is what excludes the counterexample, "not `LengthDet`". A `LengthDet`,
   productive relation was proved this round that still admits two distinct
   full-consumption lists of one string at different list lengths, so the sentence
   generalises from one witness's shape rather than from the theorem.

Additionally the audits found a **cross-repo staleness class** the gates cannot see
(`basen`'s pin validating a `codec` 10 commits behind the sibling tree, and three
prose sites quoting that pin from memory), and one **performance arithmetic** defect
of exactly the shape this project has now recorded three times: a ~25 ns/step figure
derived by subtracting figures from two different sessions, in a section that
explicitly forbids that subtraction three bullets later.

The round also **confirmed correct, with evidence**, the things most likely to be got
wrong: `Iso.law` is a genuinely required field; `[D4]`'s round-four repair is real
rather than renamed; base10's fixed-width encoding does roundtrip unconditionally
(the "variable-width trap" does not exist here); the `_char` theorems do not smuggle
their own hypothesis; both bench lanes are load-bearing; and `relRepeat_cons_eq`'s
"neither hypothesis can be dropped" is true. Those are recorded as refutations, not
tasks.

## What changes

- **One new gate arm**: every name `isDerivedDefName` drops must appear in an allowlist
  _with a reason_, mirroring the theorem-side `partition`. This is the single
  highest-leverage item — it closes the root cause behind three MUSTs.
- **`Axioms.lean`**: move the three `Prop`-valued projections into the allowlist group
  whose reason already covers them; delete the false "axiom-free ⇒ restatement"
  diagnostic and name the identities by `#print`-ing their bodies instead; remove the
  three dead allowlist entries; drop the dead and over-reaching suffix-list entries.
- **`Iso.prod` gets a law** or an allowlist reason with a real one (it is the paper's
  `×`, so a law is the honest answer), and `Iso.subset`/`Iso.element` get the **domain
  laws** their allowlist reason currently waves away.
- **Three completeness claims corrected** in `README.md` (`[S1]`, `[S3]`) and
  `Axioms.lean`, each replaced by the count that is actually checkable.
- **The mathematics sentence** in `Sound.lean` rewritten; the counterexample is
  supplied here, so this is prose plus one witness theorem, not a new theory.
- **The performance figure** re-derived from the adjacent table (or given its own row
  and stamp), and the `52.4` orphan removed.
- **`basen`**: bump the pin and re-gate, or record the deliberate lag with its reason;
  correct the "only three `native_decide`" claim; fix two pseudo-signatures.
- **Twelve further one-clause corrections** across `README.md`, `Axioms.lean`,
  `Codec/*.lean`, `basen/README.md`, `basen/Base10.lean`, `basen/default.nix` and the
  template.

## Non-goals

- **No theorem is weakened.** Every statement change makes a claim _match_ what is
  proved, or adds a law that was advertised and missing.
- **No behaviour change** in either repository's decoders or encoders. Both gates were
  green at the start of this round and stay green throughout; the round-six audit found
  no conformance defect in any of the seven bases.
- **Not a performance change.** No bench lane is re-timed. The one performance item is
  a documented arithmetic inconsistency, corrected by re-deriving from figures already
  committed, not by measuring again.
- **Not a re-audit.** This change acts on the round-six findings; it does not go
  looking for new ones.
- **R6-15 is not settled here.** The claim that `relFunctional` is derivable for
  `takeWhile`/`sepBy` was flagged by its reviewer as _inferred, not proved_. It is
  recorded as an open question with the proof attempt as its task, and the prose is not
  changed until the proof lands — see design §D6.

## Impact

- Affected specs: `codec/axiom-gate`, `codec/review-remediation`, `basen`.
- Affected code: `Axioms.lean`, `scripts/gen-axioms.lean`, `Codec/Iso.lean`,
  `Codec/Sound.lean`, `README.md`, `AGENTS.md`;
  `../lean-basen/{flake.lock, Bench.lean, README.md, BaseN/Base10.lean, default.nix}`;
  `../lean-nix-flake-template/{AGENTS.md, lakefile.lean}`.
- Every new gate arm fires on the current tree until the tree is fixed, so the counts
  in `Axioms.lean` move in lockstep — see `tasks.md` §7.

## Evidence base

- `/tmp/r6/A.md` (676 lines) — mathematics, proof honesty, gate internals.
- `/tmp/r6/B.md` (523 lines) — every `[D*]`/`[S*]` anchor against `PAPER.md` and code.
- `/tmp/r6/C.md` (391 lines) — `basen` conformance, template, cross-repo seams.
- `/tmp/r6-SYNTHESIS.md` — the merged ledger this change's `tasks.md` is built from.

**Provenance only.** Every finding a task fixes is stated in full in `tasks.md`; no
`/tmp` path is a dependency, and the Appendix carries the two proof bodies this change
needs.
