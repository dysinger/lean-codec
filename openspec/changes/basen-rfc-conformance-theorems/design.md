# Design

## Context

See `proposal.md` — Why. The `basen` package proves roundtrip for all seven
bases, but nothing is proved about _rejection_, _canonical form_, or _the
converse_, and the padded decoders actually _accept_ non-terminal padding.
The F* reference (`fstar-basen`) that this package ports from proves a
`decode_*_invalid`/`pad_first`/`bad_length` rejection family per base; the Lean
port dropped it, leaving the "rejects malformed input" spec requirement
unproved and (for padding) unfixed.

## Goals / Non-Goals

**Goals:**

- Three theorem families per base, `[propext, Quot.sound]`-only, zero `sorry`:
  1. **Canonical encoding** (alphabet-only output; terminal-only padding).
  2. **Decode totality** (reject every malformed input class).
  3. **Converse / uniqueness** (`decode xs = some ys → encode ys = xs`; encode
     injective).
- The one decoder fix they expose: base32/64 padded-tail branches require
  `rest = []`.
- Bench-lane vectors closing review findings 5.1, 5.7, 5.10.

**Non-Goals:**

- No substrate/carrier change (`List UInt8` stays).
- No C seam, no `Classical.choice`, no `sorry`, no new axioms.
- No change to base2/4/8/10 _semantics_ (their own spec; just the same
  rejection/canonical _discipline_).

## Decisions

### D1 — Three theorem families, not one "full characterization" mega-lemma

Per base, add:

- `encode_allValid` (or per-base name): `∀ x ∈ encode bs, isValidAlphabet x`
  (base16/2/4/8/10), plus `paddingTerminal`/`paddingArity` for base32/64
  (`∃ k, encode bs = core ++ List.replicate k 61`, with the RFC k by remainder,
  and no `61` in `core`).
- Rejection lemmas (the F* `decode_*_invalid` family restored): one `theorem`
  per class — `decode_alphabet_reject`, `decode_pad_reject`,
  `decode_arity_reject`, `decode_overflow_reject` (base8/10) — each showing
  `decode <bad literal> = none`, plus the stronger quantifed form where the
  precondition is a decidable predicate on the input (`∀ xs, IsBad xs →
decode xs = none`).
- `decode_encode_inverse` (converse): `decode xs = some ys → encode ys = xs`,
  and `encode_injective : encode bs = encode bs' → bs = bs'`.

Rationale: three focused families mirror the F* reference, keep each proof
simple (per the §"proving-over-primitives" lessons), and let the bench lane
value-check each class independently. A single exhaustive "decode valid iff
canonical" iff-theorem is the _eventual_ target but is assembled from these
families, not proved as one induction.

### D2 — The code fix is minimal: a `rest = []` guard in the padded tails

base32/64 `decodeN`/`decode` currently do `match decodeN rest`/`match decode
rest` in the `c2 = 61 && c3 = 61` (base64 1-byte) and `c3 = 61` (base64 2-byte)
branches (and the base32 analog). The fix adds `rest = []` to the _guard_ so
those branches require the pad to be the very end of the input: `if rest = [] &&
c2 = 61 && c3 = 61 then …`. This is the only behavioural change; the encoder
never emits trailing data after `=`, so the roundtrip proofs are unaffected
(a `rw`/`simp` of the new guard is transparent on `encode` output, where `rest`
is itself the recursive `encodeN bs` tail and the pad branch is only entered at
the list end).

### D3 — Rejection proofs are by computation on a finite alphabet (decide/omega)

Because every alphabet is a finite byte set and every rejection class is a
decidable `if`/`match` guard in `decode`, the rejection theorems reduce to
unfolding `decode` and discharging the `if` conditions with `decide`/`omega`
(no `norm_num`/`ring`). The `valToX i ≠ 61` (pad) and `valToX_valid`/`xToVal_
valToX` facts already present are reused. For the _quantified_ forms
(`∀ xs, Bad xs → decode xs = none`), structural induction over the input with
the block-recursion shape handles base32/64 (same `Nat.strongRecOn` pattern used
by the existing `roundtripN`).

### D4 — Converse and injectivity follow from roundtrip + terminal padding

`decode xs = some ys → encode ys = xs`: induction on the decode structure,
`rw [← roundtrip ys]` then use injectivity of `::` and the uniqueness forced by
terminal-pad for base32/64 (the terminal-pad guard makes the decode determinism
visible). `encode_injective` is the companion: `encode bs = encode bs'`, apply
roundtrip to both, so `decode (encode bs) = some bs = some bs'`, hence
`bs = bs'`. The base32/64 padding arity then guarantees the converse lands on
the same block decomposition.

### D5 — Proofs live next to the existing per-base code (no new module)

Each base keeps its own `*ToVal_valTo*`/`valToX_valid`/`valToX_not_pad` helper
style; the three new families are added to the same `BaseN.BaseX` namespace so
the facade (`BaseN`) can dispatch a `Base`-indexed `encode_injective`/
`decode_rejects`/`decode_encode_inverse` by `cases` the same way it dispatches
`roundtrip`. No new module, no new import surface.

### D6 — Bench lane value-checks every new law with concrete vectors

`Bench.lean` gains, per base, an `example`/`#eval` for each rejection class and
the converse, using the F* reference's concrete vectors (base64 invalid `!`,
pad-first, bad-length, `Zg==AAAA` trailing-data) plus base16 lowercase alias and
base8/10 overflow triples. This closes 5.1 (non-terminal padding), 5.7 (smoke
subset), 5.10 (base16 lowercase).

## Risks / Trade-offs

- **[Exhaustive "valid iff canonical" iff-theorem is large]** → target it as the
  _sum_ of the three families (D1), not a single monster induction; each family
  is independently testable.
- **[base32/64 block recursion complicates the quantified rejection forms]** →
  reuse the `Nat.strongRecOn` shape from the existing `roundtripN` (documented
  in the `lean` skill §"Append new learnings here", the strong-induction entry).
- **[The `rest = []` guard risks perturbing roundtrip]** → the encoder emits
  pad only at the list end, so the guard's extra conjunct is provably true in
  every `encode` output; a `change`/`simp` re-establishes the branch.
- **[Overlapping with the existing open review tasks 5.1/5.7/5.10]** → this
  change _implements_ them; the `lean-basen` tasks 5.1/5.7/5.10 are closed here
  (the other 5.x polish items remain open).

## Migration Plan

1. Fix the padded-tail `rest = []` guard in `BaseN/Base32.lean`/`BaseN/Base64.lean`
   (rebuild, re-verify roundtrip + vectors).
2. Add canonical-encoding theorems per base (alphabet + terminal pad).
3. Add rejection theorems per base (restore the F* `decode_*_invalid` family).
4. Add converse + injectivity theorems per base, and the `Base`-dispatched
   facade versions.
5. Extend `Bench.lean` with rejection/canonical/converse vectors; gate with
   `lake build` (zero sorry/warnings), `#print axioms` = `[propext, Quot.sound]`,
   `nix flake check` green.

## Open Questions

None — the RFC rules are pinned in `rfc4648.md`; base2/4/8/10 semantics are this
package's own spec and are intentionally fixed.
