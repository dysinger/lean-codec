# Proposal

## Why

An independent reviewer audited the verified core (`.lake`-clean, zero `sorry`,
zero warnings, axioms `[propext, Quot.sound]`-only) and found **no soundness bugs**,
**no purity leaks**, and **complete theorem/doc coverage**. What it did surface is a
small set of _polish_ items: one remaining ~300-line near-duplicate proof block
(after the `unfoldBy` refactor already removed the same pattern from `foldl`/`foldr`),
one under-specified `@[extern]` trust seam, one representation that understates a
provable invariant, and two minor clarity/naming nits. This change applies that
feedback so the library reflects its own "invertibility by construction" ethos at the
proof-organization level too — without changing any denotation, law, or public
signature.

## What Changes

- **Deduplicate the full-consumption decoder stack** in `Codec/DecodeByteArray.lean`:
  transfer it through the already-proved `decodeByteArrayRel_eq` bridge into the
  `DecodeArray` natives instead of re-deriving ~300 lines of `WellFounded.fix` /
  `Step` / `_some` / `_ne_none` / `_spec` machinery a second time.
- **Tighten the `@[extern]` `byteSlice` trust seam** (`Codec/ExternFastPath.lean`/`.c`):
  make the scalar/bignum-index domain explicit and documented in the Lean side (not
  just a C comment), so the pinned `_eq` law and the C symbol cannot silently diverge.
- **Make varint uniqueness structural**: change `decodeVarint` from `List (Nat × Nat)`
  to `Option (Nat × Nat)` (dropping the redundant `j`), so "at most one result" is a
  type fact rather than a prose claim; adjust `decodeVarint_eq`/`roundtripVarint` to
  `Option` equations.
- **Naming/doc cleanup**: align `byte_consumesByte`'s framing with the `ConsumesByte`
  convention; rewrite `encodeBuffer_eq` to close without a fragile `eq_comm`.
- **Docs**: fold the trust-seam domain caveat into the Lean docstrings (README already
  carries the complete `[D1]`–`[D8]`/`[S1]`–`[S6]` table — no README change needed).

## Capabilities

### New Capabilities

(none)

### Modified Capabilities

(none — this is a pure refactor/tightening with no spec-level behavior change)

## Impact

- Affects `Codec/DecodeByteArray.lean` (removal of duplicated machinery), `Codec/VarBinary.lean`
  (`decodeVarint` return type and its proof statements), `Codec/ExternFastPath.lean`/`.c`
  (trust-seam documentation), `Codec/Buffer.lean` (`encodeBuffer_eq` proof restructure),
  `Codec/Decode.lean` (naming).
- **No public `Codec`/`Rel`/`decode`/`encode` denotation changes**; every law keeps its
  exact statement (or an `Option`-projection provably equal to it). Axiom record stays
  `[propext, Quot.sound]`-only.
- `decodeVarint`'s signature change is internal (only `VarBinary.lean` references it);
  `Bench.lean`/downstream are unaffected because the varint benches already project the
  single result.
