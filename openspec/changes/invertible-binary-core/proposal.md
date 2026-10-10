# Proposal

## Why

We want a verified, bidirectional codec library in Lean 4 that takes Rendel &
Ostermann's "Invertible Syntax Descriptions" (2010) and makes it *more*
dependently typed, *more* provable, and *binary* — carried to completion. The
paper's central idea is one description, two directions, related by
invertibility; we make that invertibility a mechanical proof (not prose), make it
byte-exact (not "modulo equivalence classes"), and put it on a byte core so it
covers binary, variable-binary, and structured data.

## What Changes

- A **pure-framework core library** `codec`: `Iso` (partial isomorphisms with the
  inverse law as a *field*), `Codec` (the description typeclass), `Rel` (the
  denotational relation), and two interpreters `decode`/`encode`.
- **Byte concrete syntax** (`List UInt8` as the provable core, `ByteArray` as the later executable wrapper), with `byte` and `pure` as the
  only primitive descriptions.
- A **byte-exact roundtrip guarantee** (`decode (encode x) = x`) with no
  "modulo equivalence classes" weakening — achieved by **lossless capture** of
  skippable/optional bytes (no `ignore` primitive).
- **Deterministic decoding** (single result, return-the-remaining-bytes) with
  error reporting carrying a *structural* position.
- Leaf codecs (fixed/variable-width integers, LEB128 varint, text/UTF-8) are
  explicitly **out of scope** — they live in separate repositories.

## Capabilities

### New Capabilities

- `codec`: the verified, byte-exact, bidirectional description framework.

### Modified Capabilities

(There are no existing capabilities; this is a greenfield library.)

## Impact

- New Lean 4 package `codec` (repo `lean-codec`), stdlib-only, no mathlib.
- Downstream consumer packages (`lean-binary`, `lean-text`) will build on it, but
  are separate deliverables with their own proposals.
- No existing code/APIs/dependencies are modified.
