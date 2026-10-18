# Spec Delta

## Purpose

The shipped-C fast surface: `@[extern]` `memcpy`/`memchr`/varint/numeric-parse/zlib
seams plus per-format specialized decoders/encoders, each either proved
`[propext, Quot.sound]`-equal to the unchanged `Bytes n` spec or named as a
runtime-only trust contract.

## ADDED Requirements

### Requirement: A Layer-2 seam has a reducible Lean body and a named trusted C symbol

Every shipped fast primitive SHALL be `@[extern]`-shaped with an **elaborating Lean
body** that reduces under `simp`/`rfl`, so `#print axioms` on any law built over it
reports `[propext, Quot.sound]`-only (or none) regardless of the C. The C symbol it
binds to SHALL be a named, isolated trust seam whose contract is documented in the
module header, and SHALL be **excluded** from the `#print axioms` gate. A seam SHALL
NOT be a proven law; the only proof obligation is that the _Lean body_ equals the
`Bytes n` spec via a refinement lemma, never that the _C_ does.

#### Scenario: The axiom gate never sees the C

- **WHEN** a law is proved over a seam's Lean body (e.g. `blitBytes`'s
  `ByteArray.mk (data.extract …)` body)
- **THEN** `#print axioms` on that law reports `[propext, Quot.sound]`-only with
  no seam-related axiom, and the running C is trusted via a prose contract, never
  folded into a theorem.

#### Scenario: A wrong seam fails at run time, not only the contract

- **WHEN** a seam is exercised by a bench lane
- **THEN** the lane value-checks the seam's output byte-for-byte against the Lean
  body (or the spec), and a semantically wrong C symbol throws, so the trust
  contract is re-checked empirically.

### Requirement: Bulk copy and scan are single `memcpy`/`memchr` primitives

The fast surface SHALL expose `blitBytes` (buffer-to-buffer `memcpy`) and `findByte`
(span scan via `memchr`), each `USize`-indexed so its Lean-body refinement is
definitional (no `Nat ↔ USize` roundtrip, no `System.Platform.numBits` premise). A
length-delimited or fixed-size byte region SHALL be materializable by exactly one
`memcpy`, and a delimiter/byte search SHALL be one `memchr` over raw contiguous
bytes, never a per-byte Lean fold.

#### Scenario: A protobuf length-delimited body is one copy

- **WHEN** a decoder reads a length prefix and commits the following body
- **THEN** the body is produced by one `blitBytes`/`memcpy` over the source span
  (not a per-byte loop), and the value is checked byte-for-byte against the spec.

### Requirement: Varint and numbers parse/write through C spans

LEB128 varint encode/decode SHALL be available as an into-buffer span operation
over `lean_sarray_cptr`, and JSON/TOML numeric literals SHALL parse via a numeric
primitive wrapping `strtod`/`strtoll`. Each SHALL have a reducible Lean body equal
to the existing `VarBinary`/spec behavior, so the refinement law stays
`[propext, Quot.sound]`-only.

#### Scenario: A varint round-trips through the fast span

- **WHEN** a varint is encoded into a buffer span and decoded back from it
- **THEN** the result equals the `VarBinary` spec value, and the span op avoids
  per-byte bignum cursor arithmetic.

### Requirement: Per-format decoders/encoders are proved equal to the spec

A specialized decoder/encoder for a format (WAV, protobuf, JSON, PNG, QR) SHALL be
proved `[propext, Quot.sound]`-equal to the generic `Bytes n` spec by a
`decodeArray_eq`-style refinement lemma, with `@[extern]` seams reserved for the
raw-byte and compression regions. The generic spec interpreter SHALL remain the
single denotation; specialization SHALL NOT weaken or narrow the spec.

#### Scenario: A WAV decode is header parse plus one copy

- **WHEN** a specialized WAV decoder runs
- **THEN** it parses the fixed-size header structurally and produces the PCM sample
  block by one `memcpy` over the source span, and a refinement lemma proves it
  equal to the generic decode of the same description.

### Requirement: Deterministic choice is permitted only under Unambiguous/Functional

A shipped decoder SHALL be permitted to commit a `|` choice to a single result only
when the description is proven `Unambiguous`/`Functional` (as defined in `Sound.lean`);
the unconditional backtracking law for the general `decode` SHALL be unchanged. A
committed-choice path SHALL NOT be presented as equal to the backtracking spec
without that hypothesis.

#### Scenario: An unambiguous format commits without branching

- **WHEN** a decoder for an unambiguous format (e.g. protobuf, fixed-field WAV)
  commits a choice
- **THEN** the result is shown equal to the (single) backtracking result under the
  `Unambiguous`/`Functional` hypothesis, and no alternative result is silently
  discarded for a non-unambiguous description.

## Scope

**In scope**: the `@[extern]` seams (`blitBytes`, `findByte`, varint span,
numeric parse, zlib), their reducible Lean bodies, the per-format specialized
decoders/encoders and their refinement lemmas, and the `Unambiguous`-gated
deterministic path.

**Out of scope**: making the generic pure `Bytes n` interpreter itself fast
(accepted as the slow spec); a new GC-less compiler backend; proving the trusted C
symbols correct (they are runtime contracts, excluded from the axiom gate).
