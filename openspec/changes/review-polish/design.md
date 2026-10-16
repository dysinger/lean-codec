# Design

## Context

The verified core is complete and `.lake`-clean. A reviewer found no soundness or
purity issues, full theorem/doc coverage, and a README already carrying the complete
departure/strengthening table. Four concrete polish items remain (plus one minor
naming nit). The `unfoldBy` refactor already established the pattern for how this
project eliminates near-duplicate well-founded proof machinery: factor a generic core
with a single `_spec`/`_eq` law, and instantiate thin wrappers that preserve public
signatures.

## Goals / Non-Goals

**Goals:**

1. Remove the ~300-line near-verbatim duplication between `DecodeByteArray.lean`'s
   native full-consumption stack and `DecodeArray.lean`'s, transferring through the
   already-proved `decodeByteArrayRel_eq` bridge — mirroring the `unfoldBy` move.
2. Make the `@[extern]` `byteSlice` trust seam's scalar-index domain explicit on the
   Lean side so the pinned `_eq` law and the C cannot silently diverge on the bignum
   edge.
3. Make varint uniqueness structural (`Option` instead of `List`).
4. Clean the two minor clarity nits (`encodeBuffer_eq` `eq_comm`, `byte_consumesByte`).

**Non-Goals:**

- No change to any denotation, law statement, or public `Codec`/`Rel`/`decode`/`encode`
  signature. No new axiom. No README rewrite (already complete). No new capabilities.

## Decisions

**1. Transfer `DecodeByteArray` through the bridge, don't re-derive.**

`decodeByteArrayRel_eq : decodeByteArrayRel d a i = decodeArrayRel d a.data i` is
already definitional-level. So `decodeFullByteArray p h a i` is provably
`(decodeFullArray p h a.data i)` (up to the unit `ByteArray.mk`/`.data` round-trip),
and its `_spec` transfers by one `rw` from `decodeFullArray_spec`. Delete the
`decodeFullByteArrayStep`/`_lt`/`_some`/`_ne_none`/`decodeFullByteArray_some`/`_ne_none`
locals and re-express `decodeFullByteArray` and its laws as compositions. This is the
same lower-risk move that `decodeByteArray_eq`/`decodeByteArrayRel_eq` already make for
the non-full-consumption layer (the handoff documents that an earlier compositional
draft was replaced by natives _for the read path_; that reasoning is preserved for
`decodeByteArrayRel`, while the _full-consumption result-folding_ path is
result-list-construction-bound and gains nothing from a second native recursion — see
the handoff's own "the O(1)-index carrier win is on single/multi-byte reads, not the
list-building path" note). Where a native is genuinely hot (`decodeByteArrayRel`), keep
it; where it is pure result folding (`decodeFullByteArray`), transfer.

**2. Trust seam: document + restrict the domain, do not rewrite the C.**

The two `@[extern]`s are thin shims over the stdlib's own `@[extern]`s (established
last session: no speedup, mechanism only). The bignum-index case is _accidentally_
sound (any bignum exceeds any real array size, so both sides yield `[]`), but relying
on that is fragile. Fix by (a) documenting the scalar/`USize`-representable domain on
the Lean `byteSlice`/`encodeAppend` docstrings and the `_eq` laws, and (b) noting the
planned `USize`-indexed entry point (`slice-returning-run-model`) as the structural fix.
No C change is warranted for a mechanism-only seam.

**3. `decodeVarint : … → Option (Nat × Nat)`, dropping the redundant `j`.**

The varint's single result and `j = i + length` are already proved. Return
`Option Nat` (the value), with `decodeVarint_eq`/`roundtripVarint` stated as `Option`
equations that project through the existing `List`-membership lemmas. Consumers that
need the consumed length derive it by `varintBytes n .length`.

**4. Minor nits.**

- `encodeBuffer_eq`: state the `∃` side symmetrically (`Buffer.ofBytes l = b`) so it
  closes by `simp` without `eq_comm`.
- `byte_consumesByte`: keep the name (snake_case theorems match sibling `byteRepeat`'s
  camelCase `def` role), but tighten the docstring to say it is "the `ConsumesByte
Codec.byte` witness", resolving the framing ambiguity the review flagged.

## Risks / Trade-offs

- **Transferring `decodeFullByteArray`** risks a regression in the _native read_
  guarantee if the compositional form re-materializes `.toList`. Mitigation: the
  transfer goes through `decodeArrayRel_eq` (not `a.toList`), which is the same
  reducible `Array` the natives already use; and the full consumption layer is
  result-list-bound in _both_ forms, so no perf cliff. The `decodeByteArrayRel` native
  (the actual hot read) is **not** touched.
- **`decodeVarint` signature change** is a breaking change to `VarBinary.lean`'s
  internal API. Impact is confined to that module (verified: no other file imports
  `decodeVarint`); the `_eq`/`roundtrip` laws are re-stated as `Option` equations so
  downstream can still reason.
- **Trust-seam doc-only change** is deliberately not a rewrite: the named seam is
  already isolated; this only makes its domain explicit so a future `USize` entry point
  can be the structural fix.
