# Proposal

## Why

The pure `Bytes n := Fin n → UInt8` interpreter is the _specification_ — the
denotation every law is proved against — and it is accepted to stay slow. The
shipped C is what must be fast for real formats (JSON, TOML, protobuf, QR, PNG,
WAV), and it currently is not: the proven Layer-1 carriers cap at ~16–32 MiB/s
while the machine's `memcpy` floor is ~50 GiB/s and the one trusted `@[extern]`
`byteSlice` seam already runs ~55 GiB/s. The gap is a _representation_ problem
(boxed `UInt8`, boxed `Nat` cursor, `List` cons churn, nondeterminism plumbing),
not an algorithm problem, and the review concluded the pure interpreter can
never reach `memcpy` speed. The fix is to **stop trying to make the generic
interpreter fast** and instead ship a fast C path whose only proof obligation is
_agreement with the slow spec_.

## What Changes

- **A `blitBytes` Layer-2 seam** — generalize the shipped `byteSlice`/`commitRemainder`
  into a buffer-to-buffer `memcpy` (`ByteArray → USize → ByteArray → USize → USize → ByteArray`),
  with a reducible Lean body and a trusted C symbol, matching the `byteSlice` posture.
- **A `findByte`/`memchr` Layer-2 seam** — scan a `ByteArray` span for a byte, for
  JSON/TOML delimiter/whitespace skipping and string-escape detection, again Lean-body
  - trusted C.
- **A varint into-buffer seam** — read/write LEB128 directly at `lean_sarray_cptr`,
  the protobuf-dominant operation (the existing `VarBinary` stays the spec).
- **A numeric-parse seam** — wrap `strtod`/`strtoll` for JSON/TOML numbers, Lean body
  the slow reference parse.
- **A zlib `deflate`/`inflate` seam** — for PNG's IDAT chunks; there is no pure-Lean
  deflate at `memcpy` speed, this is "unusable → usable".
- **Per-format specialized decoders/encoders** (WAV header struct + one PCM `memcpy`;
  protobuf tag/varint loop + length-delimited `blitBytes`; the others later), each
  proved **equal to the `Bytes n` spec once** by a `decodeArray_eq`-style refinement
  lemma, with `@[extern]` seams reserved for the raw-byte regions.
- **A deterministic single-result decode path** under the already-defined
  `Unambiguous`/`Functional` predicates (`Sound.lean`), for the unambiguous binary
  formats, so the shipped path no longer builds every backtracking branch.

**No change** to `decode`/`encode`/`decodeFull`/`encodeRepeat`'s `Bytes n` type or
their laws. The `Bytes n` spec remains the single denotation; every shipped fast
path is either proved `[propext, Quot.sound]`-equal to it or is a trusted Layer-2
seam whose Lean body is that same spec.

## Capabilities

### New Capabilities

- `codec/shipped-fast-path`: a shipped-C fast surface — `@[extern]` `memcpy`/`memchr`/
  varint/numeric-parse/zlib seams (each `byteSlice`-shaped: reducible Lean body +
  trusted C) plus per-format specialized decoders/encoders, all proved `[propext,
Quot.sound]`-equal to the unchanged `Bytes n` spec or named as runtime-only trust.

### Modified Capabilities

- `codec`: **clarify** the decoding requirement so the shipped fast path is
  explicitly _permitted_ to commit a deterministic choice when the description is
  `Unambiguous`/`Functional` (as already defined in `Sound.lean`), without weakening
  the unconditional backtracking law for the general case.

## Impact

- `Codec/ByteSlice.lean` (+ `.c`): generalize `byteSlice` into (or add alongside it)
  `blitBytes`; add `findByte`.
- New `Codec/NumParse.lean`/`.c`, `Codec/VarintFast.lean`/`.c`, `Codec/Zlib.lean`/`.c`
  seams (Lean body = spec, `@[extern]` C = trusted).
- New `Codec/Shipped/*.lean` (or `Codec/Format/*.lean`): per-format specialized
  decoders/encoders and their `decode*_eq`/`encode*_eq` refinement lemmas.
- `Codec/Packed.lean`: possibly a `USize`-cursor _seam_ variant (framed as Layer 2,
  not a proven refinement) or an `Unambiguous`-gated deterministic `decodeOne`.
- `Bench.lean`: per-format lanes (WAV raw / protobuf blobs / JSON scan) value-checked
  byte-for-byte against the spec, plus the existing `byteSlice`/`commitRemainder` lanes.
- Axiom record: `#print axioms Codec.roundtrip` stays `[propext, Quot.sound]`; each
  new seam's Lean body is `[propext, Quot.sound]`-clean (or none), the C excluded.
