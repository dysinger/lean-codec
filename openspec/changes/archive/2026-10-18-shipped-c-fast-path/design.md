# Design

## Context

`byteSlice` (shipped in `carrier-performance-tuning`) and `commitRemainder`
(shipped in `partial-remainder-fast-path`) already establish the Layer-2 posture:
a `@[extern]` primitive whose **Lean body** is `ByteArray.mk (a.data.extract i.toNat
a.data.size)` (reducible, so laws close `[propext, Quot.sound]`-only) and whose
**running C** (`codec_byteSlice` in `ByteSlice.c`) is a single trusted `memcpy`,
excluded from the axiom gate. The review's measurement is decisive: the pure
`Bytes n` carriers cap at ~16–32 MiB/s because a pure immutable value is built by a
per-element fold (boxed `UInt8`, boxed `Nat` cursor, `List` cons churn,
nondeterminism plumbing), while `byteSlice` runs ~55 GiB/s — the `memcpy` floor.

`decodeArray_eq` (`Codec/Packed.lean`) is the refinement template: a packed
interpreter proved `[propext, Quot.sound]`-equal to the spec `decode`, once, by
induction on the description plus transport lemmas. `Sound.lean` already defines
`Unambiguous`/`Functional` and proves `encode_of_decode`/`encode_injective_of_unambiguous`.

## Goals / Non-Goals

**Goals:**

- Ship C that runs at `memcpy`/`memchr`/`strtod`/zlib speed for the raw-byte and
  compression regions of real formats, while keeping the pure `Bytes n` interpreter
  as the single, slow, spec denotation.
- Generalize the `byteSlice` seam into a buffer-to-buffer `blitBytes` and a
  `findByte`/`memchr`, and add varint-span, numeric-parse, and zlib seams — each
  with a reducible Lean body.
- Add per-format specialized decoders/encoders proved `[propext, Quot.sound]`-equal
  to the generic spec, starting with WAV and protobuf (clearest `memcpy`-shaped
  hot paths).
- Add an `Unambiguous`/`Functional`-gated deterministic decode so unambiguous
  binary formats skip backtracking branch-building.

**Non-Goals:**

- Making the generic pure `Bytes n` interpreter fast (accepted slow spec).
- A new GC-less compiler backend (see the skill §7: `USize` is a scalar, `Nat`
  boxes; there is no stock unboxed target; `@[extern]` seams are the stopgap).
- Proving the trusted C correct — it is a runtime contract, value-checked by the
  bench, never a theorem.

## Decisions

### The seam shape (unchanged from `byteSlice`)

Every seam is a `@[extern]` `def` with an elaborating Lean body (the _spec_), a
hand-written C symbol (the _trusted_ runtime), and a `lakefile.lean` `target` +
`moreLinkObjs` wiring the `.c` object only into the executable that consumes it
(never the proven library). `#print axioms` on the body is `[propext, Quot.sound]`-clean
(or none); the C is invisible. This is the same shape `byteSlice` already uses.

### `blitBytes` and `findByte` are `USize`-indexed

Like `byteSlice`/`commitRemainder`, the new bulk seams take `USize` offsets, so
their Lean-body refinement laws are `rfl` (no `Nat ↔ USize` roundtrip, no
`System.Platform.numBits` premise). The `Nat → USize` conversion stays at the call
site (the caller holding a `Nat` cursor).

### Specialization is proof-scoped, not a second interpreter

Each format is a module with a specialized `wavDecode`/`protobufDecode`/… defined
_structurally_ over `Array UInt8` + a cursor (or a `ByteArray` + `USize`), proved
equal to the generic `decode` of a hand-written description by a `decodeArray_eq`-style
lemma. The raw-byte materialization calls `blitBytes` (Layer 2); the structural
parse stays Layer 1. No new interpreter, no re-litigating the `Bytes n` spec.

### Determinism is gated, not added to the spec

A `decodeOne`/committed-choice path is defined **only** with an `Unambiguous`/
`Functional` hypothesis, and is shown equal to the (unique) backtracking result
under that hypothesis. The unconditional `decode (d₁ | d₂) s = decode d₁ s ++
decode d₂ s` law is untouched. This keeps the general law unconditional while
letting unambiguous binary formats commit early.

## Risks / Trade-offs

- **Trust surface growth.** Each seam is a new trusted C symbol. Mitigation: keep
  seams _thin_ (one `memcpy`/`memchr`/`strtod`/zlib call), document each contract
  verbatim (the `ByteSlice.lean` header posture), and value-check each in the bench.
- **Per-format proof volume.** Each specialized decoder needs its own refinement
  lemma. Mitigation: start with WAV (header + one copy) and protobuf (varint/tag +
  length-delimited blit), which are structurally the simplest and prove the template.
- **`Unambiguous`/`Functional` proof burden.** Gating determinism needs those
  hypotheses proven per description. Mitigation: they are already defined and the
  binary formats (protobuf field tags, fixed WAV layout) are structurally unambiguous.
- **zlib is a real dependency.** PNG speed depends on a linked zlib. Mitigation:
  treat it as a seam like any other (Lean body = raw/stored reference, C = zlib),
  and note the dependency boundary in the module header.
