# Proposal

## Why

`codec` is a verified byte-exact bidirectional codec: one `Codec α` description gives
both an encoder and a decoder, with the unconditional `roundtrip`/`decode_spec`/`bidir`
laws proved `[propext, Quot.sound]`-only over the length-indexed carrier
`Bytes n := Fin n → UInt8`. The intended use is parsing and serializing real binary
formats — JSON, PNG, QR, WAV, FLAC, Protobuf — so the description _interpreter_
(`decode d s` / `encode d x`) must run near C speed for arbitrary `α`, not just for a
single-byte repetition.

The read path is already there: `s ⟨i,·⟩` is a scalar indexed load. What is missing is a
fast _result carrier_ for the interpreter. `decode` returns `List (α × Suffix n)` — a heap
cons cell and a `Suffix`/`Bytes` closure per result — and `encode` builds a nested
`concat` closure per element. That is the cost this change removes, by giving the
interpreter a **packed `USize`-cursor result carrier** proved equal to the `Bytes n`
spec. The carrier swap, not a compiler and not more `@[extern]` C, is the lever: both
alternatives are already ruled out by prior recorded work (`compiler-tier-extraction`
archived as unsound; `extern-c-fast-path` recorded as a no-op shim over the stdlib's own
externs).

## What Changes

- **A packed `USize`-cursor decoder** (`decodeArray`) that reads `a[i]` by `USize` index,
  threads `i + m` through `seq`, and preserves `decode`'s full backtracking semantics
  (`alt` is the union `++`, `seq` is the `flatMap` cross-product). Its result is
  `List (α × USize)` — the `List` is the non-determinism multiplicity, which a faithful
  `decode` cannot drop; the packed carrier removes only the _per-branch_ `Suffix`/`Bytes`
  closure, not the `alt`/`seq` result `List`.
- **A packed full-consumption result** `decodeFullArray : … → Option (ByteArray × USize)`
  — one suffix copy, never `Option (List α × Suffix n)`.
- **A packed encoder** `encodeArray : Codec α → α → Option (Array UInt8)`, plus the
  byte-sequence packer `encodeByteArrayBytes : List UInt8 → ByteArray`, both accumulating
  via `ByteArray.push` instead of a `concat`-closure fold.
- **One refinement theorem per packed carrier**, proved `[propext, Quot.sound]`-only,
  equating the packed run to the unchanged `Bytes n` spec: `decodeArray_eq`,
  `decodeFullArray_spec`, `encodeArray_eq`, `encodeByteArrayBytes_eq`.
- **Two proof layers, both shipped and never conflated** (see the design):
  - **Layer 1 — proven, zero trusted C**: the packed carrier above, `[propext,
Quot.sound]`-only, proof body `ByteArray.mk ((a.data.toList.drop i.toNat).toArray)`.
  - **Layer 2 — named trust seam**: an `@[extern]` `byteSlice` (a `memcpy`-style suffix
    copy) whose Lean body elaborates (so it does not add an axiom) but whose running C is
    _trusted, not proven_; it is excluded from the `#print axioms` gate and wired onto a
    packed path only.

## Capabilities

### New Capabilities

- `codec/performance`: the acceptance criterion that the packed `USize`-cursor
  interpreter is a genuine refinement of the `Bytes n` spec (`decodeArray_eq` etc.,
  `[propext, Quot.sound]`-only, full backtracking preserved), measured against the
  bench's own calibrated baseline, with the two layers (proven vs trusted) reported as
  distinct lanes and never conflated.

### Scope

**In scope**: the packed `USize`-cursor carrier (`decodeArray` / `decodeFullArray` /
`encodeArray`, typed over arbitrary `Codec α`) and its refinement proof against the
unchanged `Bytes n` spec — i.e. the _correctness_ of a packed result carrier, proved
`[propext, Quot.sound]`-only, with full backtracking preserved.

**Out of scope**: proving or benchmarking that the general interpreter _runs near C for
arbitrary `α` on real workloads_ (JSON/PNG/protobuf), and any optimization of the
heterogeneous interpreter's speed beyond the isolated byte-sequence/`byte`-slice lanes.
The carrier and its proof land here; the general near-C performance claim is a separate
follow-up.

## Impact

- `Codec/Encode.lean`: already contains the packed encode accumulator (`fastEncodeRepeat`,
  `pushBytesFrom`, `array_readback`, and the clean readback lemmas `list_ofFn_getElem_clean`,
  `ofFn_concat`, `pushBytesFrom_eq`), all `[propext, Quot.sound]`-only and committed-ready.
- New packed decoder/encoder modules re-exported from the `Codec` root.
- `ExternFastPath.lean`/`.c`: the `@[extern]` `byteSlice` trust seam (re-introduced, not
  recovered — the extern tier was deleted), wired onto a packed path.
- `Bench.lean`: two honest lanes (proven packed carrier; `@[extern]` `byteSlice` floor),
  each byte-exact value-checked.
- Axiom record unchanged: `#print axioms Codec.roundtrip` ⇒ `[propext, Quot.sound]`.
