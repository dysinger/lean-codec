# Spec Delta

## ADDED Requirements

### Requirement: A partial-remainder commit is a single `memcpy`, cursor-indexed by `USize`

The fast path SHALL expose a commit step `commitRemainder : Array UInt8 → USize → ByteArray`,
defined as `byteSlice (ByteArray.mk a) c`, that materializes the remainder `[c.toNat, a.size)`
as a contiguous `ByteArray` by one `byteSlice`/`memcpy`. The index SHALL be `USize` (matching
`byteSlice`'s own index), so the commit's specification is definitional — **no** `Nat ↔ USize`
roundtrip and **no** `System.Platform.numBits` premise enter the law. The cursor-returning
decoder it commits against SHALL be the existing `decodeArray` (the `Nat`-cursor decoder),
unchanged; the decoder SHALL NOT perform any `byteSlice` during decode (which would multiply the
`memcpy` cost by the number of backtracking results).

#### Scenario: One memcpy per committed result, not per branch

- **WHEN** a partial decode yields `k` `(value, Nat-cursor)` results for one input (`alt` union / `seq` cross-product)
- **THEN** `decodeArray` returns `k` cursor pairs with **no** `byteSlice` performed; and committing
  one result runs exactly one `byteSlice`/`memcpy` via `commitRemainder` at the `USize` conversion
  the caller chooses.

### Requirement: The commit's refinement is definitional, and the only trust is the runtime C seam

`commitRemainder_spec : commitRemainder a c = ByteArray.mk (a.extract c.toNat a.size)` SHALL be a
definitional equality (unfold `byteSlice`'s body; `(ByteArray.mk a).data = a` is `rfl`). The
`@[extern "codec_byteSlice"]` symbol SHALL be the named Layer-2 trust seam, **excluded** from the
`#print axioms` gate: its trust is a _runtime C-contract_ (the emitted C matches the Lean body),
which no Lean proof can see, so it appears nowhere in a `[propext, Quot.sound]` law.

#### Scenario: The trust is runtime-only and named, not an axiom

- **WHEN** `commitRemainder_spec` (and any law built on it) is checked
- **THEN** `#print axioms` reports `[propext, Quot.sound]` (zero `Classical.choice`, zero `sorry`)
  with no `byteSlice`-related axiom — because `byteSlice`'s Lean body is axiom-clean and the C is
  invisible to Lean; and the runtime C is documented as a named trust seam in `Codec/ByteSlice.lean`,
  never presented as "no trust".

### Requirement: The partial-remainder fast path does not change the `Bytes n` spec

The refinement to the `Bytes n` spec SHALL remain the **already-proved** `decodeArray_eq`
(`Codec/Packed.lean`); this change adds **no** new equality to `decode d`. `decode`/`encode`/
`decodeFull`/`encodeRepeat` SHALL stay `Bytes n`-typed and their laws SHALL be untouched. Full
backtracking SHALL be preserved exactly — `alt` is the union `++`, `seq` is the `flatMap`
cross-product — and no greedy single-result narrowing SHALL be introduced.

#### Scenario: Backtracking is preserved, not narrowed

- **WHEN** the commit step is used against a partial decode
- **THEN** the value/cursor pairs come from the unchanged `decodeArray` (union / cross-product),
  the commit merely materializes a chosen cursor's remainder, and no decision is made during decode
  that discards an alternative result.

### Requirement: The bench value-checks the partial commit byte-for-byte

The bench SHALL add a partial-remainder lane committing a **mid-buffer** `USize` cursor via
`commitRemainder`/`byteSlice`, SHALL value-check the result byte-for-byte against `Array.extract`
(never a length check), and SHALL report ns/op and per-byte throughput against the
machine-calibrated `memcpy` baseline as a **distinct** Layer-2 lane, with every figure `[measured]`.

#### Scenario: A wrong commit fails at run time

- **WHEN** `commitRemainder a c` is timed at a mid-buffer `c`
- **THEN** the committed `ByteArray` is compared byte-for-byte to `ByteArray.mk (a.extract c.toNat
a.size)` and a mismatch throws — a semantically wrong fast path is caught by the bench, not only
  by the runtime trust contract.

## Scope

**In scope**: the `USize`-indexed `commitRemainder` (`byteSlice`-backed) and its definitional
refinement law `commitRemainder_spec`, the documented `decodeArrayFast` re-exposure of `decodeArray`,
and a byte-for-byte bench lane — with full backtracking preserved and the `Bytes n` spec unchanged.

**Out of scope**: a general bit-within-byte cursor for packed bit-fields (the F\* `shift`
accumulator is a varint-local 7-bit-group count, not a stream bit index); proving or benchmarking
near-C speed of the _general_ interpreter for arbitrary `α` on real workloads (JSON/PNG/protobuf);
and any change to `decode`/`encode`'s `Bytes n` return type.
