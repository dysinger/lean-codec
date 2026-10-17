# Spec Delta

## MODIFIED Requirements

### Requirement: Length-indexed byte string

The library SHALL represent a byte string as a **length-indexed** value
`Bytes n := Fin n → UInt8` (a reducible alias over `Fin`-indexed functions),
where the length `n : Nat` is part of the type. There SHALL be exactly one
byte-string type serving as both the proof substrate and the run-model for the
_spec_. A **Layer-2 fast path** SHALL be permitted to introduce an
`Array UInt8`/`ByteArray` _result/transport_ surface, provided it is proved equal
to `Bytes n` (by a definitional law or an `[propext, Quot.sound]`-only
refinement) and is never a second spec substrate.

#### Scenario: The length is part of the type

- **WHEN** a byte string of length `n` is constructed
- **THEN** its type carries `n`, so every consumer knows the byte count without
  an auxiliary length field or an O(n) traversal.

#### Scenario: Indexing a byte string is a structural operation

- **WHEN** a byte `s : Bytes n` is read at index `i : Fin n`
- **THEN** the read `s i` is defined structurally (no side condition, no opaque
  `toList` projection) and reduces to a scalar indexed load.

#### Scenario: The transport surface is not a second substrate

- **WHEN** a Layer-2 fast path introduces an `Array UInt8`/`ByteArray` result surface
- **THEN** that surface is a transport layer proved equal to `Bytes n` (definitionally or
  `[propext, Quot.sound]`-only), not a second proof substrate, and `Bytes n` remains the single
  length-indexed substrate the spec and its laws are stated over.
