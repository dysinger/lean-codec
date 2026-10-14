# Spec Delta

## Purpose

Defines the single byte-string substrate the codec's relation, decoder, and
encoder are stated over: a length-indexed byte string that is both structurally
reducible for proofs and a scalar indexed load in the emitted code.

## ADDED Requirements

### Requirement: Length-indexed byte string

The library SHALL represent a byte string as a **length-indexed** value
`Bytes n := Fin n → UInt8` (a reducible alias over `Fin`-indexed functions),
where the length `n : Nat` is part of the type. There SHALL be exactly one
byte-string type serving as both the proof substrate and the run-model; no
second `List`/`Array`/`ByteArray`/`Buffer` carrier SHALL exist.

#### Scenario: The length is part of the type

- **WHEN** a byte string of length `n` is constructed
- **THEN** its type carries `n`, so every consumer knows the byte count without
  an auxiliary length field or an O(n) traversal.

#### Scenario: Indexing a byte string is a structural operation

- **WHEN** a byte `s : Bytes n` is read at index `i : Fin n`
- **THEN** the read `s i` is defined structurally (no side condition, no opaque
  `toList` projection) and reduces to a scalar indexed load.

### Requirement: Finitary byte equality is decidable without classical logic

Equality of two byte strings of equal length SHALL be decidable and provable by
finite pointwise comparison (`∀ i : Fin n, s₁ i = s₂ i`), and every law stating
a byte-string equality SHALL close using only `[propext, Quot.sound]` — never
`Classical.choice`.

#### Scenario: Pointwise equality is finitary

- **WHEN** two byte strings `s₁ s₂ : Bytes n` are compared
- **THEN** `s₁ = s₂` is equivalent to `∀ i : Fin n, s₁ i = s₂ i`, and that
  equivalence is provable by `induction n`/`fin_cases` with no classical axiom.

### Requirement: Substring structure carries the consumed length

A decode's remaining buffer SHALL be a shorter `Bytes m` together with a proof
that `m ≤ n` and the remainder is a (possibly empty) suffix of the input — a
`Σ`/subtype "consumed length" witness, not a bare tail of a `List` whose length
must be re-derived.

#### Scenario: Remaining buffer records how many bytes were consumed

- **WHEN** `decode c (s : Bytes n)` returns a `(value, remainder)` pair
- **THEN** `remainder` is a `Bytes m` for some `m ≤ n`, and the fact that `m`
  bytes were consumed is a named witness, not a recomputed `List.length`.
