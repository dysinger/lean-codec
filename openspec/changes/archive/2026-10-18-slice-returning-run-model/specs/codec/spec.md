# codec — slice-run-model capability (delta)

## ADDED Requirements

### Requirement: packed, zero-copy slice decode surface

The run-model SHALL provide a `USize`-indexed, `ByteArray`-span decode entry
point (`decodeByteArraySlice`) whose `byte` case is one indexed read + index
increment (no `List` cons cell, no per-element `Nat` box), and a full-consumption
variant (`decodeFullByteArraySlice`) that returns the packed suffix as a
`ByteArray`, never an `Option (List α × Nat)`.

#### Scenario: O(1) single-byte slice decode

- **WHEN** `decodeByteArraySlice Codec.byte a i` is called with `i < a.size`
- **THEN** it returns `some (a[i], i+1)` without allocating any `List` cell

#### Scenario: full-consumption returns packed suffix

- **WHEN** `decodeFullByteArraySlice Codec.byte a 0` is called
- **THEN** it returns the packed suffix bytes (a `ByteArray`), not a `List UInt8`

### Requirement: packed, amortized-O(n) encode accumulator

The run-model SHALL provide a packed encode accumulator (`encodeByteArrayBytes`)
that appends into a pre-sized `ByteArray` buffer (amortized O(n)), replacing the
O(n²) `List.append` fold as the committed encode surface.

#### Scenario: no quadratic append

- **WHEN** encoding an `n`-byte list via the accumulator
- **THEN** the byte work is amortized O(n) (no repeated `List.append` traversal)

## MODIFIED Requirements

### Requirement: laws preserved unconditionally

The slice/packed surfaces SHALL each be proved equal to the existing `Bytes` spec
by a refinement lemma, keeping the codec's laws unconditional with
`#print axioms` = `[propext, Quot.sound]` and zero `sorry`. The `List`-returning
APIs and their laws are unchanged and remain available.

#### Scenario: the `many` case is the least-fixpoint law, over unchanged `Rel`

- **WHEN** the change lands
- **THEN** the core `Rel` (the six constructors) is unchanged; the `many` case
  is realized by `relRepeat` (the least fixpoint) and `decodeRepeat_spec` (the
  `many`-case bidirectional law), and `#print axioms` on each law reports
  `[propext, Quot.sound]` with zero `sorry`.

#### Scenario: slice surface is spec-equal

- **WHEN** the slice decode / packed encode change lands
- **THEN** a `_eq`/`_spec` lemma closes each against the existing spec, and the
  axiom record is unchanged (`[propext, Quot.sound]`, never `Classical.choice`)
