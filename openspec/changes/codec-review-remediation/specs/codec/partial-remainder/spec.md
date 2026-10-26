# Spec Delta — `codec/partial-remainder`

## MODIFIED Requirements

### Requirement: The commit's refinement is definitional, and the only trust is the runtime C seam

`commitRemainder_spec : commitRemainder a c = ByteArray.mk (a.extract c.toNat a.size)` SHALL be a
definitional equality (unfold `byteSlice`'s body; `(ByteArray.mk a).data = a` is `rfl`). The
`@[extern "codec_byteSlice"]` symbol SHALL be the named Layer-2 trust seam, **excluded** from the
`#print axioms` gate: its trust is a _runtime C-contract_ (the emitted C matches the Lean body),
which no Lean proof can see, so it appears nowhere in a `[propext, Quot.sound]` law.

**Every Layer-2 seam SHALL carry its own Lean law pinning its body.** The seam set is
`byteSlice`, `blitBytes`, `findByte`, and `commitRemainder`; each SHALL have a
`*_spec` theorem whose statement spells out the intended result, so that the
Lean body is a _checked_ specification and not merely a compact definition
prose-adjacent to the C. A seam without a law SHALL be treated as an incomplete
seam: the C's contract names the Lean body as its specification, so if no theorem
fixes that body, "the C matches the Lean body" has no machine-checkable referent.
Laws SHALL state their own axiom footprint where it differs between seams (a seam
law needing `[propext]` because of a decidable equality SHALL say so, rather than
being presented as uniform with an axiom-free sibling).

#### Scenario: The trust is runtime-only and named, not an axiom

- **WHEN** `commitRemainder_spec` (and any law built on it) is checked
- **THEN** `#print axioms` reports `[propext, Quot.sound]` (zero `Classical.choice`, zero `sorry`)
  with no `byteSlice`-related axiom — because `byteSlice`'s Lean body is axiom-clean and the C is
  invisible to Lean; and the runtime C is documented as a named trust seam in `Codec/ByteSlice.lean`,
  never presented as "no trust".

#### Scenario: Every seam is pinned by a law

- **WHEN** the Layer-2 seam set is inspected
- **THEN** each of `byteSlice`, `blitBytes`, `findByte`, `commitRemainder` has a
  `*_spec` theorem restating its body's intended result (e.g.
  `byteSlice_spec a i = ByteArray.mk (a.data.extract i.toNat a.data.size)`), and
  a consumer or a bench cites that theorem rather than re-deriving the body.

#### Scenario: Module headers agree about whether a seam is wired in

- **WHEN** a module header describes a seam's role
- **THEN** it states whether the seam is on a library code path or available but
  unused, and two headers SHALL NOT contradict each other on that point. A header
  SHALL NOT name a seam as "the deferred commit" if no decoder actually calls it;
  the honest wording is "available (`commitRemainder`), while the proven path uses
  the axiom-clean transport".

### Requirement: The bench value-checks the partial commit byte-for-byte

The bench SHALL add a partial-remainder lane committing a **mid-buffer** `USize` cursor via
`commitRemainder`/`byteSlice`, SHALL value-check the result byte-for-byte against `Array.extract`
(never a length check), and SHALL report ns/op and per-byte throughput against the
machine-calibrated `memcpy` baseline as a **distinct** Layer-2 lane, with every figure `[measured]`.

**The seam's runtime value-checks SHALL be reachable in a default run.** A lane
that exists but cannot execute — because an earlier lane aborts the process, or
because it is sequenced behind work that depends on a scaling parameter — SHALL
be treated as absent. The seam boundary checks SHALL run unconditionally, before
any lane whose success can vary with input size, so that a default invocation
either reports them as passing or fails for a seam-related reason. The value-check
set SHALL include an **aliasing** case (the same buffer passed as both
`blitBytes` source and destination) and the boundary cases already required.

#### Scenario: A wrong commit fails at run time

- **WHEN** `commitRemainder a c` is timed at a mid-buffer `c`
- **THEN** the committed `ByteArray` is compared byte-for-byte to `ByteArray.mk (a.extract c.toNat
a.size)` and a mismatch throws — a semantically wrong fast path is caught by the bench, not only
  by the runtime trust contract.

#### Scenario: The seam checks actually execute

- **WHEN** the bench is invoked with no arguments (the default, largest input)
- **THEN** the seam boundary value-checks complete and report success, and no
  earlier lane aborts the process before them; a non-zero exit is attributable to
  the lane that failed, not to an unrelated prerequisite.

#### Scenario: An aliasing seam call is value-checked

- **WHEN** `blitBytes` is called with the same buffer as source and destination,
  with overlapping windows
- **THEN** the result is compared byte-for-byte against the Lean body's intended
  value, so an in-place optimization of the C that diverges from the body is
  caught by the bench.
