# Spec Delta — `codec` (the repetition requirement)

## MODIFIED Requirements

### Requirement: Unbounded repetition is a total denotation

Unbounded repetition (`many`, paper §3.4) SHALL be realized as a total
least-fixpoint denotation with three separate interpretations, **not** as a
finite description value:

- `relRepeat (Rel p)` — the denotational relation (total for every step `p`),
  now over the length-indexed `Bytes n`;
- `decodeRepeat p h` — the productive decoder, **structural on the input's
  length index `n`** (or on a cursor into it), taking `h : ConsumesByte p` (each
  step consumes ≥ 1 byte) as its totality witness, over `Bytes n`;
- `encodeRepeat p` — the total encoder, structural on the value list, returning
  a `Bytes n` whose length is the sum of the element encodes.

The same requirement SHALL hold for the full-consumption restriction
`decodeFull p h`, which SHALL also be structural on the length index (or a
cursor), not `WellFounded.fix` on a dependent `Sigma`.

**The recursion scheme is a specification obligation, not an implementation
detail.** A definition whose recursion descends through `WellFounded.fix` on a
`Sigma`/`InvImage.wf` measure does not compile to a loop, so the public decoder
SHALL NOT be defined that way when a structural formulation over the same carrier
exists. This is measured, not stylistic: `review.md` `R5.1` records a **588×**
gap at n=4096 between the shipped well-founded definition and a structural fold
over the same types, calling the same `decode`/`bdrop` and returning the same
`Option (List UInt8)`, with a bit-identical result. Any exception to the
structural requirement SHALL carry a recorded measurement justifying it.

**Decode and encode SHALL run within a small single-digit multiple of C.** The
reference for "C" SHALL be a `memcpy`-class bulk byte operation measured in the
same process and run, and the ratio SHALL be reported as a ratio to it, not as a
machine-dependent absolute figure. This SHALL be verified by a bench lane that
**fails** when the ratio exceeds a stated bar, so the property cannot regress
silently.

The literal-decoding result types SHALL NOT be the runtime carrier. A decode step
SHALL return its value and a consumed count (a cursor), not a `List` of results
and not a materialized remainder; materializing either SHALL be confined to a
specification-level surface with a proved refinement. Rationale, measured: with
the cursor shape a bulk decode runs ~8.5× the `memcpy` floor, while the shipped
`List`-returning per-step shape runs ~47× and the search-shaped repetition
decoder ~10^5× — i.e. the deficit is the result type, not the language.

Documented throughput SHALL be a **measured** figure with its cause attributed,
distinguishing at minimum (a) the algorithm (search vs single pass), (b) the
result shape, and (c) boxed scalar arithmetic. A single ratio SHALL NOT be
presented as "the" ceiling for the library without naming which of those it
reflects.

#### Scenario: Productive repetition decodes in bounded steps

- **WHEN** `decodeRepeat p h (s : Bytes n)` is evaluated for a productive `p`
  (`Productive p`, equivalently `ConsumesByte p`)
- **THEN** it is a total function returning a finite list of
  `(value-list, remaining-buffer)` pairs in `n + 1` well-founded steps, each step
  consuming ≥ 1 byte of `s`, enumerating exactly the `relRepeat (Rel p)` results.

#### Scenario: Empty-matching repetition is genuinely infinite

- **WHEN** `p` matches the empty byte string (e.g. `pure ()`)
- **THEN** no finite decoder can enumerate all results (the value lists are
  unbounded: `relRepeat_unbounded_of_empty`), so `decodeRepeat` is defined only
  for productive `p` and never faked with a finite result.

#### Scenario: Repetition is over the single carrier

- **WHEN** `encodeRepeat p xs` and `decodeRepeat p h s` are called
- **THEN** both operate on the single length-indexed `Bytes` carrier; there is
  no transfer between a `List` spec and a slab run-model, and no `Classical.choice`
  enters the repetition laws.

#### Scenario: The repetition decoders compile to a loop

- **WHEN** `decodeFull p h n s` or `decodeRepeat p h n s` is evaluated on an
  input of length `n`
- **THEN** the recursion is structural on `n` (or a cursor over it), so the
  emitted native code contains a loop for the per-element step rather than
  `Acc`-based well-founded recursion; and the measured throughput at a fixed `n`
  is within the margin recorded by the bench's throughput-floor lane.

#### Scenario: The re-based definition is provably the old one

- **WHEN** the recursion scheme changes from `WellFounded.fix`-on-`Sigma` to
  structural
- **THEN** a bridge theorem states the new definition equals the old on every
  input, every pre-existing repetition law (`decodeRepeat_eq`,
  `decodeRepeat_spec`, `decodeFull_zero`, `decodeFull_some`,
  `decodeFull_ne_none`, `decodeFull_spec`, the `relRepeat` family) still holds
  for its stated statement, and the axiom footprint is still
  `[propext, Quot.sound]`-only with zero `Classical.choice` and zero `sorry`.

#### Scenario: Decode and encode are within a small multiple of C

- **WHEN** a decode or encode path is measured against a `memcpy`-class bulk
  operation in the same process and run
- **THEN** the reported figure is a **ratio** to that reference, the ratio is
  within a small single-digit multiple, and a bench lane asserts the bound and
  fails when it is exceeded — so an order-of-magnitude regression cannot land
  unnoticed. An absolute "MiB/s" floor SHALL NOT be used as the assertion, because
  it is machine-dependent and is tuned down rather than investigated.

#### Scenario: The decoder's result type is a cursor, not a list

- **WHEN** a decode step is checked for its runtime shape
- **THEN** it returns the decoded value together with a consumed count (so the
  caller can advance a cursor), rather than a `List` of candidates or a
  materialized remainder buffer; any `List`-returning spec form SHALL be tied to
  it by a proved refinement (`decodeArray_eq`-shaped) and SHALL NOT be the carrier
  the fast path runs on. Rationale is measured, not stylistic: the cursor shape
  runs ~8.5× the `memcpy` floor and the `List` per-step shape ~47×.

#### Scenario: A performance regression fails the bench

- **WHEN** a decoder's throughput at the bench's fixed `n` falls below the
  recorded floor
- **THEN** the bench lane aborts with a named failure rather than only printing a
  slower number, so the `R5.1` defect cannot silently return; and that lane SHALL
  be ordered before any lane that can be slow or abort, so the assertion is
  actually reached in a default run.
