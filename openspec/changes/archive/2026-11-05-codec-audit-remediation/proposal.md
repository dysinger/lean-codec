# Proposal

## Why

A four-reviewer hypercritical audit of `Codec/` (2026-11-05) found the proof corpus
itself in good shape — 242 of 243 theorems report `[propext, Quot.sound]`-only,
every structural law is exhaustive over all seven constructors, and mutation testing
confirms the laws are load-bearing rather than vacuous. The defects are all on the
**edges**: one theorem violates the axiom discipline while a docstring asserts the
opposite, nothing in the repository would have caught it, three docstrings cite
theorems that do not exist, and several `README.md` claims do not match the code.

The root cause is structural, not incidental: **this repository has no axiom gate at
all.** `-DwarningAsError` catches `sorry`, but nothing collects axioms, so the
`Classical.choice` half of the discipline is unenforced. That is the single reason
the one real leak survived to ship. `../lean-basen` has an `Axioms.lean`
`@[default_target]` lib with `#guard_msgs`; `lean-codec`, the dependency, does not —
the asymmetry is backwards.

## What Changes

- **Add an in-repo axiom gate** (`Axioms.lean`, `@[default_target]` lib with
  `#guard_msgs`) covering every public theorem, so `lake build` fails on a
  `Classical.choice` regression. This makes the existing
  `review-remediation` requirement "the axiom check SHALL be runnable inside this
  repository" actually true, which it currently is not.
- **Fix the `findByte_spec` axiom leak.** `Codec.findByte` is defined through
  `Array.findIdx?`, whose `DecidableEq UInt8` decision reaches classical logic, so
  `findByte_spec` reports `[propext, Classical.choice, Quot.sound]`. Both its
  docstring and `README.md` claim `[propext]` with "No `Classical.choice`". Replace
  the scan with a constructive `Nat`-recursion so the seam's law is genuinely
  `[propext, Quot.sound]`-only; if that proves infeasible, state the measured
  footprint and exclude the law from the gate explicitly rather than misreporting it.
- **Close the three false docstring claims**: `relUnambiguous_of_relAligned` (cited
  as proved; never written), `decodeOne`'s advertised completeness/equality theorem
  (unproved; the two uniqueness lemmas do not compose as written), and
  `decodeArray_functional_byte` (presented as a `Functional` instance; it is the
  mirror shape).
- **Close the cheap coverage gaps**: a `ConsumesByte` witness for `empty` (the only
  constructor without one), and a concrete `MeasureDecreases` supplier (the only
  hypothesis family with none, despite being satisfiable in ~20 lines).
- **Correct `README.md`** where it does not match the code: `[S3]` omits the shipped
  `takeWhile` triple, `[S4]` misstates the `foldr` types, two tables give
  contradictory `packedCands` figures, the `[D4]` lay-terms paragraph reinstates a
  diagnosis the `[D4]` block disavows, `[D7]` undercounts `chainl1`'s requirements,
  and Scope names the stale `lean-binary`.

## Capabilities

### New Capabilities

- `codec/axiom-gate`: the machine-enforced axiom discipline — an in-repo gate that
  collects and checks the axiom footprint of every public theorem on every build, so
  a `Classical.choice` regression fails the build instead of being found by a reader.

### Modified Capabilities

- `codec/review-remediation`: "The proof gate SHALL be enforced, not observed"
  already requires the axiom check to be runnable in-repo and to be documented as
  enforced only once the step exists. That requirement was never satisfied; this
  change satisfies it and strengthens it from "runnable by hand" to
  "enforced on every build".

## Impact

- **New file** `Axioms.lean` (+ `lakefile.lean` target); the library's `.ilean`
  footprint and CI time grow by one gate compilation.
- **`Codec/ByteSlice.lean`**: `findByte`'s definition and `findByte_spec`'s statement
  may change. `Codec/ByteSlice.c` is unaffected — the C symbol contract is unchanged
  and this stays a generic `memchr`-shaped seam, not per-format C.
- **`Codec/DecodeOne.lean`**: either a new completeness theorem or a corrected module
  header. `Codec/Sound.lean`: a new `relUnambiguous_of_relAligned` or a deleted
  docstring reference. `Codec/Decode.lean`: one `empty` witness.
- **`README.md`**: factual corrections only; no anchor `[D1]`–`[S6]` is removed.
- **Downstream**: `../lean-basen` pins `codec` by rev, so it needs
  `nix flake update codec` + `lake update codec` only if a _statement_ it consumes
  changes. `findByte`/`decodeOne` are not in `basen`'s import surface; `basen` uses
  the `decodeFull`/`decodeRepeat` family, which is untouched.
