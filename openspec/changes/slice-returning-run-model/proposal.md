# Proposal

## Why

Two efficiency attempts failed, and they failed for one shared, now-precise
reason: they tried to speed up Lean's _boxed_ representation, but the cost the
bench actually measures is the **`List UInt8` result type itself** — a heap
`List` of cons cells (and `Nat` boxes) that the run-model returns at its API
edge. `decodeFullByteArray byte [8192]` costs ~300 µs building 8192 cons cells;
`encodeRepeat byte [1 MiB]` costs ~20 ms in an O(n²) `List.append` fold; the byte
_loop_ underneath is already `memcpy`-speed (~13 µs). The `@[extern]` fast path
added no speedup because the stdlib externs already own the byte loop; the
GC-less C backend plan was archived as unsound (`Nat→size_t` is a semantic change
Lean's IR doesn't support, `WellFounded.fix` is not a tail loop). The fix is not
a compiler and not more `@[extern]`: it is to **stop returning a `List` at the
hot edge**.

## What Changes

- **A slice-returning decode entry point** — `decodeByteArraySlice : Codec α →
ByteArray → Nat → Option (α × ByteArray × Nat)` (or a `ByteArray`-span
  result), whose `byte` case is one `a[i]` read + index increment and whose
  full-consumption case returns the _packed_ suffix `(ByteArray, size)`, never a
  `List` of cons cells. **Zero-copy**: the result aliases the source `ByteArray`.
- **A non-quadratic, packed encode accumulator** — make `ByteArray.push`-based
  accumulation (amortized O(n), pre-sized buffer) the _committed_ encode surface,
  replacing the O(n²) `List.append` fold of `encodeRepeat` (the `List` shape
  stays as the pure spec/denotation only).
- **Refinement proofs** transferring each new surface to the existing `Bytes`
  spec, `[propext, Quot.sound]`-only (no new axiom), reusing the machinery
  already in `Codec/DecodeByteArray.lean` and `Codec/ExternFastPath.lean`.
- **A `Bench.lean` lane** measuring the slice/push surface against the `List`
  baseline and a `memchr`-equivalent raw copy, so the speedup is _seen_ before
  any further codegen discussion.

## Capabilities

### New Capabilities

- `codec/slice-run-model`: a packed, zero-copy `ByteArray`-span decode surface
  (and its packed encode dual), proved equal to the `Bytes` spec.

### Modified Capabilities

- `codec`: the run-model gains a slice-returning decode entry point and a packed
  encode accumulator as the _committed_ executable surface; the `List` APIs and
  the `[propext, Quot.sound]`-only unconditional laws are unchanged.

## Impact

- New `Codec/DecodeByteArraySlice.lean` (or an extension of
  `Codec/DecodeByteArray.lean`) + an encode counterpart; new refinement lemmas in
  the transfer-law module.
- `Bench.lean` gains the head-to-head lane.
- **Depends on** `bytearray-carrier-decoders` (the `ByteArray` carrier) and
  **supersedes** the now-archived idea that a compiler backend or more
  `@[extern]` C is needed to reach near-C speed. The lifetime/aliasing contract
  of the zero-copy slice is a _named trust seam_ recorded in the design.
