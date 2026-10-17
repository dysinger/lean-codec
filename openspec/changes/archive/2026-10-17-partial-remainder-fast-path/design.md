# Design

## Context

`carrier-performance-tuning` (complete, 11/11) established two facts by measurement and IR
inspection:

1. The pure carriers (`Bytes n`, the packed `Array UInt8`/`Nat` cursor) cap at ~30–42 MiB/s
   for the bulk write, because a pure immutable value is built by a per-element fold, which
   `memcpy` cannot do. The `encodeRepeat iso` lane (the same byte loop with carrier bookkeeping
   elided) reaches ~750 MiB/s — the accumulator floor — and `byteSlice` (the `@[extern]` suffix
   copy) reaches ~80 GiB/s, the `memcpy` floor.
2. `byteSlice` is currently **dead code**: its only caller is a bench lane, because
   `decode`/`encode`/`decodeFull` stay on `Bytes n` (unchanged) and `decodeFullArray`
   materializes its own remainder suffix by a slow `List.toArray.drop` fold.

The seed note `design-note-5th-move.md` concludes the next move is **not** a fifth carrier but a
**return-type + wiring** decision: let `byteSlice` be the single `memcpy` in a `ByteArray`-returning
commit, proved equal to the `Bytes n` spec. This design is that move, corrected by review.

## The F\* prior (corrected citation)

`../fstar-codec/src/Data.Codec.Types.fst` threads a **byte-position cursor `p : nat`** through
its decoder: `varint_decode_go s n p value shift` returns `Inr (v', p + 1)` — a `(value, byte
position)` pair, with **no slicing in the return path**. The `Seq.slice s p (p+n)` occurrences are
in _proof lemmas_ (`lemma_varint_decode_shift`, `lemma_varint_decode_consumed_le_len`, …) as a
shift-invariance reasoning device, not a runtime commit; `bytes_decode` slices _per recursive
step_, the opposite of "one commit-time copy." F\* is pure and has no `memcpy`. So the honest
parallel is: **F\* threads a `(value, consumed)` cursor; our `byteSlice` commit is a _new_ step, not
a port.** The varint's `shift : nat` accumulator (`shift + 7` per byte, `b * pow2 shift`) is a
_7-bit-group count_, not a stream bit index — a bit cursor is out of scope here.

## The design

### Cursor vs commit, and where `USize` lives

The packed decoder `decodeArray : Codec α → Array UInt8 → Nat → List (α × Nat)` (already in
`Codec/Packed.lean`, proved by `decodeArray_eq`) keeps its **`Nat` cursor** — a fixed binding
decision (task 3.1 IR finding: `USize` does not lower to a scalar for the carrier). The _commit_
step takes a **`USize`** index, matching `byteSlice`'s own index directly. This sidesteps the
review's central finding: a `Nat`-indexed commit would force a `(c.toUSize).toNat = c` roundtrip
that needs `c < 2^System.Platform.numBits` — the exact platform fact this repo refuses to assume.
By making `commitRemainder` `USize`-indexed, the `Nat → USize` conversion happens **once, at the
call site** (the caller converting its `Nat` cursor), and the commit's own law is definitionally
clean.

### The surface

```lean
-- the existing cursor decoder, re-exposed with the partial-remainder contract explicit
decodeArrayFast : Codec α → Array UInt8 → Nat → List (α × Nat)
  -- := decodeArray  (a rename documenting "decode yields cursors, nothing is materialized")

-- the single commit: one byteSlice/memcpy turning a USize cursor into a ByteArray remainder
commitRemainder (a : Array UInt8) (c : USize) : ByteArray :=
  byteSlice (ByteArray.mk a) c
```

`decodeArrayFast` is **not** a new decoder — it is `decodeArray` re-exported under a name that
documents the "return a cursor, commit later" contract. The only genuinely new code is
`commitRemainder` (a one-line `byteSlice` wrapper) and one law.

### Why not bake `byteSlice` into each decode result

A per-result `byteSlice` would run one `memcpy` per backtracking result, so a decode yielding `k`
results does `k` copies — inflating the "reached the floor" number by `k` exactly as the prior
session's 2× throughput error did. The cursor-only decoder keeps decode allocation-light and
deferred, and the single `memcpy` happens once, at commitment, on the result the caller chooses.
This is the same split F\* makes (cursor-returning decoder, no commit-time copy), and the `memcpy`
here is new.

### The refinement (all definitional — no new equality to `decode d`)

```lean
theorem commitRemainder_spec (a : Array UInt8) (c : USize) :
    commitRemainder a c = ByteArray.mk (a.extract c.toNat a.size) := by
  rfl
```

This is definitional: `commitRemainder` unfolds to `byteSlice (ByteArray.mk a) c`, whose body is
`ByteArray.mk ((ByteArray.mk a).data.extract c.toNat ((ByteArray.mk a).data.size))`; both
`(ByteArray.mk a).data = a` and the `.size` coincidence are `rfl`. There is **no** `Nat ↔ USize`
roundtrip (the index is already `USize`), so **no** `System.Platform.numBits` premise enters.

Two facts the prior (reviewed, rejected) draft got wrong, recorded here so they are not repeated:

- **The `byteSlice` trust is a runtime C-contract, not a Lean proof step.** `@[extern]` swaps only
  the emitted C; `byteSlice`'s Lean body still reduces, so no Lean proof can see the trusted C.
  `#print axioms Codec.commitRemainder_spec` reports `[propext, Quot.sound]` (indeed `rfl`-clean)
  **regardless**, with no `byteSlice`-related axiom. The trust is documented in prose in
  `Codec/ByteSlice.lean` (the F\*-vs-KaRaMeL posture), and it is **not** part of any law. It is a
  category error to call it "the single trusted step of `commitRemainder_spec`."

- **The refinement to `decode d` is the already-proved `decodeArray_eq`.** `decodeArrayFast :=
decodeArray`, so `(decodeArrayFast d a i).map (fun (x, c) => (x, commitRemainder a c.toUSize))`
  is related to `decode d` through `decodeArray_eq` (plus the caller's `Nat → USize` conversion at
  the call site). This change adds **no** new theorem equating anything to `decode d`.

### The bench

Add `benchCommitRemainder n` committing a **mid-buffer** `USize` cursor `c = (n / 3).toUSize` (not
the full-consumption suffix the existing `byteSlice` lane uses), value-checking
`commitRemainder src c` byte-for-byte against `ByteArray.mk (src.extract c.toNat src.size)`, and
reporting ns/op + MiB/s against the `memcpy` calibration as a distinct Layer-2 lane. This is the
partial-remainder case the existing lane does not cover.

## Measurement and acceptance

Every figure `[measured]` (run the bench, never hand-typed). Acceptance: the partial
`commitRemainder` lane value-checks byte-for-byte and reports throughput against the `memcpy`
baseline; `commitRemainder_spec` is `rfl`-clean (`#print axioms` ⇒ `[propext, Quot.sound]`);
`lake build` zero `sorry`/warnings; and `#print axioms Codec.roundtrip` ⇒ `[propext, Quot.sound]`
(unchanged).

## What this design does not do

- Does **not** introduce a fifth carrier (`ByteArray` is already the packed result type).
- Does **not** change `decode`/`encode`/`decodeFull`/`encodeRepeat` (they stay `Bytes n`).
- Does **not** add a new equality to `decode d` (the refinement is the existing `decodeArray_eq`).
- Does **not** introduce a general bit-within-byte cursor (the F\* `shift` accumulator is a
  varint-local 7-bit-group count).
- Does **not** fold the `byteSlice`/C trust into a law (it is a prose-documented runtime contract,
  invisible to Lean, excluded from the axiom gate).
- Does **not** claim near-C speed of the general interpreter for arbitrary `α` on real workloads —
  that remains out of scope.
