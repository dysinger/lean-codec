# Proposal

## Why

Four result carriers (`List UInt8` → `Buffer`/`ByteArray` → `Bytes n := Fin n → UInt8` →
packed `Array UInt8`/`Nat` cursor) have all been measured to cap at the same place: a pure,
immutable, length-indexed value whose bulk write is a per-element fold, which `memcpy`
cannot produce. The `@[extern]` `byteSlice` trust seam (shipped in `carrier-performance-tuning`)
is the only thing that reaches the `memcpy` floor (~80 GiB/s vs the carriers' ~30–42 MiB/s),
but it is **dead code** — nothing calls it, because `decode`/`encode` stay on `Bytes n` and
`decodeFullArray` materializes its own remainder suffix by a slow `List.toArray.drop` fold.

This change wires `byteSlice` to its one genuine consumer: a **partial-remainder commit**.
The packed decoder already returns `(value, consumed count)` cursors; the missing piece is a
single `memcpy` that turns a chosen cursor into a `ByteArray` remainder at commitment time.
That is the shape already proven in `../fstar-codec` (a `(value, byte-position)` cursor with
no commit-time materialization) — the `byteSlice` commit is the one step that is _new_ here.

## What Changes

- **`commitRemainder : Array UInt8 → USize → ByteArray`** — the single `memcpy` commit:
  `commitRemainder a c := byteSlice (ByteArray.mk a) c`. It is `USize`-indexed (matching
  `byteSlice`'s own index), so its specification is definitionally clean — **no** `Nat ↔ USize`
  roundtrip and **no** `System.Platform.numBits` premise (those are the caller's concern when
  it converts a `Nat` cursor).
- **`decodeArrayFast : Codec α → Array UInt8 → Nat → List (α × Nat)`** — a documented re-exposure
  of the existing `decodeArray` (the `Nat`-cursor decoder), _not_ a new decoder. Its only
  purpose is to name the "decode yields cursors, nothing is materialized during decode" contract.
- **One refinement law** `commitRemainder_spec : commitRemainder a c = ByteArray.mk (a.extract
c.toNat a.size)`, which is definitional (`rfl` after `byteSlice`'s body and `(ByteArray.mk a).data
= a`). The refinement to the `Bytes n` spec stays the **already-proved** `decodeArray_eq`;
  this change adds no new equality to `decode d`.
- **A bench lane** that commits a **mid-buffer** `USize` cursor via `commitRemainder`/`byteSlice`,
  value-checks byte-for-byte against `Array.extract`, and reports ns/op + MiB/s against the
  calibrated `memcpy` baseline as a distinct Layer-2 lane.

**No change** to `decode`/`encode`/`decodeFull`/`encodeRepeat` (they stay `Bytes n`-typed, laws
untouched). **No new carrier type**: `ByteArray` is already the packed result type. The only new
surface is the commit step and its specification.

## Capabilities

### New Capabilities

- `codec/partial-remainder`: a `USize`-indexed `commitRemainder` (`byteSlice`-backed) that
  materializes a `ByteArray` remainder from a consumed count, with a definitional refinement
  law and a byte-for-byte bench check; the cursor-returning decoder it commits against is the
  existing `decodeArray` (unchanged).

### Modified Capabilities

- `codec`: **relax** the "no second `List UInt8`/`Array`/`ByteArray`/`Buffer` carrier" clause in
  the decoding requirement — a distinct-named **Layer-2 fast path** MAY carry data on
  `Array UInt8`/`ByteArray`, provided it is proved (or definitionally) equal to `Bytes n` and is
  never conflated with the spec substrate. (This relaxation is required, not optional: the packed
  carrier already introduced `Array UInt8`/`ByteArray` surface in `carrier-performance-tuning`
  without this clause being updated; this change corrects that gap.)
- `codec/byte-string`: **relax** the "no second `List`/`Array`/`ByteArray`/`Buffer` carrier SHALL
  exist" clause the same way — the `Bytes n` spec substrate remains the single proof substrate and
  run-model; the relaxation permits Layer-2 fast paths whose `Array UInt8`/`ByteArray` surface is a
  _result/transport_ distinct from and proved equal to `Bytes n`, never a second spec substrate.

## Impact

- `Codec/ByteSlice.lean`: add `commitRemainder` (the `byteSlice` wrapper) — the first library
  consumer of the trust seam; the seam stays excluded from the `#print axioms` gate.
- `Codec/Packed.lean`: add `decodeArrayFast` (a rename of `decodeArray`, documented) and
  `commitRemainder_spec`.
- `Bench.lean`: a partial-remainder commit lane (mid-buffer `USize` cursor), value-checked.
- `README.md` §Performance, `AGENTS.md`: state the partial-remainder surface honestly and record
  the two carrier-requirement relaxations.
- Axiom record: `#print axioms Codec.roundtrip` ⇒ `[propext, Quot.sound]` (unchanged);
  `#print axioms Codec.commitRemainder_spec` reports `[propext, Quot.sound]`-only (definitional —
  the `byteSlice`→C trust is a runtime contract invisible to Lean, documented in `Codec/ByteSlice.lean`,
  not an axiom).
