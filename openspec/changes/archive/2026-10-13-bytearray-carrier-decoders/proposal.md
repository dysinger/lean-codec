# Proposal

## Why

The provable core decodes over `Bytes = List UInt8` because `List` reduces under
`simp`/`rfl`/`induction` — but every byte of every input is a heap-allocated
`lean_object` cons cell, and the carrier _itself_ is the performance ceiling: each
byte access walks the spine. The `buffer-carrier-decoders` change added the
F\*-style two-tier move (a native, indexed run-model proved equal to the `List`
spec) but chose **`Array UInt8`** as the carrier. `Array UInt8` is a _pointer array
of individually-boxed `UInt8` values_ — O(1) indexed access, but each byte is still
a separately-allocated `lean_object`, so the per-byte boxing survives.

The stdlib's densest carrier is **`ByteArray`**: `structure ByteArray where
data : Array UInt8` whose `@[extern]` runtime representation is `lean_sarray`
(`LeanScalarArray`) — a contiguous `uint8_t*` buffer with a cached `size`/`capacity`
and `O(1)` `lean_byte_array_get`/`lean_sarray_size` primops (`memcpy`/`memcmp`-style,
no per-element boxing). This is, byte-for-byte, the F\* `Seq.seq byte`/`byte_seq`
model the paper's sibling work (miTLS, EverCrypt, HACL\*) uses, and it is the
_highest-performance stdlib carrier reachable without authoring FFI_ (decision #6
keeps FFI/compiler deferred). The `llvm-lean4-toolchain` change already enabled the
`@[extern]` primops that make `ByteArray` genuinely O(1); this change builds on top
of it rather than re-litigating the toolchain.

`Codec/Buffer.lean` already wraps `ByteArray`, but `decodeBuffer`/`encodeBuffer` are
a **transport barrier**, not a faster carrier: they materialize the full `List`
(`Buffer.toBytes`) and run the list interpreter on it. The missing piece is the
F\*-style **native `ByteArray` recursion with a `Nat` cursor**, defined directly over
the buffer, plus its equality proof against `decode d (a.data.toList.drop i)`.

## What Changes

- A **new module `Codec/DecodeByteArray.lean`** (plus `Codec/EncodeByteArray.lean`, or
  one combined module) defining the indexed, `ByteArray`-carrier interpreters:
  - `decodeByteArray {α} (d : Codec α) (a : ByteArray) (i : Nat) : List (α × Nat)` —
    the _same_ recursion as `decode`, reading `a[i]` (the `O(1)` `lean_byte_array_get`)
    instead of cons-peeling; the remainder is a `Nat` index, not a byte list.
  - `encodeByteArray {α} (d : Codec α) (x : α) : Option ByteArray` — the same
    recursion as `encode`, extending a `ByteArray` (via `push` / a reusable builder)
    instead of appending `List`s.
- **A varbinary / varint combinator over the `ByteArray` carrier**, as the first
  consumer and the motivating hot path:
  - `decodeVarint : ByteArray → Nat → List (Nat × Nat)` — the LEB128 read (7 data
    bits/byte, continuation high bit), the F\* `varint_decode_go` port over
    `a[i + k]`.
  - `encodeVarint : Nat → ByteArray` — the LEB128 write, the F\* `varint_encode_go`
    port.
  - The `Bytes`-level `varint : Iso Nat Bytes` kept as the _provable spec_ that these
    carrier functions are proved equal to (`decodeVarint_eq`/`encodeVarint_eq`).
- **Equality laws** — the F\*-style refinement, proved once in the existing
  `rfl`/`simp`/`induction` style (`[propext, Quot.sound]`, no `Classical`, no `extern`):
  the `ByteArray` interpreter agrees with the `List` spec through the `ByteArray.data`
  / `Array.toList` barrier, so every unconditional `Bytes`-level law (`decode_spec`,
  `bidir`, `roundtrip`) transfers by rewriting, not re-proving.
- **No changes to the `Codec` AST, `Rel`, `decode`, or `encode`** — the proof
  substrate stays `Bytes = List UInt8` (decision #1), and the `ByteArray` carrier is
  a _separate_ run-model, exactly as `Array UInt8` is today.
- **A standing representation decision, stated here and in the README** (see
  `Representations — two byte types, two jobs`): the run-model is **committed to
  `ByteArray`**, and `Array UInt8` is _not_ a type a caller should choose. The two
  byte types are assigned one job each — `Bytes` = proof substrate, `ByteArray` =
  run-model — and this change is where that split becomes the _standing_ rule rather
  than an incidental detail.

## Capabilities

### New Capabilities

_(None — this is a carrier/run-model extension with no observable capability delta;
`skip_specs: true`. The codec's denotation, which the README's `[D1]`–`[D8]`/
`[S1]`–`[S6]` tables describe, is unchanged.)_

### Modified Capabilities

_(None.)_

## Impact

- New modules `Codec/DecodeByteArray.lean` / `Codec/EncodeByteArray.lean` (or one
  combined `Codec/ByteArrayCodec.lean`) with the `ByteArray`-carrier interpreters and
  their refinement laws, plus the varbinary combinator over them.
- No change to `Codec`/`Rel`/`decode`/`encode`/`Sound`; the `Bytes` substrate stays
  the proof substrate. The existing `Array UInt8` carrier (`decodeArray`/`encodeArray`)
  **stays in the tree as a documented, non-canonical Tier-B stepping stone**, but the
  committed run-model surface is `ByteArray`. A future change may remove `Array UInt8`
  outright; this change records the decision but does not delete it (deleting a carrier
  is a separate, mechanical cleanup outside this change's proof work).
- `Bench.lean` (the §10.5/§10.6 extraction + benchmark harness) gains `ByteArray`
  carrier and `decodeVarint`/`encodeVarint` legs to measure the packed-buffer win
  against the `List` and `Array UInt8` baselines.
- Depends on the now-merged `llvm-lean4-toolchain` (the `@[extern]` primops that make
  `ByteArray.get`/`size`/`push` actually O(1) in the extracted C); without it the
  carrier collapses back to its pure-`List` fallback.
- Non-goals (unchanged): no FFI authored here, no compiler authored here, no codec
  semantics change, no `Classical`, no new proof axioms beyond `[propext, Quot.sound]`.
