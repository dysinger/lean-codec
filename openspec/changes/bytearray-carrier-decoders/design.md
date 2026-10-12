# Design

## Context

The F\*-style two-tier move already exists in this repo, on two carriers:

- `Bytes = List UInt8` — the _proof_ substrate (decision #1 in AGENTS.md). Every
  `List` lemma transfers; the wire cost is one `lean_object` node per byte.
- `Array UInt8` (`Codec/DecodeArray.lean`, `Codec/EncodeArray.lean`) — the Tier-B
  run-model, a `Nat`-indexed recursion proved equal to the `List` spec via
  `decodeArray_eq`/`encodeArray_eq` (`[propext, Quot.sound]` only).

Established and verified this session (against the pinned `lean4` 4.34.1 source at
`src/Init/Prelude.lean`, `src/Init/Data/ByteArray/Basic.lean`, `src/runtime/object.cpp`,
`src/runtime/object.h`, `src/runtime/buffer.h`):

- `ByteArray` is `structure ByteArray where data : Array UInt8`, with
  `attribute [extern "lean_byte_array_data"] ByteArray.data`. At runtime it is a
  `LeanScalarArray` (`lean_sarray`): a contiguous `uint8_t*` (`lean_sarray_cptr`)
  with cached `size`/`capacity` (`lean_sarray_size`), equality by `std::memcmp`
  (`lean_sarray_eq_cold`). **This is the "packed byte buffer" the stdlib docstring
  advertises, not a `List` or a pointer-array of boxed elements.**
- `Array UInt8` is `lean_array_object` — a pointer array (`m_data` of `void*`) where
  each `UInt8` is an individually-boxed `lean_object`. O(1) indexed access, but the
  per-byte boxing survives.
- The `llvm-lean4-toolchain` change (merged) turned the `@[extern]` primops on:
  `ByteArray.get`/`size`/`push` lower to `lean_byte_array_get`/`lean_sarray_size`/
  `lean_sarray_push` — genuinely O(1) — in the extracted C, whereas without LLVM they
  fell back to pure-`List`.
- `Codec/Buffer.lean` already wraps a `ByteArray` (`Buffer.byteArray`) but its
  interpreters are a _transport barrier_ (`decodeBuffer` = `decode d b.toBytes`,
  recomputing the full `List`), not a native-index recursion — so the byte-list cost
  is still paid on every decode.

Two lessons carry over from the `Array UInt8` carrier (encoded in
`buffer-carrier-decoders`) and must be respected here:

1. `Array`/`ByteArray` reduce via `.data`/`.toList` — reason over `a.toList`, reach
   `ByteArray` only through `ByteArray.data` (the reducible `Array`), **not** the
   opaque `ByteArray.toList`.
2. The _membership-form_ refinement `(x,j) ∈ decodeArray d a i ↔ (x, drop j) ∈
decode d (drop i)` was **wrong** for non-consuming `pure` and empty remainders
   (index info is lost by `drop`). Use the _function-level_ form:
   `decodeArray d a i = (decode d (drop i)).map (fun (x,r) => (x, i + (drop i).length - r.length))`.
   The `ByteArray` refinement must use the same function-level shape, not membership.

## Goals / Non-Goals

**Goals:**

- Add a third carrier — **`ByteArray` + `Nat` cursor** — to the run-model family,
  the _densest_ stdlib carrier (packed `uint8_t*`, no per-byte boxing), proved equal
  to the `Bytes` spec by the same function-level refinement as `decodeArray_eq`.
- Port the F\* LEB128 varbinary (`varint_decode_go`/`varint_encode_go`, 7 data
  bits/byte + continuation high bit) onto that carrier as the first real consumer and
  the motivating hot path, with the `Bytes`-level `varint : Iso Nat Bytes` kept as the
  provable spec the carrier functions are proved equal to.
- **Record the standing representation decision** (and its README statement): the
  run-model is committed to `ByteArray`, `Bytes` stays the proof-only substrate, and
  `Array UInt8` is demoted to a non-canonical stepping stone. This change is the point
  where that split stops being an incidental detail and becomes the stated rule.

**Non-Goals:**

- No FFI authored by us; no compiler authored here (decision #6 — the author-FFI/
  compiler tier stays deferred). This only _uses_ the now-enabled `@[extern]`
  primops.
- No change to `Codec`/`Rel`/`decode`/`encode`/`Sound`, and no change to the
  `Bytes` substrate; `decodeArray`/`encodeArray` stay as the `Array` milestone.
- **No deletion of the `Array UInt8` carrier in this change.** The decision (below)
  commits the run-model to `ByteArray` and demotes `Array UInt8` to a non-canonical
  stepping stone, but physically removing the module is a separate mechanical
  cleanup — recorded here as a follow-up, not silently folded into the proof work.
- No bit-level varbinary (packing across byte boundaries). The F\* varint is
  byte-aligned 7-bits/byte; true sub-byte packing would need a bit-offset threaded
  through decoder state, which is an explicit non-goal here (recorded as deferred,
  not silently dropped).
- No `Classical`, no new proof axioms; `[propext, Quot.sound]` only.

## Decisions

1. **`ByteArray`, not `Array UInt8`, is the new carrier.** `ByteArray` is the stdlib's
   only _packed_ byte container; `Array UInt8` boxes each byte. The varbinary hot path
   is a byte-cursor read, which is exactly what `ByteArray.get`/`size` are O(1) for
   post-LLVM. _Alternative considered:_ reuse `Array UInt8` (the existing carrier) —
   rejected: it never removes the per-byte boxing, so it cannot deliver the packed-
   buffer win that is the whole point.
2. **The ByteArray carrier is a _native_ index recursion, not composition over the
   `Array` carrier.** `decodeByteArray d a i : List (α × Nat)` recurses structurally on
   `d`, reading `a[i]` (the O(1) `lean_byte_array_get!` / `uget` primop) in the `byte`
   case and recursing `i+m` through `seq` — **never materializing a `List`**. The
   composition `decodeByteArray d a i = decodeArray d a.data i` (the earlier draft)
   _defeats the carrier_: it re-materializes `a.data.toList` and runs the list decoder,
   so it never reads a packed byte. The refinement proof (`decodeByteArray_eq`) closes
   via `a[i] = a.data[i]` (`ByteArray.getElem_eq_getElem_data`) against `decodeArray_eq`,
   no new induction. Same for `decodeFullByteArray`: a native `WellFounded.fix` on
   `a.size - i` threading one `Option (List α)` and reading `a[i]`, **not**
   `decodeFull` over `a.data.toList.drop i`.
   _Alternative considered (and rejected):_ composition over `decodeArray`/`decodeFull` —
   fewer lines, but it ships the same `List`-materialization + list-walk cost the
   carrier exists to remove, so the packed-`uint8_t*` win is never realized (measured:
   `decodeFullByteArray` ≈ `decodeFull` ≈ the list cost, ~0 gain).
3. **The refinement is the _function-level_ form over `a.data.toList.drop i`** (lesson
   1 + 2 above), proved through the reducible `ByteArray.data`, _never_ through the
   opaque `ByteArray.toList`. The transport law
   `ByteArray.data (ByteArray.mk l) = l.toArray`-adjacent rewrites close by `rfl`,
   exactly as `Buffer.toBytes`/`toBytes_ofBytes` already do.
4. **Varbinary lives on the carrier, with a `Bytes`-level `Iso` spec.** `varint :
Iso Nat Bytes` (encode via `varint_encode_go`, decode via `varint_decode_go`, the
   `varint` roundtrip proved once) is the _spec_; `decodeVarint`/`encodeVarint` over
   `ByteArray` are the _run-model_, proved equal via the carrier equality. Every
   codec law then transfers by composition, matching the `Iso`-driven combinator
   style already in `Codec/Iso.lean`/`Codec/Combinators.lean`. The bit arithmetic is
   `% 128`/`<<< 7`/`&&& 0x80` (or `pow2`-free shifts), the F\* form ported directly.
5. **`skip_specs: true`** — like the two prior infra changes, the codec's _observable_
   denotation is unchanged (a `ByteArray` carrier is a representation swap, not a new
   capability), so no spec delta exists and none is invented.
6. **The run-model is committed to `ByteArray`; `Array UInt8` is demoted to a
   non-canonical stepping stone.** Measured (arm64, reps=20): `decodeByteArray byte`
   ~112 ns vs `decodeArray byte` ~14.7 µs (the array's `.toList` transport), and
   `encodeByteArray byte` ~52 ns vs `encodeArray byte` ~441 ns. There is **no** axis
   on which `Array UInt8` beats `ByteArray`: it is strictly dominated on both decode
   (transport cost) and encode (boxed accumulation), and it is no more provable than
   `ByteArray` (both reduce through `.data`/`.toList`). So the executable surface a
   caller touches — `decodeByteArray`/`encodeByteArray`/`decodeFullByteArray` and the
   varbinary `decodeVarint`/`encodeVarint` — is `ByteArray`, with `Bytes` kept as the
   proof substrate and `Buffer` as the transport seam. This is recorded as the
   README's `Representations — two byte types, two jobs` section, and is a _standing_
   decision, not a one-off: a follow-up change removes the `Array UInt8` carrier
   outright; this change only establishes the rule.
   _Alternative considered (and rejected):_ a _single_ type that is both provable and
   fast. Impossible: `ByteArray.toList` is opaque (nothing reduces), and `List UInt8`
   boxes each byte (one heap cell per byte). The two-tier F\* shape — spec over the
   list, run-model over the packed buffer, proved equal — is the only way to have both.

## Risks / Trade-offs

- _[`ByteArray.data`'s `.toList` is the linear-time transport cost at the `Bytes`
  seam]_ → the win is _once transported_ every byte access is O(1) packed-buffer, not
  a node walk; the transport is the same cost `Buffer.toBytes` already pays. The spec
  stays over `Bytes` (decision #1), so this is inherent to the two-tier move, not a
  new cost.
- _[The speedup may still under-deliver if the run-model's `List (α × Nat)` result
  list dominates]_ → measure before claiming. The carrier removes the _byte access_
  cost; the result enumeration is the same nondeterministic `List` semantics. Recorded
  honestly in `Bench.lean` against the `Array`/`List` baselines rather than promised
  as a guaranteed multiplier.
- _[`ByteArray.push` reallocation on the encode side could be O(n²) if not amortized]_
  → use Lean's built-in amortized `ByteArray` builder (or accumulate and `mk` once) so
  encoding is O(n) amortized, mirroring `encodeArray`'s accumulator.
- _[A wrong membership-form refinement (lesson 2) re-introduces the `pure`/
  empty-remainder bug]_ → mandate the function-level form from the outset and reuse
  `decodeArray_eq`'s proof skeleton verbatim where possible.

## Migration Plan

1. Add `Codec/DecodeByteArray.lean` / `Codec/EncodeByteArray.lean` (or one combined
   module) with `decodeByteArray`/`encodeByteArray` and their `_eq` refinement laws.
2. Add the varbinary layer: `varint : Iso Nat Bytes` (spec) + `decodeVarint`/
   `encodeVarint` (ByteArray run-model) + their `_eq` laws; add the three transfer
   laws (`decodeByteArray_spec`-analogue, `encodeByteArray_rel`-analogue,
   `roundtripByteArray`-analogue) to `Codec/Sound.lean`.
3. Add `Bench.lean` legs; `nix build '.#check'` (proof gate) green with
   `[propext, Quot.sound]` unchanged; record before/after against the `List` and
   `Array UInt8` baselines.
4. Update `AGENTS.md` handoff and the `invertible-binary-core/tasks.md` ledger with
   the measured figures and the "densest carrier, still no FFI" finding.
5. Rollback = delete the new modules (no change to existing `Codec`/`Sound` files to
   roll back).

## Open Questions

- Whether one combined `Codec/ByteArrayCodec.lean` or the split
  `DecodeByteArray`/`EncodeByteArray` pair better matches the existing
  `Decode`/`Encode`/`DecodeArray`/`EncodeArray` layout — resolved during
  implementation by matching the existing split.
- Whether `decodeVarint` should return `List (Nat × Nat)` (the nondeterministic,
  full-backtracking shape) or a single `Option (Nat × Nat)` (the deterministic,
  full-consumption reading, like `decodeFull`) — resolved during implementation by
  matching the decoder it composes with; the varint is unambiguous, so both denotations
  agree, and the spec `varint : Iso Nat Bytes` pins whichever is chosen.
