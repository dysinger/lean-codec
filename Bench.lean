/- Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later -/

import Codec

/-!
# Extraction + benchmark harness (§10.5)

Drives the extracted `decode`/`encode` hot path and the semantic repetition
triple (`decodeRepeat`/`encodeRepeat`) on a multi-MB synthetic `byte`/`many`
description, recording wall-clock numbers that back the linear-time /
no-per-byte-boxing acceptance claim.

**Not** part of the proven core; imports nothing beyond `Codec`. The `unsafe`
annotations are confined to the periphery (byte-list construction and timing via
`IO.monoNanosNow`), never the interpreter under test.

The honest shape of the numbers (§10.5, task 1.6):

  * `decode Codec.byte s`         — peels one byte, O(1) (does not traverse `s`).
  * `encodeRepeat Codec.byte xs`  — linear in `xs.length` (structural recursion).
  * `Buffer.ofBytes` / `toBytes`  — the packed, no-per-byte-list-cell transport,
    linear in the byte count.
  * `decodeRepeat Codec.byte h s` — the backtracking "many" decoder; its *output*
    is all `m+1` prefixes, so it is inherently Θ(m²) in output size (paper §4.4)
    and is measured only at a small `m`.

Hot-path audit (§10.5, "no `getElem`-with-proof leak"): `decode` destructures its
input by `match`, never indexed access; `Buffer.toBytes` routes through
`ByteArray.data` (the reducible `Array`), not the opaque `ByteArray.toList`. The
provable substrate `Bytes = List UInt8` boxes each byte as a `lean_object`; the
*packed* (no-boxing) representation is `Buffer`, measured by the transport path.
-/

namespace Codec.Bench

open Codec

/-- `n` copies of the byte `0x01` as the provable `Bytes` substrate. -/
unsafe def bytesOf (n : Nat) : Bytes := List.replicate n (1 : UInt8)

/-- Time a batch of `reps` runs of `f : Nat → α`, returning the wall-clock
elapsed nanoseconds (total over the batch) as a `Nat`. The result `r` (the last
run's output) is returned so the caller can force it and the computation is not
dead-code-eliminated; callers divide by `reps` for a per-op figure. -/
unsafe def timeBatch (reps : Nat) (f : Nat → α) : IO (α × Nat) := do
  let mut r : α := f 0
  r := f 0
  let start ← IO.monoNanosNow
  for i in [0:reps] do
    r := f i
  let stop ← IO.monoNanosNow
  return (r, (stop - start))

unsafe def benchDecodeByte (n : Nat) (reps : Nat) : IO Unit := do
  let s : Bytes := bytesOf n
  let (_, dt) ← timeBatch reps fun _ => decode Codec.byte s
  IO.println s!"decode  byte [{n}]: {dt / reps} ns/op"

unsafe def benchEncodeRepeat (n : Nat) (reps : Nat) : IO Unit := do
  let xs : List UInt8 := bytesOf n
  let (r, dt) ← timeBatch reps fun _ => encodeRepeat Codec.byte xs
  match r with
  | some s =>
      if s.length != n then
        throw (IO.userError "encodeRepeat length mismatch")
  | none => throw (IO.userError "encodeRepeat returned none")
  IO.println s!"encodeRepeat byte [{n}]: {dt / reps} ns/op"

/-- The packed transport: `Buffer.ofBytes` (list → contiguous `ByteArray`) and
`Buffer.toBytes` (`ByteArray` → list) are both linear and touch every byte; this
is the no-per-byte-list-cell surface of §10.5. -/
unsafe def benchBufferTransport (n : Nat) (reps : Nat) : IO Unit := do
  let xs : Bytes := bytesOf n
  let (b, dt1) ← timeBatch reps fun _ => Buffer.ofBytes xs
  let (_, dt2) ← timeBatch reps fun _ => b.toBytes
  IO.println s!"Buffer.ofBytes [{n}]: {dt1 / reps} ns/op"
  IO.println s!"Buffer.toBytes  [{n}]: {dt2 / reps} ns/op"

/-- The backtracking "many" decoder (quadratic output, paper §4.4), kept at a
small `n`. Confirms it yields `n+1` prefixes. -/
unsafe def benchDecodeRepeat (n : Nat) : IO Unit := do
  let s : Bytes := bytesOf n
  let (out, dt) ← timeBatch 1 fun _ => decodeRepeat Codec.byte byte_consumesByte s
  if out.length != n + 1 then
    throw (IO.userError s!"decodeRepeat: expected {n+1} prefixes, got {out.length}")
  IO.println s!"decodeRepeat byte [{n}]: {dt} ns"

/-- The Tier A full-consumption repetition decoder: the §4.4/§10.6 target. Unlike
`decodeRepeat` (which materializes all `n+1` prefixes), this threads one `Option` and
returns `some (replicate n byte)` for the whole input. At the `m`-scale this should be
an order of magnitude faster than `decodeRepeat`. -/
unsafe def benchDecodeFull (n : Nat) (reps : Nat) : IO Unit := do
  let s : Bytes := bytesOf n
  let (r, dt) ← timeBatch reps fun _ => decodeFull Codec.byte byte_consumesByte s
  match r with
  | some xs =>
      if xs.length != n then
        throw (IO.userError s!"decodeFull: expected {n} bytes, got {xs.length}")
  | none => throw (IO.userError "decodeFull: expected some, got none")
  IO.println s!"decodeFull byte [{n}]: {dt / reps} ns/op"

/-- The `decodeRepeatFull` alias (same full-consumption decoder as `decodeFull`),
measured to confirm it shares the fast path, with the same byte-exact assertion. -/
unsafe def benchDecodeRepeatFull (n : Nat) (reps : Nat) : IO Unit := do
  let s : Bytes := bytesOf n
  let (r, dt) ← timeBatch reps fun _ => decodeRepeatFull Codec.byte byte_consumesByte s
  match r with
  | some xs =>
      if xs != s then
        throw (IO.userError "decodeRepeatFull: byte mismatch")
  | none => throw (IO.userError "decodeRepeatFull: expected some, got none")
  IO.println s!"decodeRepeatFull byte [{n}]: {dt / reps} ns/op"

/-- The fused single-step decoder `decodeFast`: peels one `Codec.byte` in O(1),
deny-re-traversing. Confirms `decodeFast` equals `decode` (one result). -/
unsafe def benchDecodeFast (n : Nat) (reps : Nat) : IO Unit := do
  let s : Bytes := bytesOf n
  let (r, dt) ← timeBatch reps fun _ => decodeFast Codec.byte s
  if r != decode Codec.byte s then
    throw (IO.userError "decodeFast ≠ decode")
  IO.println s!"decodeFast byte [{n}]: {dt / reps} ns/op"

/-- The packed (`Buffer`-backed) single-byte roundtrip across the transport
barrier (§10.4): `encodeBuffer`/`decodeBuffer` of `Codec.byte`, byte-exact. -/
unsafe def benchRoundtripBuffer (reps : Nat) : IO Unit := do
  let (encoded, dt1) ← timeBatch reps fun _ => encodeBuffer Codec.byte (1 : UInt8)
  match encoded with
  | none => throw (IO.userError "encodeBuffer byte returned none")
  | some b =>
      let (decoded, dt2) ← timeBatch reps fun _ => decodeBuffer Codec.byte b
      match decoded with
      | [(x, r)] =>
          if x != (1 : UInt8) || r.toBytes != [] then
            throw (IO.userError "roundtrip Buffer: byte mismatch")
      | _ => throw (IO.userError "roundtrip Buffer: expected one full-consumption result")
      IO.println s!"encodeBuffer byte: {dt1 / reps} ns/op"
      IO.println s!"decodeBuffer byte: {dt2 / reps} ns/op"

/-! ## The array-carrier run-models (§10.6, buffer tier)

`decodeArray`/`encodeArray`/`decodeFullArray` are the F\*-style run-models over the
`Array UInt8` carrier (§10.6 / the `buffer-carrier-decoders` change), *proved equal*
to the list specs. These legs measure the carrier swap against the §10.5 list-carrier
baselines; the array decoder reads `a[i]` by index (no per-byte cons-peel). -/

/-- The `n` bytes as an `Array UInt8` (the `List`-backed `Array.mk`, reducible to
its `toList`; no `ByteArray` involved). -/
unsafe def arrayBytesOf (n : Nat) : Array UInt8 :=
  (bytesOf n).toArray

/-- The array-carrier single-step decoder: `decodeArray Codec.byte a 0` peels one
byte in O(1) by index. Confirms it yields `[(1, 1)]`. -/
unsafe def benchDecodeArray (n : Nat) (reps : Nat) : IO Unit := do
  let a : Array UInt8 := arrayBytesOf n
  let (r, dt) ← timeBatch reps fun _ => decodeArray Codec.byte a 0
  let expected : List (UInt8 × Nat) := [(1, 1)]
  if r != expected then
    throw (IO.userError s!"decodeArray byte: expected [(1,1)], got {r}")
  IO.println s!"decodeArray byte [{n}]: {dt / reps} ns/op"

/-- The array-accumulating single-step encoder: `encodeArray Codec.byte 1` yields
`some #[1]`. -/
unsafe def benchEncodeArray (reps : Nat) : IO Unit := do
  let (r, dt) ← timeBatch reps fun _ => encodeArray Codec.byte (1 : UInt8)
  match r with
  | some a =>
      if a != #[1] then throw (IO.userError "encodeArray byte: expected #[1]")
  | none => throw (IO.userError "encodeArray byte: expected some")
  IO.println s!"encodeArray byte: {dt / reps} ns/op"

/-- The array-carrier full-consumption repetition decoder: `decodeFullArray` of
`Codec.byte` over `n` bytes should return `some (replicate n 1, n)`. -/
unsafe def benchDecodeFullArray (n : Nat) (reps : Nat) : IO Unit := do
  let a : Array UInt8 := arrayBytesOf n
  let (r, dt) ← timeBatch reps fun _ => decodeFullArray Codec.byte byte_consumesByte a 0
  match r with
  | some (xs, j) =>
      if xs.length != n || j != n then
        throw (IO.userError s!"decodeFullArray byte: expected ({n},{n}), got ({xs.length},{j})")
  | none => throw (IO.userError "decodeFullArray byte: expected some")
  IO.println s!"decodeFullArray byte [{n}]: {dt / reps} ns/op"

/-! ## The packed `ByteArray`-carrier run-models (§10.6, densest tier)

`decodeByteArray`/`encodeByteArray` (`Codec.DecodeByteArray`/`Codec.EncodeByteArray`)
and the LEB128 `decodeVarint`/`encodeVarint` (`Codec.VarBinary`) are the *densest*
stdlib-carrier run-models (packed `uint8_t*`, no per-byte boxing), proved equal to
`varint : Iso Nat Bytes`. These legs measure the packed carrier and the varbinary
hot path against the `List` and `Array UInt8` baselines above. -/

/-- The `n` bytes as a packed `ByteArray` (`ByteArray.mk` over the reducible
`Array`, no per-byte box). -/
unsafe def byteArrayBytesOf (n : Nat) : ByteArray :=
  ByteArray.mk (arrayBytesOf n)

/-- The packed-carrier single-step decoder: `decodeByteArray Codec.byte a 0` peels
one byte in O(1) by index (the `lean_byte_array_get` primop). Confirms `[(1, 1)]`. -/
unsafe def benchDecodeByteArray (n : Nat) (reps : Nat) : IO Unit := do
  let a : ByteArray := byteArrayBytesOf n
  let (r, dt) ← timeBatch reps fun _ => decodeByteArray Codec.byte a 0
  let expected : List (UInt8 × Nat) := [(1, 1)]
  if r != expected then
    throw (IO.userError s!"decodeByteArray byte: expected [(1,1)], got {r}")
  IO.println s!"decodeByteArray byte [{n}]: {dt / reps} ns/op"

/-- The packed-accumulating single-step encoder: `encodeByteArray Codec.byte 1`
yields `some {data := #[1]}`. -/
unsafe def benchEncodeByteArray (reps : Nat) : IO Unit := do
  let (r, dt) ← timeBatch reps fun _ => encodeByteArray Codec.byte (1 : UInt8)
  match r with
  | some a =>
      if a.data.toList != [1] then throw (IO.userError "encodeByteArray byte: expected [1]")
  | none => throw (IO.userError "encodeByteArray byte: expected some")
  IO.println s!"encodeByteArray byte: {dt / reps} ns/op"

/-- The LEB128 varbinary roundtrip over the packed carrier: `decodeVarint
(encodeVarint n) 0` must recover `n` at the canonical consumed length. -/
unsafe def benchRoundtripVarint (reps : Nat) : IO Unit := do
  let (encoded, dt1) ← timeBatch reps fun _ => encodeVarint 12345678
  let (decoded, dt2) ← timeBatch reps fun _ => decodeVarint encoded 0
  match decoded with
  | [(n, j)] =>
      if n != 12345678 || j != (encoded.data.toList.length) then
        throw (IO.userError "roundtrip varint: mismatch")
  | _ => throw (IO.userError "roundtrip varint: expected one result")
  IO.println s!"encodeVarint 12345678: {dt1 / reps} ns/op"
  IO.println s!"decodeVarint 12345678: {dt2 / reps} ns/op"

/-- The packed-carrier full-consumption repetition decoder. -/
unsafe def benchDecodeFullByteArray (n : Nat) (reps : Nat) : IO Unit := do
  let a : ByteArray := byteArrayBytesOf n
  let (r, dt) ← timeBatch reps fun _ => decodeFullByteArray Codec.byte byte_consumesByte a 0
  match r with
  | some (xs, j) =>
      if xs.length != n || j != n then
        throw (IO.userError s!"decodeFullByteArray byte: expected ({n},{n}), got ({xs.length},{j})")
  | none => throw (IO.userError "decodeFullByteArray byte: expected some")
  IO.println s!"decodeFullByteArray byte [{n}]: {dt / reps} ns/op"

/-! ## The `@[extern]` C fast-path tier (the memchr-adjacent raw-byte loop)

`Codec.ExternFastPath` splices hand-written, GC-less C into the `ByteArray`
run-model's hot path. These legs drive the trusted primitives
(`byteSlice`/`encodeAppend`) and the routed fast paths
(`decodeFullByteArrayByte`/`encodeByteArrayBytes`) against the boxed
`ByteArray`/`List` baselines above — the head-to-head the design's acceptance
(within ~2× of a raw `memchr`/`memcpy` byte loop) is checked against. -/

open Codec.ExternFastPath

/-- The raw-byte slice loop: one `codec_byte_array_slice` call copies `a[0 .. n)`
into a fresh packed `ByteArray` (a `memcpy`-style C loop). This is the
memchr-adjacent *raw-byte throughput ceiling* the hot path is measured against. -/
unsafe def benchByteSlice (n : Nat) (reps : Nat) : IO Unit := do
  let a : ByteArray := byteArrayBytesOf n
  let (r, dt) ← timeBatch reps fun _ => byteSlice a 0
  if r.data.toList.length != n then
    throw (IO.userError s!"byteSlice: expected {n} bytes, got {r.data.toList.length}")
  IO.println s!"byteSlice byte [{n}]: {dt / reps} ns/op"

/-- The routed full-consumption decode: `decodeFullByteArrayByte a 0` — one
`codec_byte_array_slice` + one `List` materialization at the boundary, replacing
the `WellFounded.fix` per-byte recursion. -/
unsafe def benchDecodeFullByteArrayByte (n : Nat) (reps : Nat) : IO Unit := do
  let a : ByteArray := byteArrayBytesOf n
  let (r, dt) ← timeBatch reps fun _ => decodeFullByteArrayByte a 0
  match r with
  | some (xs, j) =>
      if xs.length != n || j != n then
        throw (IO.userError s!"decodeFullByteArrayByte: expected ({n},{n}), got ({xs.length},{j})")
  | none => throw (IO.userError "decodeFullByteArrayByte: expected some")
  IO.println s!"decodeFullByteArrayByte byte [{n}]: {dt / reps} ns/op"

/-- The encode accumulator: `encodeByteArrayBytes` appends `n` bytes into one
pre-grown packed `ByteArray` (amortized O(n) `push`), replacing the `List`-append
fold. -/
unsafe def benchEncodeByteArrayBytes (n : Nat) (reps : Nat) : IO Unit := do
  let xs : List UInt8 := bytesOf n
  let (r, dt) ← timeBatch reps fun _ => encodeByteArrayBytes xs
  if r.data.toList.length != n then
    throw (IO.userError s!"encodeByteArrayBytes: expected {n} bytes, got {r.data.toList.length}")
  IO.println s!"encodeByteArrayBytes byte [{n}]: {dt / reps} ns/op"

/-- The single-byte encode append primitive (`codec_encode_append`, the
amortized-O(1) `lean_byte_array_push` path). -/
unsafe def benchEncodeAppend (reps : Nat) : IO Unit := do
  let (r, dt) ← timeBatch reps fun _ => encodeAppend ByteArray.empty (1 : UInt8)
  if r.data.toList != [1] then throw (IO.userError "encodeAppend byte: expected [1]")
  IO.println s!"encodeAppend byte: {dt / reps} ns/op"

end Codec.Bench

open Codec.Bench in
/-- The benchmark entry point (top-level, so `lake`'s `lean_exe` generates the C
`main`). `n` (first CLI arg, default 1 MiB) drives the linear paths; `m` (second
CLI arg, default 8192) drives the quadratic `decodeRepeat`. -/
unsafe def main (args : List String) : IO Unit := do
  let n := (args.getD 0 "1048576").toNat!
  let m := (args.getD 1 "8192").toNat!
  let reps := 20
  IO.println s!"codec bench — linear n = {n} bytes, quadratic m = {m} bytes, reps = {reps}"
  -- Linear paths, scaled ×1/×2/×4 to show O(n) growth.
  for size in [n / 4, n / 2, n] do
    Codec.Bench.benchDecodeByte size reps
    Codec.Bench.benchEncodeRepeat size reps
    Codec.Bench.benchBufferTransport size reps
  -- Packed single-byte roundtrip (transport barrier, §10.4).
  Codec.Bench.benchRoundtripBuffer reps
  -- Quadratic backtracking "many" decoder (kept small, paper §4.4).
  Codec.Bench.benchDecodeRepeat m
  -- Tier A efficient repeaters: the §4.4/§10.6 target (order-of-magnitude faster than
  -- the all-prefix `decodeRepeat`), plus the fused single-step decoder.
  Codec.Bench.benchDecodeFull m reps
  Codec.Bench.benchDecodeRepeatFull m reps
  Codec.Bench.benchDecodeFast n reps
  -- Array-carrier run-models (§10.6, buffer tier): the array decoder/encoder/full
  -- repetition, each a proved-equal carrier swap over the `Array UInt8` run-model.
  Codec.Bench.benchDecodeArray n reps
  Codec.Bench.benchEncodeArray reps
  Codec.Bench.benchDecodeFullArray m reps
  -- Packed `ByteArray`-carrier run-models (§10.6, densest tier) + LEB128 varbinary.
  Codec.Bench.benchDecodeByteArray n reps
  Codec.Bench.benchEncodeByteArray reps
  Codec.Bench.benchDecodeFullByteArray m reps
  Codec.Bench.benchRoundtripVarint reps
  -- `@[extern]` C fast-path tier: the trusted raw-byte slice loop + the routed
  -- full-consumption decoder and encode accumulator (vs the boxed baselines above).
  for size in [n / 4, n / 2, n] do
    Codec.Bench.benchByteSlice size reps
    Codec.Bench.benchEncodeByteArrayBytes size reps
  Codec.Bench.benchDecodeFullByteArrayByte m reps
  Codec.Bench.benchEncodeAppend reps
  IO.println "done"
