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
  IO.println "done"
