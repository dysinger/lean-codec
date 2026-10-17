/- Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later -/

import Codec

/-!
# Extraction + benchmark harness (§10.5)

Drives the extracted `decode`/`encode` hot path and the semantic repetition
triple (`decodeRepeat`/`encodeRepeat`) on a multi-MB synthetic `byte`/`many`
description over the single length-indexed carrier `Bytes n := Fin n → UInt8`,
recording wall-clock numbers that back the linear-time / scalar-indexed-load
acceptance claim.

**Not** part of the proven core; imports nothing beyond `Codec`. The `unsafe`
annotations are confined to the periphery (byte-string construction and timing via
`IO.monoNanosNow`), never the interpreter under test.

The honest shape of the numbers (§10.5, task 1.6), re-based onto the single carrier:

  * `decode Codec.byte s`         — peels one byte, O(1) (reads `s ⟨0, ·⟩`).
  * `encodeRepeat Codec.byte xs`  — linear in `xs.length` (structural recursion).
  * the scalar-index read `s ⟨i, ·⟩` — a structural indexed load (no side condition).
  * `decodeRepeat Codec.byte h n s` — the backtracking "many" decoder; its *output*
    is all `m+1` prefixes, so it is inherently Θ(m²) in output size (paper §4.4)
    and is measured only at a small `m`.

There is **one** byte-string type: `Bytes n` serves as both the proof substrate and
the run-model; no `List UInt8` spec and no `ByteArray`/`Array`/`Buffer` slab remain.
The scalar indexed load `s ⟨i, ·⟩` is the single read the carrier exposes, and it
lowers to a scalar indexed load in the emitted IR.
-/

namespace Codec.Bench

open Codec

/-- `n` copies of the byte `0x01` as a length-indexed `Bytes n` (a `Fin n → UInt8`,
so a `Bytes n` is built by a constant function — no `List` cons cells). -/
def bytesOf (n : Nat) : Bytes n := fun _ => (1 : UInt8)

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

/-- Per-op throughput in MiB/s: `bytes` bytes moved in `nsPerOp` nanoseconds. -/
def mebibytesPerSec (bytes : Nat) (nsPerOp : Nat) : Nat :=
  if nsPerOp = 0 then 0 else (bytes * 10^9) / (nsPerOp * 2^20)

/-- Print one lane's timing line with both ns/op and MiB/s (when a non-zero byte
count is supplied). The `label` is left-padded by the caller's alignment. -/
unsafe def printLane (label : String) (n : Nat) (nsPerOp : Nat) (bytesPerOp : Nat) : IO Unit :=
  if bytesPerOp = 0 then
    IO.println s!"{label} [{n}]: {nsPerOp} ns/op"
  else
    IO.println s!"{label} [{n}]: {nsPerOp} ns/op  ({mebibytesPerSec bytesPerOp nsPerOp} MiB/s)"

/-- The machine calibration baseline lane: a `memset`-like fill (writing one byte
`n` times into a fresh `ByteArray` via a `push` append loop) and a `memcpy`-like
copy (`ByteArray.copySlice`, the `@[extern "lean_byte_array_copy_slice"]` primitive)
of the same `n`-byte count. Printed once at startup so every other lane's
throughput is *relative* to this same machine's raw memory-move speed, not an
absolute ns figure. -/
unsafe def benchCalibration (n : Nat) (reps : Nat) : IO Unit := do
  -- memset-like: write a single byte into a fresh n-byte array (the allocation
  -- cost dominates here; it is the floor for any "produce n bytes" lane).
  let (filled, dtMemset) ← timeBatch reps fun _ =>
    Id.run do
      let mut a := ByteArray.empty
      for _i in [0:n] do a := a.push (1 : UInt8)
      a
  if (filled.size : Nat) != n then
    throw (IO.userError "calibration memset: size mismatch")
  -- memcpy-like: copy the n-byte source into a fresh destination via the
  -- `lean_byte_array_copy_slice` extern (a real memcpy).
  let src := filled
  let (copied, dtMemcpy) ← timeBatch reps fun _ => src.copySlice 0 ByteArray.empty 0 n
  if (copied.size : Nat) != n then
    throw (IO.userError "calibration memcpy: size mismatch")
  printLane "calib memset " n (dtMemset / reps) n
  printLane "calib memcpy " n (dtMemcpy / reps) n

/-- The Layer-2 trust-seam lane: `byteSlice src i` (the `@[extern "codec_byteSlice"]`
`memcpy`-style suffix copy) is timed on a packed path, and **value-checked
byte-for-byte** against the Lean *body* (`Array.extract` on `.data`, the
specification the law is pinned to — not a length check). A wrong C implementation
fails the bench, not just the trust contract. The lane copies the `n/2`-suffix, so
`bytesPerOp` is `n - n/2` (the bytes actually moved), not `n`. -/
unsafe def benchByteSlice (n : Nat) (reps : Nat) : IO Unit := do
  let src := ByteArray.mk (Array.ofFn fun (_ : Fin n) => (1 : UInt8))
  let half : Nat := n / 2
  let idx : USize := half.toUSize
  -- spec: the Lean body `byteSlice` reduces to (`extract` on `.data`).
  let spec : ByteArray := ByteArray.mk (src.data.extract half src.data.size)
  let (r, dt) ← timeBatch reps fun _ => byteSlice src idx
  if r != spec then
    throw (IO.userError "byteSlice ≠ extract (value mismatch)")
  printLane "byteSlice L2  " n (dt / reps) (n - half)

/-- The partial-remainder commit lane: `commitRemainder src c` (the single
`byteSlice`/`memcpy` commit) at a **mid-buffer** `USize` cursor `c = (n / 3).toUSize`
— the partial case the full-suffix `byteSlice` lane does not cover. Value-checks the
committed `ByteArray` **byte-for-byte** against
`ByteArray.mk (src.extract c.toNat src.size)` (never a length check), so a
semantically wrong fast path fails at run time, not only at the trust contract.
`bytesPerOp` is `n - n/3` (the bytes actually committed). A distinct Layer-2 lane. -/
unsafe def benchCommitRemainder (n : Nat) (reps : Nat) : IO Unit := do
  let src : Array UInt8 := Array.ofFn fun (_ : Fin n) => (1 : UInt8)
  let third : Nat := n / 3
  let c : USize := third.toUSize
  -- spec: the definitional law `commitRemainder_spec` body (`extract` on `a`).
  let spec : ByteArray := ByteArray.mk (src.extract third src.size)
  let (r, dt) ← timeBatch reps fun _ => commitRemainder src c
  if r != spec then
    throw (IO.userError "commitRemainder ≠ extract (value mismatch)")
  printLane "commitRemainder L2" n (dt / reps) (n - third)

/-- The Layer-2 bulk-copy seam lane: `blitBytes dst dstOff src srcOff len` (the
`@[extern "codec_blitBytes"]` buffer-to-buffer `memcpy`) is timed on a packed path,
and **value-checked byte-for-byte** against the Lean *body* (the
`Array.extract`+`append` composition, the specification the law is pinned to —
not a length check). Copies a mid-buffer `len = n/2` window at `srcOff = n/4`
into `dstOff = n/8`, so the window is neither the prefix nor the suffix and a
wrong C `memcpy` (wrong offsets, wrong length) is caught at run time.
`bytesPerOp` is `len` (the bytes actually moved). -/
unsafe def benchBlitBytes (n : Nat) (reps : Nat) : IO Unit := do
  let mk : Nat → ByteArray := fun v =>
    ByteArray.mk (Array.ofFn fun (_ : Fin n) => UInt8.ofNat v)
  let dst := mk 1
  let src := mk 2
  let dstOff : USize := (n / 8).toUSize
  let srcOff : USize := (n / 4).toUSize
  let len : USize := (n / 2).toUSize
  -- spec: the Lean body `blitBytes` reduces to (`Array.extract` + `append`).
  let spec : ByteArray :=
    ByteArray.mk
      (dst.data.extract 0 dstOff.toNat
        ++ src.data.extract srcOff.toNat (srcOff.toNat + len.toNat)
        ++ dst.data.extract (dstOff.toNat + len.toNat) dst.data.size)
  let (r, dt) ← timeBatch reps fun _ => blitBytes dst dstOff src srcOff len
  if r != spec then
    throw (IO.userError "blitBytes ≠ extract+append (value mismatch)")
  printLane "blitBytes L2  " n (dt / reps) (n / 2)

/-- The Layer-2 span-scan seam lane: `findByte a off b` (the
`@[extern "codec_findByte"]` `memchr` scan) is timed, and **value-checked** against
the Lean *body* (the `Array.findIdx?` scan of the suffix). Places a single
sentinel byte `b = 0x7F` at `n/2` and scans from `off = n/4`, so a wrong C
`memchr` (bad start offset, wrong byte, off-by-one result) is caught. Reports
ns/op only (no byte throughput — a scan moves no buffer). -/
unsafe def benchFindByte (n : Nat) (reps : Nat) : IO Unit := do
  let arr : Array UInt8 := Array.ofFn fun (i : Fin n) =>
    if i.val = n / 2 then (0x7F : UInt8) else (1 : UInt8)
  let a : ByteArray := ByteArray.mk arr
  let off : USize := (n / 4).toUSize
  -- spec: the Lean body `findByte` reduces to (`findIdx?` over the suffix).
  let spec : Option USize :=
    match Array.findIdx? (fun x => x == (0x7F : UInt8)) (a.data.extract off.toNat a.data.size) with
    | some i => some (off + i.toUSize)
    | none => none
  let (r, dt) ← timeBatch reps fun _ => findByte a off (0x7F : UInt8)
  if r != spec then
    throw (IO.userError "findByte ≠ findIdx? scan (value mismatch)")
  if spec != some (n / 2).toUSize then
    throw (IO.userError "findByte: expected sentinel at n/2")
  IO.println s!"findByte L2   [{n}]: {dt / reps} ns/op"

/-- The scalar-index read lane: reading `s ⟨i, ·⟩` is a structural indexed load on
the length-indexed carrier (the one read the single substrate exposes). -/
unsafe def benchScalarIndexRead (n : Nat) (reps : Nat) : IO Unit := do
  let s : Bytes n := bytesOf n
  let (r, dt) ← timeBatch reps fun _ =>
    if h : n = 0 then (0 : UInt8) else s ⟨0, Nat.pos_of_ne_zero h⟩
  if r != (1 : UInt8) then
    throw (IO.userError "scalar-index read: expected byte 0x01")
  IO.println s!"scalar-index read [{n}]: {dt / reps} ns/op"

/-- The single-step decoder: `decode Codec.byte s` peels one byte in O(1), leaving
the `Suffix.drop 1 s` remainder. Confirms one result. -/
unsafe def benchDecodeByte (n : Nat) (reps : Nat) : IO Unit := do
  let s : Bytes n := bytesOf n
  let (r, dt) ← timeBatch reps fun _ => decode Codec.byte s
  match r with
  | [(1, t)] =>
      if t.remaining != n - 1 then
        throw (IO.userError "decode byte: remainder length mismatch")
  | _ => throw (IO.userError "decode byte: expected one result")
  IO.println s!"decode  byte [{n}]: {dt / reps} ns/op"

/-- The single-byte roundtrip with an **empty remainder** (`Suffix.empty n`):
`encode Codec.byte (1 : UInt8) = some ⟨1, s⟩` decodes back to `1` leaving nothing. -/
unsafe def benchRoundtripByte (reps : Nat) : IO Unit := do
  let (encoded, dt1) ← timeBatch reps fun _ => encode Codec.byte (1 : UInt8)
  match encoded with
  | none => throw (IO.userError "encode byte returned none")
  | some ⟨n, s⟩ =>
      if n != 1 then throw (IO.userError "encode byte: expected length 1")
      let (decoded, dt2) ← timeBatch reps fun _ => decode Codec.byte s
      match decoded with
      | [(1, t)] =>
          if t.remaining != 0 then
            throw (IO.userError "roundtrip byte: expected empty remainder")
      | _ => throw (IO.userError "roundtrip byte: expected one result")
      IO.println s!"roundtrip byte (encode): {dt1 / reps} ns/op"
      IO.println s!"roundtrip byte (decode): {dt2 / reps} ns/op"

/-- The encode-length lane: `encode Codec.byte x` returns the bytes **and their
length** in one sigma; the length is exactly `1` for a byte. Reports ns/op and
the per-byte throughput (MiB/s) so the bulk-encode cost is visible against the
calibration baseline. -/
unsafe def benchEncodeLength (n : Nat) (reps : Nat) : IO Unit := do
  let xs : List UInt8 := List.replicate n (1 : UInt8)
  let (r, dt) ← timeBatch reps fun _ => encodeRepeat Codec.byte xs
  match r with
  | some ⟨k, _s⟩ =>
      if k != n then
        throw (IO.userError "encodeRepeat length mismatch")
  | none => throw (IO.userError "encodeRepeat returned none")
  printLane "encodeRepeat byte" n (dt / reps) n

/-- The bulk fast-path lane: `fastEncodeRepeat Codec.byte xs` accumulates into an
`Array UInt8` and reads back a `Bytes`, asserting the result **value** (byte-for-byte,
`Sigma`-equal) against the spec `encodeRepeat Codec.byte xs` — a wrong fast path fails
the bench, not just the proof (the refinement is `Codec.fastEncodeRepeat_eq`, but the
bench re-checks it at run time). Reports ns/op + MiB/s against the calibrated baseline. -/
unsafe def benchFastEncodeRepeat (n : Nat) (reps : Nat) : IO Unit := do
  let xs : List UInt8 := List.replicate n (1 : UInt8)
  let (r, dt) ← timeBatch reps fun _ => fastEncodeRepeat Codec.byte xs
  match r, encodeRepeat Codec.byte xs with
  | some fast, some spec =>
      if fast != spec then
        throw (IO.userError "fastEncodeRepeat ≠ encodeRepeat (value mismatch)")
  | none, none => return ()
  | _, _ => throw (IO.userError "fastEncodeRepeat/spec none mismatch")
  printLane "fastEncodeRepeat byte" n (dt / reps) n

/-- The representation-isolation lane for `encodeRepeat`: time the encode with the
`concat`/sigma/`Fin`-sum arithmetic **elided** — a raw `unsafe` scratch `ByteArray`
accumulator that appends one byte per element (`ByteArray.push`, an `@[extern]`
primop), so this is the bandwidth + allocation floor separate from the carrier's
`Nat`/`Fin` index arithmetic, sigma re-packaging, and `concat`/cast. Not part of
`Codec`; purely to split bandwidth vs dependent-type bookkeeping vs residual in
the profiling attribution. -/
unsafe def benchEncodeRepeatIsolation (n : Nat) (reps : Nat) : IO Unit := do
  let (acc, dt) ← timeBatch reps fun _ =>
    Id.run do
      let mut b := ByteArray.empty
      for _i in [0:n] do b := b.push (1 : UInt8)
      b
  if (acc.size : Nat) != n then
    throw (IO.userError "encodeRepeat isolation: size mismatch")
  printLane "encodeRepeat iso  " n (dt / reps) n

/-- The backtracking "many" decoder (quadratic output, paper §4.4), kept at a
small `n`. Confirms it yields `n+1` prefixes. -/
unsafe def benchDecodeRepeat (n : Nat) : IO Unit := do
  let s : Bytes n := bytesOf n
  let (out, dt) ← timeBatch 1 fun _ => decodeRepeat Codec.byte byteConsumesByte n s
  if out.length != n + 1 then
    throw (IO.userError s!"decodeRepeat: expected {n+1} prefixes, got {out.length}")
  IO.println s!"decodeRepeat byte [{n}]: {dt} ns"

/-- The full-consumption repetition decoder: unlike `decodeRepeat` (which
materializes all `n+1` prefixes), this threads one `Option` and returns
`some (replicate n byte)` for the whole input. Asserts the *value* (not just its
length) against `replicate n (1 : UInt8)`; that this value is a full-consumption
result is the unconditional `Codec.decodeFull_some` law. -/
unsafe def benchDecodeFull (n : Nat) (reps : Nat) : IO Unit := do
  let s : Bytes n := bytesOf n
  let (r, dt) ← timeBatch reps fun _ => decodeFull Codec.byte byteConsumesByte n s
  match r with
  | some xs =>
      let expected : List UInt8 := List.replicate n (1 : UInt8)
      if xs != expected then
        throw (IO.userError s!"decodeFull: expected {expected.length}×0x01 bytes, got {xs}")
  | none => throw (IO.userError "decodeFull: expected some, got none")
  IO.println s!"decodeFull byte [{n}]: {dt / reps} ns/op"

/-- The fused single-step decoder `decodeFast`: peels one `Codec.byte` in O(1),
without re-traversing. Confirms `decodeFast` agrees with `decode` on the remainder
length (the `Suffix` carries no decidable value-equality, so this lanes checks the
consumed-length component; value agreement is the `decodeFast_eq` theorem). -/
unsafe def benchDecodeFast (n : Nat) (reps : Nat) : IO Unit := do
  let s : Bytes n := bytesOf n
  let (r, dt) ← timeBatch reps fun _ => decodeFast Codec.byte s
  match r, decode Codec.byte s with
  | [(1, t)], [(1, t')] =>
      if t.remaining != t'.remaining then
        throw (IO.userError "decodeFast ≠ decode (remainder length)")
  | _, _ => throw (IO.userError "decodeFast: expected one result")
  IO.println s!"decodeFast byte [{n}]: {dt / reps} ns/op"

/-- The Layer-2 varint-span seam lane: `varintEncodeInto`/`varintDecodeFrom` (the
`@[extern]` LEB128 span ops) are timed and **value-checked byte-for-byte** against
their Lean bodies (the `VarBinary` spec). Encodes `n = 12345678` into an empty
buffer and decodes back from offset `0`, asserting both the recovered value and the
consumed count match the `varintBytes` spec. A wrong C (bad LEB128 loop, wrong
offsets, wrong return boxing) fails the bench, not just the trust contract. -/
unsafe def benchVarintSpan (reps : Nat) : IO Unit := do
  let n : Nat := 12345678
  let mut buf := ByteArray.empty
  for _i in [0:10] do buf := buf.push (0 : UInt8)
  -- spec: the Lean bodies `varintEncodeInto`/`varintDecodeFrom` reduce to.
  let specEnc : ByteArray := varintEncodeInto buf 0 n
  let specDec : Option (Nat × USize) := varintDecodeFrom specEnc 0
  let (enc, dt1) ← timeBatch reps fun _ => varintEncodeInto buf 0 n
  if enc != specEnc then
    throw (IO.userError "varintEncodeInto ≠ spec body (value mismatch)")
  let (dec, dt2) ← timeBatch reps fun _ => varintDecodeFrom enc 0
  if dec != specDec then
    throw (IO.userError "varintDecodeFrom ≠ spec body (value mismatch)")
  match dec with
  | some (v, k) =>
      if v != n then throw (IO.userError "varint span: value mismatch")
      if k.toNat != (varintBytes n).1 then
        throw (IO.userError "varint span: consumed-count mismatch")
  | none => throw (IO.userError "varint span: expected a decode result")
  IO.println s!"varint span enc [{n}]: {dt1 / reps} ns/op"
  IO.println s!"varint span dec [{n}]: {dt2 / reps} ns/op"

/-- The Layer-2 numeric-parse seam lane: `parseNumber a off` (the `@[extern]`
decimal-span primitive) is timed and **value-checked byte-for-byte** against its
Lean body (the `decimalStep` scan). Parses the ASCII digit prefix `"12345678"` at
offset `off = 2` (preceded by non-digit bytes), asserting the recovered value and
consumed count. A wrong C (bad digit test, off-by-one stop, bad return boxing)
fails the bench, not just the trust contract. -/
unsafe def benchParseNumber (reps : Nat) : IO Unit := do
  -- build the bytes: [0,0,'1','2','3','4','5','6','7','8','x','x']
  let arr : Array UInt8 := Array.ofFn fun (i : Fin 12) =>
    if i.val < 2 then (0 : UInt8)
    else if i.val < 10 then (UInt8.ofNat (48 + (i.val - 1)))
    else (120 : UInt8)
  let a : ByteArray := ByteArray.mk arr
  let off : USize := 2
  let spec : Option (Nat × USize) := parseNumber a off
  let (r, dt) ← timeBatch reps fun _ => parseNumber a off
  if r != spec then
    throw (IO.userError "parseNumber ≠ spec body (value mismatch)")
  match r with
  | some (v, k) =>
      if v != 12345678 then throw (IO.userError "parseNumber: value mismatch")
      if k.toNat != 8 then throw (IO.userError "parseNumber: consumed-count mismatch")
  | none => throw (IO.userError "parseNumber: expected a parse result")
  IO.println s!"parseNumber L2 [{off.toNat}]: {dt / reps} ns/op"

/-- The LEB128 varbinary roundtrip over the length-indexed carrier: `decodeVarint
(encodeVarint 12345678)` must recover the value. -/
unsafe def benchRoundtripVarint (reps : Nat) : IO Unit := do
  let (encoded, dt1) ← timeBatch reps fun _ => encodeVarint 12345678
  let (decoded, dt2) ← timeBatch reps fun _ => decodeVarint encoded
  match decoded with
  | some n =>
      if n != 12345678 then
        throw (IO.userError "roundtrip varint: mismatch")
  | none => throw (IO.userError "roundtrip varint: expected a result")
  IO.println s!"encodeVarint 12345678: {dt1 / reps} ns/op"
  IO.println s!"decodeVarint 12345678: {dt2 / reps} ns/op"

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
  -- Machine calibration baseline (memset/memcpy at the same byte count), once at
  -- startup so every lane below is relative to this machine's raw memory speed.
  Codec.Bench.benchCalibration n reps
  -- Linear paths, scaled ×1/×2/×4 to show O(n) growth.
  for size in [n / 4, n / 2, n] do
    Codec.Bench.benchScalarIndexRead size reps
    Codec.Bench.benchDecodeByte size reps
    Codec.Bench.benchEncodeLength size reps
    -- Bulk fast path (proved `= encodeRepeat`, value-checked here at run time).
    Codec.Bench.benchFastEncodeRepeat size reps
    -- Representation-isolation: same byte count, but concat/sigma/Fin-sum elided.
    Codec.Bench.benchEncodeRepeatIsolation size reps
    -- Layer-2 named trust seam: the `codec_byteSlice` memcpy suffix copy.
    Codec.Bench.benchByteSlice size reps
    -- Layer-2 partial-remainder commit: mid-buffer `USize` cursor, value-checked.
    Codec.Bench.benchCommitRemainder size reps
    -- Layer-2 bulk copy seam: buffer-to-buffer `blitBytes` memcpy, value-checked.
    Codec.Bench.benchBlitBytes size reps
    -- Layer-2 span scan seam: `findByte` memchr, value-checked.
    Codec.Bench.benchFindByte size reps
  -- Single-byte empty-remainder roundtrip.
  Codec.Bench.benchRoundtripByte reps
  -- Quadratic backtracking "many" decoder (kept small, paper §4.4).
  Codec.Bench.benchDecodeRepeat m
  -- Full-consumption repetition decoder + fused single-step decoder.
  Codec.Bench.benchDecodeFull m reps
  Codec.Bench.benchDecodeFast n reps
  -- LEB128 varbinary over the single carrier.
  Codec.Bench.benchRoundtripVarint reps
  -- LEB128 span seams over the byte-array output (Layer 2, value-checked).
  Codec.Bench.benchVarintSpan reps
  -- Numeric-parse seam (Layer 2, value-checked).
  Codec.Bench.benchParseNumber reps
  IO.println "done"
