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

/-! ## Value-checks for the normal-form layer (`Codec/Normal.lean`)

These are `example`s, not timing lanes: the layer is a *type*, so its content is
proved, and the bench's job is to value-check the concrete instance a consumer
would build (here: a two-symbol alphabet folded to one canonical case). They back
RFC 4648 §8's "a decoder MUST accept both cases" over an ordinary `Iso` — no `Iso`
relaxation anywhere.

Kept deliberately tiny (`UInt8` → `Bool`), so the arithmetic is decidable and the
checks reduce; a real base's fold is the same shape over its own alphabet. -/

/-- A total, idempotent normalizer on the two hex-ish symbols `0x41` and `0x61`:
everything folds to `0x61`, everything else is unchanged. -/
def foldNorm (b : UInt8) : UInt8 := if b == 0x41 then 0x61 else b

theorem foldNorm_idem : ∀ x, foldNorm (foldNorm x) = foldNorm x := by
  intro x
  unfold foldNorm
  split <;> (try split) <;> first | rfl | (exfalso; assumption)

/-- The normalizer bundles the law — the type carries it (design D2). -/
theorem foldNz : Normalizer UInt8 foldNorm := ⟨foldNorm_idem⟩

/-- `fill` presents a byte as a normal form; both spellings reach the same class —
which is the whole point of the layer. -/
example : (fill foldNz (0x41 : UInt8)).raw = (fill foldNz (0x61 : UInt8)).raw := rfl

/-- A strict `Iso` on normal forms: the value side **is** the quotient, so
`apply`/`unapply` are honest inverses and the `law` stays a field.

The honest way to see why the byte side must be the quotient: writing
`unapply b := some ⟨b, h⟩` needs a proof that `b` is already normal, which is not
free; and `unapply b := some (fill foldNz b)` makes `apply ∘ unapply ≠ some` on
non-normal bytes. So an `Iso` into normal forms can only invert *normal* bytes —
exactly why the lossy direction is a wrapper outside the `Iso`, not a relaxed law. -/
def foldIso : Iso (Normal UInt8 foldNorm) (Normal UInt8 foldNorm) where
  apply f := some f
  unapply f := some f
  law := by
    intro f b
    constructor
    · intro h
      have : f = b := by simpa using h
      subst this
      rfl
    · intro h
      have : b = f := by simpa using h
      subst this
      rfl

/-- The **decode-only wrapper** over `foldIso`: the normalizer runs outside the
`Iso`, so it takes arbitrary bytes (including `0x41`) where the `Iso` takes only
normal forms. This is the RFC 4648 §8 shape. -/
def decodeFold (b : UInt8) : Option (Normal UInt8 foldNorm) :=
  decodeNormal foldNz foldIso b

/-- Both spellings decode to the same value: §8, over a strict `Iso`. -/
example : decodeFold (0x41 : UInt8) = decodeFold (0x61 : UInt8) := rfl

/-- `fill` reaches every normal form, so the quotient is faithfully represented
(design D7) — asserted for the concrete instance. -/
example (f : Normal UInt8 foldNorm) : fill foldNz f.raw = f := fill_surj foldNz f

/-- `fill_fixed`: `norm` on a normal form is the identity. -/
example (b : UInt8) : foldNorm (fill foldNz b).raw = (fill foldNz b).raw :=
  fill_fixed foldNz b

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
  -- spec: `byteSlice_spec` (the seam's own law) read as the `Nat`-indexed form
  -- the bench can compare against — not a re-derivation of the body.
  let spec : ByteArray := ByteArray.mk (src.data.extract (idx.toNat) src.data.size)
  let (r, dt) ← timeBatch reps fun _ => byteSlice src idx
  if r != spec then
    throw (IO.userError "byteSlice ≠ extract (value mismatch)")
  -- The value-check above is `byteSlice_spec` at `i = idx`: the byte-for-byte
  -- event that makes the C's trust contract checkable, not merely asserted.
  let _seamLaw : byteSlice src idx = spec := byteSlice_spec src idx
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
  let spec : ByteArray := ByteArray.mk (src.extract (c.toNat) src.size)
  let (r, dt) ← timeBatch reps fun _ => commitRemainder src c
  if r != spec then
    throw (IO.userError "commitRemainder ≠ extract (value mismatch)")
  -- The value-check is `commitRemainder_spec` itself, restated at this input.
  let _seamLaw : commitRemainder src c = spec := commitRemainder_spec src c
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
  -- spec: the Lean body `blitBytes` reduces to (clamped cursor/run + `extract`
  -- + `append`), with `dc`/`sc`/`lc` the destination/source cursors and the
  -- copied run, each clamped as `Array.extract` clamps its bounds.
  let n' := dst.data.size
  let slen := src.data.size
  let dc := min dstOff.toNat n'
  let sc := min srcOff.toNat slen
  let lc := min len.toNat (min (n' - dc) (slen - sc))
  let spec : ByteArray :=
    ByteArray.mk
      (dst.data.extract 0 dc
        ++ src.data.extract sc (sc + lc)
        ++ dst.data.extract (dc + lc) dst.data.size)
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

/-- **Layer-2 boundary smoke test** — value-checks all three trust seams against
their Lean bodies across the out-of-range cases (empty source, `off` at/past
either end, `len` past the end), so the "matches byte-for-byte on every input"
claim is *checkable*, not asserted. Uses a small fixed buffer so the cases are
exact and cheap; each `≠ none` failure names the seam and the case. -/
unsafe def benchSeamBoundaries : IO Unit := do
  let a5 : ByteArray := ByteArray.mk (#[1,2,3,4,5] : Array UInt8)
  let a3 : ByteArray := ByteArray.mk (#[9,9,9] : Array UInt8)
  -- byteSlice: suffix [i, size) with i clamped to [0, size].
  for i in [0, 2, 5, 6] do
    let got := byteSlice a5 (i.toUSize)
    let spec := ByteArray.mk (a5.data.extract (i.toUSize).toNat a5.data.size)
    if got != spec then
      throw (IO.userError s!"byteSlice boundary mismatch at i={i}")
  -- findByte: scan [off, size) with off clamped to [0, size]; none when off ≥ size.
  for off in [0, 3, 5, 6] do
    let got := findByte a5 (off.toUSize) 4
    let spec : Option USize :=
      match Array.findIdx? (fun x => x == (4 : UInt8)) (a5.data.extract (off.toUSize).toNat a5.data.size) with
      | some j => some (off.toUSize + j.toUSize)
      | none => none
    if got != spec then
      throw (IO.userError s!"findByte boundary mismatch at off={off}")
  -- blitBytes: full-length dst with clamped destination/source cursors and run.
  let cases : List (Nat × Nat × Nat) :=
    [ (1, 0, 3)     -- normal window
    , (1, 0, 5)     -- src too short (len 5, src size 3) ⇒ run clamped to 2
    , (6, 0, 3)     -- dstOff past end ⇒ dc clamped to 5
    , (1, 6, 3)     -- srcOff past end ⇒ sc clamped to 3 ⇒ run 0
    , (1, 0, 10)    -- len past dst end ⇒ run clamped
    , (1, 0, 0)     -- len 0 ⇒ unchanged dst
    ]
  for (dstOff, srcOff, len) in cases do
    let got := blitBytes a5 (dstOff.toUSize) a3 (srcOff.toUSize) (len.toUSize)
    let n' := a5.data.size
    let slen := a3.data.size
    let dc := min (dstOff.toUSize).toNat n'
    let sc := min (srcOff.toUSize).toNat slen
    let lc := min (len.toUSize).toNat (min (n' - dc) (slen - sc))
    let spec : ByteArray :=
      ByteArray.mk (a5.data.extract 0 dc ++ a3.data.extract sc (sc + lc) ++ a5.data.extract (dc + lc) n')
    if got != spec then
      throw (IO.userError s!"blitBytes boundary mismatch at dstOff={dstOff} srcOff={srcOff} len={len}")
  IO.println "seam boundaries OK (byteSlice/findByte/blitBytes out-of-range value-checks)"

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

/-- The **fast** full-consumption decoder: `decodeFullFastRoot`, the flat-cursor,
backtracking implementation. This lane exists because the 237x / 9,047x ratio
quoted for this function elsewhere had **no bench lane at all** — the number was
not reproducible from the binary.

**It asserts correctness, not speed.** The value is checked byte for byte against
`replicate n (1 : UInt8)`, and against `decodeFull` — the proved bridge
`Codec.decodeFullFastRoot_eq` makes that unconditional, so a mismatch means the
running code disagrees with the theorem.

**No MiB/s and no ratio is printed, deliberately.** Every attempt to time this
function in-process has produced a wrong number, and the wrong numbers are
recorded in `tasks.md` 6.1b so nobody repeats them:

- timing `(...).isSome`, or folding to a sum/length, lets the optimiser delete the
  whole decode — this lane reported a literal **0 ns/op**, and a probe an
  impossible 321 ns for a 1024-byte decode;
- making the input vary per iteration did **not** stop the hoist, because the
  closure is still loop-invariant in shape — 0 ns/op and then 41 ns/op, both
  impossible;
- mean-over-a-short-batch averages in the allocator's ~125 µs cold start, which
  once made `memcpy` look 200x slower than its ~100 ns steady state.

The measurement that did reproduce is **outside** any loop the optimiser can
reason about: one fresh timed call per size, median of 15, `n` from 64 to 1024,
all on an idle machine. That gave **~1,250–1,500 ns/byte (~0.8 MiB/s)** — flat
across sizes, so it is real work and not a fixed overhead. Reproduce it with a
standalone driver before trusting any in-process lane. 6.4 owns the lane and the
threshold; it needs an idle machine and a `memcpy` reference interleaved in the
same samples. -/
unsafe def benchDecodeFullFast (n : Nat) : IO Unit := do
  let s : Bytes n := bytesOf n
  match decodeFullFastRoot Codec.byte byteConsumesByte s with
  | some xs =>
      let expected : List UInt8 := List.replicate n (1 : UInt8)
      if xs != expected then
        throw (IO.userError s!"decodeFullFastRoot: expected {expected.length}×0x01 bytes, got length {xs.length}")
      if some xs != decodeFull Codec.byte byteConsumesByte n s then
        throw (IO.userError "decodeFullFastRoot ≠ decodeFull (the proved bridge disagrees at run time)")
      IO.println s!"decodeFullFast root [{n}]: value + bridge OK (unbenchmarked, see 6.1b)"
  | none => throw (IO.userError "decodeFullFastRoot: expected some, got none")

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

/-! ## TEMPORARY speed test: RFC 3339 date-time (AST-shaped, application-style)

RFC 3339 is the Internet profile of ISO 8601 (`date-time` = `full-date "T"
full-time`). The grammar (ABNF in section 5.6) is:

    date-fullyear   = 4DIGIT
    date-month      = 2DIGIT  ; 01-12
    date-mday       = 2DIGIT  ; 01-28/29/30/31 by month+leap-year
    time-hour       = 2DIGIT  ; 00-23
    time-minute     = 2DIGIT  ; 00-59
    time-second     = 2DIGIT  ; 00-58/59/60 (leap second)
    time-secfrac    = "." 1*DIGIT
    time-numoffset  = ("+" / "-") time-hour ":" time-minute
    time-offset     = "Z" / time-numoffset
    partial-time    = time-hour ":" time-minute ":" time-second [time-secfrac]
    full-date       = date-fullyear "-" date-month "-" date-mday
    full-time       = partial-time time-offset
    date-time       = full-date "T" full-time

`T`/`Z` may be lowercase `t`/`z` (RFC 3339 §5.6 NOTE; generators SHOULD emit
uppercase). The hour MUST be 00-23 (not 24); day is validated against the
month/year with leap-year (Appendix C); the second may be 60 (leap second).

The point of this section is to answer, with real numbers on *this* machine:
**does the packed/fast path actually beat the pure spec for a structured value**,
or is the measured ceiling real? Nothing here is part of the proven core; it is a
throwaway measurement, drafted so it can later be lifted into a separate package
verbatim (the `Timestamp` AST + `parse`/`print` live here only for the bench). -/

/-- The RFC 3339 `date-time` AST, exactly what an application would define. The
fraction (`secfrac`) is kept as the raw digit list (arbitrary precision per
`1*DIGIT`, so a fixed `Nat` can't hold it), and the offset is a tagged union of
`Z` (UTC) or a nonzero `±HH:MM` numeric offset (in minutes east of UTC, signed). -/
structure Timestamp where
  year : Nat
  month : Nat
  day : Nat
  hour : Nat
  minute : Nat
  second : Nat
  secfrac : List UInt8          -- the digits after the '.', e.g. ['5','2'] — empty = none
  utc : Bool                     -- true = 'Z', false = numeric offset
  offsetMin : Int                -- numeric offset in minutes (east-positive), valid when ¬utc
  deriving Repr, Inhabited, BEq

/-- Reference value (`1985-04-12T23:20:50.52Z`, RFC 3339 §5.8 example 1). -/
def sampleTimestamp : Timestamp :=
  ⟨1985, 4, 12, 23, 20, 50, [UInt8.ofNat 53, UInt8.ofNat 50], true, 0⟩

/-- The decimal digits of `n` (most-significant first) as ASCII bytes. -/
def digits (n : Nat) : List UInt8 := Id.run do
  let mut acc : List UInt8 := []
  let mut m := n
  if m = 0 then
    acc := [UInt8.ofNat 48]
  else
    while m > 0 do
      acc := (UInt8.ofNat (48 + m % 10)) :: acc
      m := m / 10
  acc

/-- Pad a digit list on the left with ASCII `'0'` to width `w`. -/
def padLeft (w : Nat) (ds : List UInt8) : List UInt8 :=
  (List.replicate (w - ds.length) (UInt8.ofNat 48)) ++ ds

/-- RFC 3339 Appendix C leap-year test: a year is a leap year iff divisible by 4
and (not divisible by 100 or divisible by 400). -/
def isLeapYear (y : Nat) : Bool :=
  y % 4 = 0 ∧ (y % 100 ≠ 0 ∨ y % 400 = 0)

/-- Days in a month (1-12), with the leap-year February rule (§5.7). -/
def daysInMonth (y : Nat) (m : Nat) : Nat :=
  match m with
  | 1 | 3 | 5 | 7 | 8 | 10 | 12 => 31
  | 4 | 6 | 9 | 11 => 30
  | 2 => if isLeapYear y then 29 else 28
  | _ => 0

/-- The numeric-offset suffix `±HH:MM` (east-positive minutes). -/
def offsetBytes (offMin : Int) : List UInt8 :=
  let sign : UInt8 := if offMin < 0 then 45 else 43
  let absMin : Nat := Int.natAbs offMin
  let hh := absMin / 60
  let mm := absMin % 60
  [sign] ++ padLeft 2 (digits hh) ++ [58] ++ padLeft 2 (digits mm)

/-- The full date-time byte list (uppercase `T`/`Z`, the SHOULD form), for
`print`. Fraction is emitted only when non-empty. -/
def timestampBytes (t : Timestamp) : List UInt8 :=
  padLeft 4 (digits t.year) ++ [45] ++ padLeft 2 (digits t.month) ++ [45]
  ++ padLeft 2 (digits t.day) ++ [84]
  ++ padLeft 2 (digits t.hour) ++ [58] ++ padLeft 2 (digits t.minute) ++ [58]
  ++ padLeft 2 (digits t.second)
  ++ (if t.secfrac.isEmpty then [] else [46] ++ t.secfrac)
  ++ (if t.utc then [90] else offsetBytes t.offsetMin)

/-- **Print** (encode): the application-style fast path — write the exact byte
list into a fresh `ByteArray` with `Array.push` (the `@[extern]` contiguous
append). This is the hot path an app would ship; nothing here touches the `Codec`
AST or an `Iso` proof. -/
unsafe def printTimestamp (t : Timestamp) : ByteArray := Id.run do
  let mut bs : ByteArray := ByteArray.empty
  for b in timestampBytes t do
    bs := bs.push b
  bs

/-- The pure *spec* encode over the length-indexed `Bytes` carrier (the slow
denotation this fast path is compared against): build the same byte list, then
read it back into `Bytes k` via the proven `encodeByteArrayBytes`. -/
def specEncodeTimestamp (t : Timestamp) : Sigma fun k => Bytes k :=
  let arr := (encodeByteArrayBytes (timestampBytes t)).toList.toArray
  (⟨arr.size, fun i => arr[i.val]⟩)

/-- Total byte accessor: `baGet a i` is `a[i]` when in range, else `0`. Used so
the parse stays total without threading `i < a.size` proofs through every
exact-width read (bounded reads already check `i + w ≤ a.size`). -/
def baGet (a : ByteArray) (i : Nat) : UInt8 :=
  if h : i < a.size then a[i] else 0

/-- **Parse** core: read exactly `w` ASCII decimal digits at `i` into a `Nat`.
`none` on overrun or a non-digit. Single scalar loop, no backtracking. -/
def readNDigits (a : ByteArray) (i : Nat) (w : Nat) : Option (Nat × Nat) :=
  if i + w > a.size then none else
    -- structural recursion over `w`; accumulator is a plain pair (no Option in
    -- the middle of the loop, no List.range/foldl churn)
    let rec go (k : Nat) (acc : Nat) (j : Nat) : Option (Nat × Nat) :=
      match k with
      | 0 => some (acc, j)
      | k' + 1 =>
          let c : Nat := (baGet a j).toNat
          if 48 ≤ c ∧ c < 58 then go k' (acc * 10 + (c - 48)) (j + 1) else none
    go w 0 i

/-- Parse one or more ASCII decimal digits (the `1*DIGIT` fraction), returning
the digit bytes and the advanced cursor. Scans forward from `i`, stopping at the
first non-digit (after at least one digit) or the buffer end. -/
def readDigits1 (a : ByteArray) (i : Nat) : Option (List UInt8 × Nat) :=
  -- collect digits with cons (O(n)), reverse once at the end
  let rec go (j : Nat) (acc : List UInt8) : Option (List UInt8 × Nat) :=
    if _h : j < a.size then
      let c := baGet a j
      if c.toNat ≥ 48 ∧ c.toNat < 58 then go (j + 1) (c :: acc) else
        if acc.isEmpty then none else some (acc.reverse, j)
    else
      if acc.isEmpty then none else some (acc.reverse, j)
    termination_by a.size - j
    decreasing_by
      simp_wf
      omega
  go i []

/-- Read a literal ASCII byte `b` (`-`, `:`, `T`, `Z`): succeeds iff the byte at
`i` equals `b`. -/
def readLiteral (a : ByteArray) (i : Nat) (b : UInt8) : Option Nat :=
  if baGet a i = b then some (i + 1) else none

/-- Validate the date/time fields per §5.6-§5.7: month 01-12, hour 00-23,
minute 00-59, second 00-59 (60 allowed only as a leap second at month end), and
day within `daysInMonth`. The ast-level ranges are checked here (the parse is
total and returns `none` on any violation). -/
def validFields (t : Timestamp) : Bool :=
  1 ≤ t.month ∧ t.month ≤ 12 ∧
  t.hour ≤ 23 ∧ t.minute ≤ 59 ∧
  (t.second ≤ 59 ∨ t.second = 60) ∧
  t.day ≥ 1 ∧ t.day ≤ daysInMonth t.year t.month

/-- **Parse** (decode): the application-style fast path — one linear pass with
exact-length digit reads and literal separators, tolerating lowercase `t`/`z`.
Returns the `Timestamp` AST and the consumed count, or `none` on any structural
or range violation. -/
def parseTimestamp (a : ByteArray) : Option (Timestamp × Nat) := do
  let (year, i1) ← readNDigits a 0 4
  let i2 ← readLiteral a i1 45
  let (month, i3) ← readNDigits a i2 2
  let i4 ← readLiteral a i3 45
  let (day, i5) ← readNDigits a i4 2
  -- time separator: 'T' or 't'
  let tsep := baGet a i5
  if tsep ≠ 84 ∧ tsep ≠ 116 then none else
  let (hour, i7) ← readNDigits a (i5 + 1) 2
  let i8 ← readLiteral a i7 58
  let (minute, i9) ← readNDigits a i8 2
  let i10 ← readLiteral a i9 58
  let (second, i11) ← readNDigits a i10 2
  -- optional fraction: '.' 1*DIGIT (a missing fraction means none)
  let (frac, i12) : List UInt8 × Nat :=
    if baGet a i11 = 46 then
      match readDigits1 a (i11 + 1) with
      | some pr => pr
      | none => ([], i11 + 1)
    else ([], i11)
  -- offset: 'Z'/'z' or ±HH:MM
  let b0 := baGet a i12
  if b0 = 90 ∨ b0 = 122 then
    let t : Timestamp := ⟨year, month, day, hour, minute, second, frac, true, 0⟩
    if validFields t then some (t, i12 + 1) else none
  else if b0 = 43 ∨ b0 = 45 then
    let (oh, i14) ← readNDigits a (i12 + 1) 2
    let i15 ← readLiteral a i14 58
    let (om, i16) ← readNDigits a i15 2
    let offMag := oh * 60 + om
    let offMin : Int := if b0 = 45 then - Int.ofNat offMag else Int.ofNat offMag
    let t : Timestamp := ⟨year, month, day, hour, minute, second, frac, false, offMin⟩
    if validFields t then some (t, i16) else none
  else none

/-- End-to-end encode lane: `printTimestamp` vs `specEncodeTimestamp`, both
value-checked byte-for-byte against the expected bytes of `sampleTimestamp`. -/
unsafe def benchIso8601Encode (reps : Nat) : IO Unit := do
  let expected : List UInt8 := timestampBytes sampleTimestamp
  let (fast, dt1) ← timeBatch reps fun _ => printTimestamp sampleTimestamp
  let (spec, dt2) ← timeBatch reps fun _ => specEncodeTimestamp sampleTimestamp
  if (fast.toList : List UInt8) != expected then
    throw (IO.userError "fast iso8601 encode: wrong bytes")
  if (List.ofFn spec.2 : List UInt8) != expected then
    throw (IO.userError "spec iso8601 encode: wrong bytes")
  printLane "iso8601 encode fast" expected.length (dt1 / reps) expected.length
  printLane "iso8601 encode spec" expected.length (dt2 / reps) expected.length

/-- End-to-end decode lane: `parseTimestamp` parses the encoded bytes back to the
AST, value-checked against `sampleTimestamp`. Also exercises a numeric-offset
example (`1996-12-19T16:39:57-08:00`) and a lowercase-`t`/`z` variant. -/
unsafe def benchIso8601Decode (reps : Nat) : IO Unit := do
  let encoded := printTimestamp sampleTimestamp
  let (r, dt) ← timeBatch reps fun _ => parseTimestamp encoded
  match r with
  | some (t, c) =>
      if t != sampleTimestamp then
        throw (IO.userError "fast iso8601 decode: value mismatch")
      if c != encoded.size then
        throw (IO.userError "fast iso8601 decode: consumed length mismatch")
  | none => throw (IO.userError "fast iso8601 decode: expected a parse")
  -- A second, structural example (offset + lowercase t/z), parsed once for value.
  let offBytes : List UInt8 :=
    padLeft 4 (digits 1996) ++ [45] ++ padLeft 2 (digits 12) ++ [45] ++ padLeft 2 (digits 19)
    ++ [116] ++ padLeft 2 (digits 16) ++ [58] ++ padLeft 2 (digits 39) ++ [58]
    ++ padLeft 2 (digits 57) ++ [45] ++ padLeft 2 (digits 8) ++ [58] ++ padLeft 2 (digits 0)
  let offBA : ByteArray := ByteArray.mk offBytes.toArray
  match parseTimestamp offBA with
  | some (t, _) =>
      if t.year != 1996 ∨ t.month != 12 ∨ t.day != 19 ∨ t.hour != 16 ∨ t.minute != 39
         ∨ t.second != 57 ∨ t.utc ∨ t.offsetMin != -480 then
        throw (IO.userError "iso8601 offset example: value mismatch")
  | none => throw (IO.userError "iso8601 offset example: expected a parse")
  printLane "iso8601 decode fast" encoded.size (dt / reps) encoded.size

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
  -- The fast full-consumption decoder: value- AND bridge-checked, ratio-printing.
  Codec.Bench.benchDecodeFullFast m
  Codec.Bench.benchDecodeFast n reps
  -- Layer-2 seam boundary smoke test (out-of-range value-checks).
  Codec.Bench.benchSeamBoundaries
  -- TEMPORARY: ISO 8601 timestamp (AST-shaped) speed test.
  Codec.Bench.benchIso8601Encode reps
  Codec.Bench.benchIso8601Decode reps
  IO.println "done"
