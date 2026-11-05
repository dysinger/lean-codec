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

/-- **Median of a list** (`Nat`), by insertion into a sorted list. Used instead of
rule 3's forbidden mean: the mean averages in the cold start, and the best-of
picks up zero-length spans from a coarse clock. -/
def medianOf (xs : List Nat) : Nat :=
  let sorted := xs.foldl (fun acc x =>
    let rec ins : List Nat → List Nat
      | [] => [x]
      | y :: ys => if x ≤ y then x :: y :: ys else y :: ins ys
    ins acc) []
  match sorted.length with
  | 0 => 0
  | k + 1 => sorted.getD (k / 2) 0

/-- **Burst lane: `bursts` back-to-back calls inside ONE timing window.**

Why this exists, and why it is not redundant with `benchRatio`. `benchRatio`
interleaves a same-size `memcpy` with the measured call so the two see the same
cache state — correct for a *ratio to `memcpy`*, and it is what every
throughput row uses. But the interleaving also **evicts the input between
calls**, so what it measures is cold-input (memory-bound) cost. That is a
legitimate number; it is not "the achievable pure-Lean per-element floor",
which is a *compute* claim.

Measured, same loop, same machine, `n = 4096`: **burst 6 ns/step vs interleaved
15 ns/step** — a 2.5× gap that is entirely cache state, and previously it was
misread as a floor. A burst also clears the other landmine: `IO.monoNanosNow`
granularity is ~41 ns, so timing one 4 KiB decode inside the interleaved lane is
timing noise, whereas a burst of `bursts` calls spans milliseconds.

**Both numbers are reported and neither is "the" answer.** Quote a *compute*
floor from a burst and a *throughput* figure from `benchRatio`; never mix them.

The input is varied per call (a different byte position each iteration), so the
loop is not invariant and cannot be hoisted.

**Two defects this lane used to carry, both fixed here (next-session task 1 and 2).**

1. *It reported the minimum of 5 rounds and called it "the floor".* The rounds are
   not independent — they differ only in how warm the cache is — so the minimum is
   systematically the **most favourable** round, not a floor. Measured, one
   invocation of the `idealCursor` loop at `n = 4096`: `25578, 22425, 15405,
   12742, 11931` ns/op. Every figure derived from the old lane was derived from the
   last of those. The lane now prints **min / median / max over every round**, plus
   the round count, so the decay is visible instead of hidden behind one endpoint.
2. *"Warm" was not L1-resident.* It rotated 8 buffers of `n` bytes, so the working
   set was `8n` = 32 KiB at `n = 4096` — past L1. It now rotates **`n` calls inside
   one buffer** instead, so the working set is the buffer itself.

Both variants are printed, because they answer different questions: `(burst@8buf)`
keeps the old shape (a caller streaming several buffers sees it), `(burst)` is the
L1-resident one (a compute floor). The **median is the figure to quote**; the min
and max are printed so the spread is on the record rather than behind one endpoint.

**What this lane cannot see.** Every row it is used on today (`idealCursor`,
`arrayRead`, `decodeFullArray` at `Codec.byte`) has exactly **one candidate per
cursor position**, so `decodeFullArraySearch` never iterates and the whole search
term is unpriced. A `k > 1` lane is the next session's task (see `AGENTS.md`). -/
unsafe def benchBurst {α : Type} [Inhabited α] (label : String) (n : Nat) (bursts : Nat)
    (mk : Nat → α) (measure : Nat → α → UInt8) : IO Unit := do
  -- Warm-up, so the first (cold) call is not part of any measured span.
  let _ := measure 0 (mk 0)
  -- **Variant A: one buffer, vary a byte *inside* it per call.** The input still
  -- changes (so the optimiser cannot hoist the loop) while the working set stays
  -- resident — `8n` bytes of rotation was past L1. The call index is passed to
  -- `measure` so it can vary its own input; that is a *contract*, not a
  -- convenience: a `measure` that ignores `j` makes the loop invariant and the
  -- optimiser reports clock granularity for real work.
  --
  -- **Variant B: the old 8-buffer rotation**, kept so the change is visible rather
  -- than silent, and printed *after* A so the L1-resident row is the headline.
  let rounds : Nat := 5
  let runVariant (tag : String) (buffers : Array α) : IO Unit := do
    let mut times : List Nat := []
    let mut sink : UInt8 := 0
    for i in [0:rounds] do
      let t0 ← IO.monoNanosNow
      for j in [0:bursts] do
        sink := sink * 31 + measure (i + j) buffers[(i + j) % buffers.size]!
      let t1 ← IO.monoNanosNow
      times := (t1 - t0) / bursts :: times
    if sink == 0 then
      throw (IO.userError s!"{label}: sink is zero — the measured work was elided")
    let mx := times.foldl max 0
    let mn := times.foldl min (times.headD 0)
    let md := medianOf times
    IO.println s!"{tag} [{n}]: min {mn}, median {md}, max {mx} ns/op over {times.length} rounds ({n} steps/burst)"
  -- A: the L1-resident variant — ONE buffer; the caller's `measure` varies its own
  -- input per call (see the docstring contract).
  runVariant s!"{label} (burst)      " #[mk 0]
  -- B: the old 8-buffer rotation (working set `8n`), for the record.
  runVariant s!"{label} (burst@8buf) " (Array.range 8 |>.map (fun j => mk j))

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
  -- blitBytes **aliasing**: the same buffer as both source and destination, with
  -- overlapping windows. The Lean body is `extract ++ extract ++ extract` over the
  -- *backing* `data`, so it reads the original bytes throughout; a C implementation
  -- that blits in place must therefore either be equivalent on this input or be
  -- caught here. This is the case where "matches the body" is not free.
  for (off, len) in [(0, 3), (1, 3), (2, 5)] do
    let dst := a5
    let got := blitBytes dst (off.toUSize) dst (off.toUSize) (len.toUSize)
    let n' := dst.data.size
    let dc := min (off.toUSize).toNat n'
    let sc := min (off.toUSize).toNat n'
    let lc := min (len.toUSize).toNat (min (n' - dc) (n' - sc))
    let spec : ByteArray :=
      ByteArray.mk (dst.data.extract 0 dc ++ dst.data.extract sc (sc + lc)
        ++ dst.data.extract (dc + lc) n')
    if got != spec then
      throw (IO.userError s!"blitBytes aliasing mismatch at off={off} len={len}")
  IO.println "seam aliasing OK (blitBytes src = dst, overlapping windows)"

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

/-! ## Value-check for `count`'s inductive step (`codec-audit-round-three` §1.1.3)

`Rel_count_succ` is proved, but a proof of a *decomposition* is exactly the shape
that can be vacuously true on a description that never relates anything. This lane
exercises the behaviour at two concrete `n` (`1` and `3`), so the step is not only
proved but observed: it decodes and re-encodes `count n Codec.byte` over a vector of
`n` bytes, and checks the result is the whole vector with nothing left over.

It deliberately does **not** re-derive the statement — it goes through
`decodeWhole`, the wire surface a consumer uses, so the check also covers the
composition of the step with the real decoder rather than only the `Rel` predicate. -/
unsafe def benchCountStep : IO Unit := do
  for m in [0, 2] do
    let k := m + 1
    let p : Codec UInt8 := Codec.byte
    -- `count k byte` relates a length-`k` list of `b`s to `k` copies of `b`.
    let b : UInt8 := 0x2A
    let xs : List UInt8 := List.replicate k b
    match encodeWhole (count k p) xs with
    | none => throw (IO.userError s!"count step [n={k}]: encodeWhole returned none")
    | some a =>
        if a.size != k then
          throw (IO.userError s!"count step [n={k}]: expected {k} bytes, got {a.size}")
        match decodeWhole (count k p) (countSuccConsumesByte p byteConsumesByte m) a with
        | none => throw (IO.userError s!"count step [n={k}]: decodeWhole returned none")
        | some results =>
            -- `count k byte` related exactly one value to this input, and
            -- whole-buffer decode enumerates every fully-consuming result, so the
            -- result list must be the singleton `[xs]`. Checking the list *and* its
            -- length is what makes this a statement about the step rather than
            -- about the first element the search happened to find.
            if results != [xs] then
              throw (IO.userError s!"count step [n={k}]: expected exactly one result [{k} values], got {results.length}")
            IO.println s!"count step [n={k}]: round trip OK (the step law holds at a concrete n)"
  -- The `n = 0` base case is `Rel_count_zero`; the step is claimed for `n + 1`, so
  -- `k = 0` would prove nothing here and is deliberately absent.

/-- **The wired fast surface (task 6.3)**: `decodeWhole` is the named entry point
readers are pointed at, and this lane asserts it is both *correct* and *the fast
path* — i.e. that wiring did not accidentally leave the surface on the slow route.
Both claims are checked, not assumed:

* the value is byte-for-byte what `decodeFull` returns, via the `decodeWhole_eq`
  law, so a wiring change that broke the delegate fails here;
* it is compared **against the specification decoder in the same run**, so if
  `decodeWhole` ever stopped delegating to the packed cursor the lane would report a
  slow number rather than hiding it. -/
unsafe def benchDecodeWhole (n : Nat) : IO Unit := do
  let s : Bytes n := bytesOf n
  let a : Array UInt8 := bytesToArray s
  match decodeWhole Codec.byte byteConsumesByte a with
  | some xs =>
      let expected : List UInt8 := List.replicate n (1 : UInt8)
      if xs != expected then
        throw (IO.userError s!"decodeWhole: expected {expected.length}×0x01 bytes, got length {xs.length}")
      -- `decodeWhole_eq`, at this input: the wired surface *is* the specification.
      -- Comparing against `decodeFull` (the slow spec decoder) is the check that
      -- would catch a wiring change that returned something else.
      if some xs != decodeFull Codec.byte byteConsumesByte (bytesToArray s).size
            (arrayToBytes (bytesToArray s)) then
        throw (IO.userError "decodeWhole ≠ decodeFull (the decodeWhole_eq law disagrees at run time)")
      IO.println s!"decodeWhole [{n}]: value + decodeWhole_eq OK"
  | none => throw (IO.userError "decodeWhole: expected some, got none")

/-- `decodeWholeBytes` is the specification-carrier entry point; it must agree with
`decodeWhole` on the same input (the packing transport is size-preserving and value-
preserving), and it exists so a caller holding a `Bytes n` has a wired path rather
than being told to pack by hand. -/
unsafe def benchDecodeWholeBytes (n : Nat) : IO Unit := do
  let s : Bytes n := bytesOf n
  let a : Array UInt8 := bytesToArray s
  if decodeWholeBytes Codec.byte byteConsumesByte s
      != decodeWhole Codec.byte byteConsumesByte a then
    throw (IO.userError "decodeWholeBytes ≠ decodeWhole on the packed readback")
  if (bytesToArray s).size != n then
    throw (IO.userError "bytesToArray_size disagrees at run time")
  IO.println s!"decodeWholeBytes [{n}]: agrees with decodeWhole, size preserved"

/-- The **packed cursor** decoder: `decodeFullArrayRoot` over an `Array UInt8`, with
the `Nat` consumed-count cursor. This is task 6.1b's construction, and the lane's job
is the same as `benchDecodeFullFast`'s: **assert correctness, not speed.**

The value is checked byte for byte, and checked **against `decodeFull` through the
proved bridge** `Codec.decodeFullArrayRoot_eq` — so a mismatch means the running code
disagrees with the theorem, not that a number moved. No MiB/s or ratio is printed:
6.4 owns the lane that defends the ratio, and it needs an idle machine with a
`memcpy` reference interleaved in the same samples (see `tasks.md` 6.1b's MEASUREMENT
RULES — every naive in-process timing here has produced a wrong number). -/
unsafe def benchDecodeFullArray (n : Nat) : IO Unit := do
  let s : Bytes n := bytesOf n
  let a : Array UInt8 := Array.mk (List.ofFn s)
  match decodeFullArrayRoot Codec.byte byteConsumesByte a with
  | some xs =>
      let expected : List UInt8 := List.replicate n (1 : UInt8)
      if xs != expected then
        throw (IO.userError s!"decodeFullArrayRoot: expected {expected.length}×0x01 bytes, got length {xs.length}")
      if some xs != decodeFull Codec.byte byteConsumesByte n s then
        throw (IO.userError "decodeFullArrayRoot ≠ decodeFull (the proved bridge disagrees at run time)")
      IO.println s!"decodeFullArray root [{n}]: value + bridge OK (unbenchmarked, see 6.1b/6.4)"
  | none => throw (IO.userError "decodeFullArrayRoot: expected some, got none")

/-! ## Ratio measurement (task 6.4)

This section exists because every earlier attempt to put a *number* on the decode
paths produced a wrong one. The five rules in `tasks.md` 6.1b MEASUREMENT RULES
are implemented literally here, and each is marked at the line that honours it.

The lanes print a **ratio to a same-run `memcpy`**, never an absolute MiB/s: an
absolute floor is machine-dependent and gets tuned down the first time CI is slow,
while the ratio is the property actually meant. The `memcpy` reference is taken
from `ByteArray.copySlice` — the `@[extern "lean_byte_array_copy_slice"]`
primitive, i.e. a real `memcpy` — at the same byte count in the same process.

Where the ledger says a figure is untrustworthy it means *this*: a naive lane
reports a literal `0 ns/op` (dead-code elimination), or reports 41 ns for a
1024-byte decode (loop hoisting), or makes `memcpy` look 200× slow (a mean over a
short batch averages in the allocator's ~125 µs cold start). -/

/-- **One timed sample of `reps` calls**: `f` runs `reps` times, each with a
*different* argument (`i * reps + j`), inside one bracketed window. The per-call
figure is the span divided by `reps`.

**Why a varying-argument loop, not a single call.** Both halves of rule 1 are
honoured: the call is not loop-invariant (the argument changes every iteration, and
the caller makes the *input* change with it), so it cannot be hoisted out; and a
single call per sample was measured to be **sunk past the clock reads entirely** —
this lane reported 750 ns for a decode that `benchDecodeFull` times at 407 ms in the
same process, and an earlier version reported the clock's 41 ns granularity. Binding
the result and force-reading it through `IO.eprintln` did *not* stop the sinking.
The loop shape is the one that survives: it is the same shape `timeBatch` uses, and
`timeBatch`'s numbers agree with `benchDecodeFull` to within noise.

`IO.monoNanosNow` (~41 ns granularity) brackets the whole batch, so the granularity
is amortised over `reps` calls rather than being the per-call error. -/
unsafe def timeOne (reps : Nat) (f : Nat → α) (i : Nat) : IO (α × Nat) := do
  let mut r : α := f (i * reps)
  let start ← IO.monoNanosNow
  for j in [0:reps] do
    r := f (i * reps + j)
  let stop ← IO.monoNanosNow
  return (r, stop - start)

/-- **Data-dependent sink** (rule 2). `bytesOf` is all `0x01`, so folding a result
to a sum or a length is a constant and the optimiser deletes the whole decode.
`a * 31 + b` mixes every byte's *value* into the result, so the fold cannot be
constant-folded away. The caller additionally asserts the sink is non-zero. -/
def sinkOfList (xs : List UInt8) : UInt8 :=
  xs.foldl (fun a b => a * 31 + b) 7

/-- **Interleaved ratio lane** (rules 1–5). For each of `samples` iterations: one
fresh call of the measured function and one fresh same-size `memcpy`, bracketed
individually, and both elapsed times pushed onto their lists. The ratio is
`median measured / median memcpy`, so a load spike that hits both sides cancels
out (rule 4) rather than turning into a ratio about the machine.

`label` names the path; `bytes` is the byte count per call (for ns/byte, which is
the figure that is *flat in n* when the cost is real per-byte work rather than
fixed overhead). -/
unsafe def benchRatio (label : String) (bytes : Nat) (samples : Nat)
    (reps : Nat) (mk : Nat → α) (measure : α → UInt8) : IO Unit := do
  let mut measured : List Nat := []
  let mut memc : List Nat := []
  let mut sink : UInt8 := 0
  -- **Pre-build the `memcpy` sources outside the timed window.** The reference is
  -- the *copy*, so the buffers it copies from must already exist; building them
  -- inside the window charges the reference for an `Array.ofFn` allocation the
  -- measured side pays for only where its own semantics require it. Measured: with
  -- construction inside, the 8192-byte `memcpy` reference read 110 µs (≈29 GiB/s
  -- of "memcpy" that was really allocation) and every ratio was ~500× too small.
  let sources : Array ByteArray :=
    (Array.range 8).map fun _ =>
      ByteArray.mk (Array.ofFn fun (_ : Fin (max bytes 1)) => (1 : UInt8))
  for i in [0:samples] do
    let (r, dt) ← timeOne reps (fun j => measure (mk j)) i
    -- Data-dependent read of the result: the decode cannot be elided.
    sink := sink * 31 + r
    -- The reference is `copySlice` exactly as `benchCalibration` measures it, so
    -- the ratio is against the same operation the rest of the file calls `memcpy`.
    let (_, dtc) ← timeOne reps
      (fun j => (sources[j % 8]!).copySlice 0 ByteArray.empty 0 bytes |>.size.toUInt8) i
    -- Per-call figures, so the ratio is call-for-call.
    measured := (dt / reps) :: measured
    memc := (dtc / reps) :: memc
  if sink == 0 then
    throw (IO.userError s!"{label}: sink is zero — the measured work was elided")
  let medM := medianOf measured
  let medC := medianOf memc
  -- A sub-100 ns `memcpy` is below `monoNanosNow`'s ~41 ns granularity, so the
  -- median can land on `0` and any ratio derived from it would be division by a
  -- clock artifact. **Report the measured side and skip the ratio** rather than
  -- either dividing by zero or aborting the process — a measurement lane that
  -- throws on a small `n` makes every lane after it unreachable, which is the
  -- defect 2.2(a) fixed for the seam checks and would be re-introduced here.
  if medC == 0 then
    IO.println s!"{label} [{bytes}]: {medM} ns ({medM / (max bytes 1)} ns/byte) — memcpy below clock granularity, no ratio"
    return
  let nsPerByte := if bytes == 0 then 0 else medM / bytes
  let ratio10 := (medM * 10) / medC
  -- **Read the ratio with its caveat.** The `memcpy` reference is taken in the
  -- same sample (rule 4), but a slow measured call (e.g. `decodeFull`, hundreds of
  -- ms) evicts the source from cache before the reference runs, so the reference is
  -- *cold* and the ratio is biased **low** — favourably, in the direction that
  -- flatters the code. The `ns/byte` figure is the number to quote; the ratio is
  -- order-of-magnitude information and is **not** comparable across rows measured
  -- at very different per-call costs. Cross-check any absolute figure against an
  -- independent lane (this file's `benchDecodeFull` times `decodeFull` directly).
  IO.println s!"{label} [{bytes}]: {medM} ns ({nsPerByte} ns/byte) vs memcpy {medC} ns = {ratio10 / 10}.{ratio10 % 10}x"

/-- **Task 6.7: the Layer-2 seam against the `List` transport, measured side by side.**

This lane exists because the decision in `Codec/Packed.lean` §"Task 6.7" is a
*measured* one — the seam is ~50–75× faster than the `List` transport and is still not
wired, because the equality proof needs an `Array.extract` readback that carries
`Classical.choice`. Keeping the comparison live means the trade-off stays checkable:
if a future toolchain makes the transport axiom-clean, this lane already shows what
wiring would buy, and if the seam regresses it shows that too.

Both sides are value-checked against each other, so a divergence fails the lane rather
than silently changing what "the same bytes" means. -/
unsafe def benchRemainderTransports (n : Nat) (samples : Nat) : IO Unit := do
  -- A pool of distinct buffers: the transport is a pure function of its input, so a
  -- single reused buffer lets the optimiser CSE the whole computation and reports a
  -- ratio about the optimiser rather than about the transport. Each sample takes a
  -- different buffer.
  let pool : List (Array UInt8) := (List.range 8).map fun j =>
    Array.ofFn fun (i : Fin n) =>
      if i.val = 0 then UInt8.ofNat (j % 7 + 1) else (1 : UInt8)
  let c := n / 2
  -- Value agreement first: a divergence makes every number below meaningless.
  let a0 := pool.head!
  if ByteArray.mk ((a0.toList.drop c).toArray) != commitRemainder a0 c.toUSize then
    throw (IO.userError "commitRemainder ≠ List transport (the two spellings disagree)")
  let mut lists : List Nat := []
  let mut seams : List Nat := []
  let mut sink : Nat := 0
  for i in [0:samples] do
    let a := pool.getD (i % 8) a0
    -- One fresh, separately-bracketed call each, interleaved (measurement rules 1/4).
    let (r1, t1) ← timeOne 1 (fun _ => (ByteArray.mk ((a.toList.drop c).toArray)).size) i
    sink := sink + r1
    let (r2, t2) ← timeOne 1 (fun _ => (commitRemainder a c.toUSize).size) i
    sink := sink + r2
    lists := t1 :: lists
    seams := t2 :: seams
  if sink == 0 then
    throw (IO.userError "transport lane: sink is zero — the work was elided")
  let medL := medianOf lists
  let medS := medianOf seams
  IO.println s!"transport List vs seam [{n}]: {medL} ns vs {medS} ns (seam {medL / (max medS 1)}x faster, values equal)"

/-- **The wired encode surface (task 6.5)**: `encodeWholeRepeat` accumulates through
`encodeArray` with no per-element `Bytes` intermediate, where `fastEncodeRepeat` still
calls `encode p x` per element and re-reads the result through `pushBytes`.

Two claims checked, not assumed:

* the **value** equals `encodeRepeat`'s, through `encodeWholeRepeat_eq` — so an
  accumulation bug in the wired fold fails here rather than silently emitting
  different bytes;
* the **round trip** closes: decoding the wired encoder's output with the wired
  decoder gives back the input list, which is the property a caller actually wants and
  which no single-side law states on its own. -/
unsafe def benchEncodeWhole (n : Nat) (reps : Nat) : IO Unit := do
  let xs : List UInt8 := List.replicate n (1 : UInt8)
  let (r, dt) ← timeBatch reps fun _ => encodeWholeRepeat Codec.byte xs
  match r with
  | some a =>
      -- `encodeWholeRepeat_eq`: the byte list is the specification's.
      let expected := (encodeRepeat Codec.byte xs).map (fun e : Sigma fun k => Bytes k =>
        List.ofFn e.2)
      if (some a.toList) != expected then
        throw (IO.userError "encodeWholeRepeat ≠ encodeRepeat (the law disagrees at run time)")
      -- the round trip through the wired decoder
      match decodeWhole Codec.byte byteConsumesByte a with
      | some ys =>
          if ys != xs then
            throw (IO.userError s!"encodeWhole/decodeWhole round trip: expected {n} elements, got {ys.length}")
      | none => throw (IO.userError "encodeWhole/decodeWhole round trip: decode returned none")
      printLane "encodeWhole (6.5)" n (dt / reps) n
  | none => throw (IO.userError "encodeWholeRepeat: expected some, got none")

/-- Ratio lane for the wired encoder against the same-run `memcpy`, so its cost is
read on the same scale as the decode lanes rather than a bare ns figure. -/
unsafe def benchEncodeWholeRatio (n : Nat) (samples : Nat) : IO Unit := do
  let xs : List UInt8 := List.replicate n (1 : UInt8)
  Codec.Bench.benchRatio "encodeWhole (6.5) " n samples 1
    (fun _ => xs)
    (fun ys => match encodeWholeRepeat Codec.byte ys with
               | some a => a.foldl (fun (x : UInt8) b => x * 31 + b) 7
               | none => 200)

/-- **The measured decode paths** (task 6.4). Everything measured is a *proved*
implementation of the same specification — `decodeFull` — so the numbers compare
implementation shapes, not correctness:

- `spec (Bytes)`: `decodeFull`, the `Bytes n`/`Suffix n` specification itself;
- `fast (Bytes)`: `decodeFullFastRoot`, the flat-cursor backtracking version;
- `packed root`: `decodeFullArrayRoot`, the `Array UInt8` + `Nat` cursor (6.1b);
- `cursor step`: one `decodeArray` step over `Array UInt8`, the per-step floor.

The last one is the interesting number: it isolates the *per-step* cost from the
search and the accumulator, so it separates "the compiler boxes arithmetic" from
"this algorithm allocates a `List` per step". -/
unsafe def benchDecodeShapes (n : Nat) (samples : Nat) (r : Nat) : IO Unit := do
  -- **Rule 1's real content: the *input* must differ per sample.** A buffer built
  -- once and closed over (`fun _ => s`) makes the measured closure loop-invariant
  -- and the optimiser hoists it out of the sample sequence — the lane then reports
  -- the clock's granularity (41 ns) for a multi-millisecond decode. Measured: the
  -- first version of this lane did exactly that. So every sample rebuilds the
  -- buffer with a different byte at index 0.
  let bytesAt (j : Nat) : Bytes n :=
    fun i => if i.val = 0 then UInt8.ofNat (j % 8 + 1) else (1 : UInt8)
  let arrayAt (j : Nat) : Array UInt8 := Array.mk (List.ofFn (bytesAt j))
  -- spec: `decodeFull` over `Bytes n`, sunk through its full-consumption value.
  Codec.Bench.benchRatio "decodeFull spec " n samples r
    bytesAt
    (fun s => match decodeFull Codec.byte byteConsumesByte n s with
              | some xs => sinkOfList xs
              | none => 200)
  -- fast: `decodeFullFastRoot` (still `Bytes n`/`Suffix n`, flat cursor).
  Codec.Bench.benchRatio "decodeFullFast " n samples r
    bytesAt
    (fun s => match decodeFullFastRoot Codec.byte byteConsumesByte s with
              | some xs => sinkOfList xs
              | none => 200)
  -- packed: `decodeFullArrayRoot` over `Array UInt8` + `Nat` cursor (6.1b).
  let dfaRoot (arr : Array UInt8) : UInt8 :=
    match decodeFullArrayRoot Codec.byte byteConsumesByte arr with
    | some xs => sinkOfList xs
    | none => 200
  -- **The burst at `n` exactly**, so the row can be divided by the `idealCursor`
  -- burst at the same `n` — the whole point of a "gap to the floor". The decoded
  -- input must differ per call or the decode hoists (measured: a sink-only
  -- perturbation left the loop invariant and the lane aborted on a zero sink). So
  -- each call decodes a **different `n`-byte window** of the same hot buffer,
  -- window start staggered by `j`. The decode path is unchanged — same
  -- `decodeFullArrayRoot`, same cursor, same result list — and the only per-call
  -- overhead is one `Array.extract`, i.e. a `memcpy` of `n/8` bytes: the honest
  -- cost of "a different input arrived". (An earlier attempt decoded a *subsampled
  -- copy* of the buffer so the allocation would be cheap; that shrinks the working
  -- set and turns a memory question into a different one, so it was withdrawn.)
  let rootWindow (j : Nat) (base : Array UInt8) : UInt8 :=
    if base.size = 0 then 200
    else
      let w := base.extract ((j * 8) % base.size) (((j * 8) % base.size) + (base.size / 8))
      match decodeFullArrayRoot Codec.byte byteConsumesByte w with
      | some xs => sinkOfList xs + UInt8.ofNat w.size
      | none => 200
  Codec.Bench.benchRatio "decodeFullArray " n samples r arrayAt dfaRoot
  Codec.Bench.benchBurst "decodeFullArray " (n / 8) 200 (fun _ => arrayAt 0) rootWindow
  -- the wired surface (6.3): must be the *same* number as `decodeFullArray`, since
  -- it delegates; a divergence here means the wiring left the fast path.
  Codec.Bench.benchRatio "decodeWhole (6.3) " n samples r
    arrayAt
    (fun arr => match decodeWhole Codec.byte byteConsumesByte arr with
                | some xs => sinkOfList xs
                | none => 200)
  -- floor: one raw cursor step (no search, no accumulator, no `Suffix`).
  Codec.Bench.benchRatio "decodeArray step" n samples r
    (fun j => (j % n, arrayAt j))
    (fun (j, arr) =>
      let cs := decodeArray Codec.byte arr j
      match cs with
      | (x, _) :: _ => x
      | [] => 200)
  -- **the three rows the README's table quotes but no lane printed (task 7.1).**
  -- Each isolates one named cost term, and each is the term the "× floor" column
  -- divides by, so leaving them unmeasured made the whole ratio narrative
  -- unsourced. `benchRatio` prints ns/op, so divide by `n` for ns/step.
  --
  -- `Array` indexed read alone: the memory floor, no codec logic at all. The burst
  -- reads a *different* index each call, which is what keeps a one-buffer burst
  -- un-hoistable.
  let readOne (p : Nat × Array UInt8) : UInt8 := p.2.getD p.1 0
  Codec.Bench.benchRatio "arrayRead " n samples r
    (fun j => (j % n, arrayAt j))
    readOne
  let readAt (j : Nat) (arr : Array UInt8) : UInt8 :=
    readOne (j % (max arr.size 1), arr)
  Codec.Bench.benchBurst "arrayRead " n 200 (fun _ => arrayAt 0) readAt
  -- the ideal `Id.run` cursor loop: `arr[k]` + `Nat` cursor, **no allocation**.
  -- Deliberately does NOT build an output array: a `push`-per-element version
  -- measures the floor *plus* n elements of array growth, which is not a floor and
  -- was previously (wrongly) quoted as one -- it read ~23 ns/step against this
  -- lane's ~6, i.e. the array growth was ~3/4 of the "floor". The result is sunk
  -- through a `Nat` accumulator so the loop cannot be elided.
  let idealLoop (arr : Array UInt8) : UInt8 :=
    let acc := Id.run do
      let mut acc : Nat := 0
      let mut k : Nat := 0
      while k < arr.size do
        acc := acc + (arr.getD k 0).toNat
        k := k + 1
      return acc
    UInt8.ofNat acc
  -- The L1-resident burst reuses ONE buffer, so its `measure` must vary its own
  -- input per call — `arrayAt j` was only varied by the 8-buffer rotation, and
  -- feeding a constant array to a burst makes the whole loop hoistable.
  let idealLoopAt (j : Nat) (arr : Array UInt8) : UInt8 :=
    -- Read a per-call offset *first*, so the loop's initial value (and therefore
    -- the whole result) depends on `j` and the optimiser cannot hoist it.
    let lift : Nat := (arr.getD (j % (max arr.size 1)) 0).toNat
    let acc := Id.run do
      let mut acc : Nat := lift
      let mut k : Nat := 0
      while k < arr.size do
        acc := acc + (arr.getD k 0).toNat
        k := k + 1
      return acc
    UInt8.ofNat acc
  Codec.Bench.benchRatio "idealCursor " n samples r arrayAt idealLoop
  -- **the same loop, burst-timed.** `benchRatio` interleaves a `memcpy` per sample,
  -- which evicts the 4 KiB input from L1, so its figure is *cold-input* cost. A
  -- burst measures compute with the input hot. Both are real and they answer
  -- different questions — a *floor* is a compute claim, so the floor comes from the
  -- burst; throughput comes from `benchRatio`. The burst reuses ONE buffer and
  -- varies an offset inside it per call: the working set stays resident, which the
  -- old 8-buffer rotation (`8n` = 32 KiB at `n` = 4096) did not.
  Codec.Bench.benchBurst "idealCursor " n 200 (fun _ => arrayAt 0) idealLoopAt
  -- **The `k > 1` lane (AGENTS.md's task): the search's per-CANDIDATE cost.**
  --
  -- Everything above is measured on `Codec.byte`, which has **exactly one** candidate
  -- per cursor position, so `decodeFullArraySearch` never iterates and the whole
  -- search term is unpriced — the "~10.5x gap to the floor" is the degenerate
  -- `k = 1` case, not a backtracking search. This lane supplies the missing `k`.
  --
  -- The codec: `satisfy (fun _ => true) | satisfy (fun _ => true)` — **two**
  -- candidates at every position, each consuming exactly one byte, each able to
  -- complete the buffer. That is the worst case for the search: the first candidate
  -- succeeds and the second is never tried on the *happy* path, but the candidate
  -- list is built (and its `PackedCand` proofs attached) with two entries instead of
  -- one, which is exactly the cost the `byte` lane cannot see. Measured against the
  -- same `n` as `decodeFullArray`, so the two rows subtract.
  let bothByte : Codec UInt8 := Codec.satisfy (fun _ => true)
  let twoCands : Codec UInt8 := Codec.alt bothByte bothByte
  let hTwo : ConsumesByte twoCands :=
    altConsumesByte _ _ (satisfyConsumesByte _) (satisfyConsumesByte _)
  -- **Assert the premise.** A lane that silently degenerates to `k = 1` would report
  -- a number that looks like a search measurement and is not one — the exact defect
  -- this lane exists to fix. So the candidate count is checked before timing.
  let probe : Array UInt8 := Array.mk (List.ofFn (bytesAt 0))
  let kAt0 : Nat := (packedCands twoCands hTwo probe 0 (Nat.zero_le _)).length
  let kB : Nat := (packedCands twoCands hTwo probe (probe.size / 2) (by omega)).length
  if kAt0 < 2 || kB < 2 then
    throw (IO.userError s!"k > 1 lane: premise failed — candidate counts were {kAt0} and {kB}, expected ≥ 2 at both cursors")
  let dfaTwo (arr : Array UInt8) : UInt8 :=
    match decodeFullArrayRoot twoCands hTwo arr with
    | some xs => sinkOfList xs
    | none => 200
  Codec.Bench.benchRatio "decodeFullArray k=2 " n samples r arrayAt dfaTwo
  let twoWindow (j : Nat) (base : Array UInt8) : UInt8 :=
    if base.size = 0 then 200
    else
      let w := base.extract ((j * 8) % base.size) (((j * 8) % base.size) + (base.size / 8))
      match decodeFullArrayRoot twoCands hTwo w with
      | some xs => sinkOfList xs + UInt8.ofNat w.size
      | none => 200
  Codec.Bench.benchBurst "decodeFullArray k=2 " (n / 8) 200 (fun _ => arrayAt 0) twoWindow
  -- **`packedCands` at ONE cursor position, `bytes := n` so the printed ns is
  -- per-step** -- because a decode step rebuilds the candidate list once. The
  -- original version built it once over the whole array and let `benchRatio` divide
  -- by `n`, which reported ~12 ns/step, *below* the per-step decode it is a
  -- component of: an arithmetic impossibility. `bytes` here is `n` because the row
  -- is quoted in the ns/**step** column and the ratio is per-call, not per-byte:
  -- one call is one step, and dividing by `n` is what manufactured the wrong figure.
  -- It is reported through `printLane` as **ns/op (one call)**, not through
  -- `benchRatio`, precisely because it is a per-call quantity and every attempt to
  -- express it per byte sourced the wrong figure twice: once by dividing a
  -- whole-array build by `n` (gave ~12 ns/"step", below the decode it composes),
  -- and once by passing `bytes := 1`, which made the memcpy reference a 1-byte copy
  -- and priced clock granularity. Measured directly: **~4.3 microseconds per call**,
  -- because `attach.map` rebuilds `PackedCand`'s *proof terms* -- that is the cost.
  do
    let arr := arrayAt 0
    let perStep (a : Array UInt8) : UInt8 :=
      match Codec.packedCands Codec.byte byteConsumesByte a 0 (Nat.zero_le _) with
      | [] => 0
      | cs => cs.length.toUInt8
    let (res, dt) ← timeOne r (fun _ => perStep arr) 0
    if res == 0 then
      throw (IO.userError "packedCands: sink is zero — the measured work was elided")
    printLane "packedCands (per step)" n (dt / r) 0
  -- **`packedCands` at `k = 2`, hot, under the burst lane.** The row above is a
  -- *cold* figure (it re-reads a 4 KiB array once), which is why it is 430–650 and
  -- why it cannot be a per-step term of the decode. This one is the attribution the
  -- `k > 1` lane needs: `packedCands` is rebuilt on every step, so if the `k = 2`
  -- search costs ~2× the `k = 1` search, the per-candidate cost of this function is
  -- where it shows. Bursted over ONE hot buffer with the cursor varied per call, so
  -- what it prints is compute, not first-touch.
  do
    let bothByte : Codec UInt8 := Codec.satisfy (fun _ => true)
    let twoCands : Codec UInt8 := Codec.alt bothByte bothByte
    let hTwo : ConsumesByte twoCands :=
      altConsumesByte _ _ (satisfyConsumesByte _) (satisfyConsumesByte _)
    let one : Codec UInt8 := bothByte
    let hOne : ConsumesByte one := satisfyConsumesByte _
    let arr := arrayAt 0
    -- **The cursor is hoisted OUT of the timed closure, and the premise asserts it.**
    -- The first version of this lane computed `j % (a.size + 1)` and its bound proof
    -- (`hbnd j a`) *inside* the measured closure, with `j` varying per call: it
    -- priced a `Nat` modulus plus a proof-term construction, not `packedCands`, and
    -- reported 75/95 ns — which contradicted the decode it is a component of (75
    -- alone is more than the whole 27.5 ns/step `k = 1` decode step). Fixed here.
    --
    -- The cursor is therefore fixed at a mid-buffer position and the per-call
    -- variation lives in the *sink seed* only, which cannot be elided because the
    -- fold consumes the candidate values.
    let c : Nat := arr.size / 2
    let hc : c ≤ arr.size := by omega
    -- The sink must depend on the candidate *values*, not just their length: the
    -- length is a constant (1 or 2) and a length-only sink is folded away — that is
    -- the trap that made the older "3 ns/call" reading and that aborted this lane's
    -- own `k = 2` variant on a zero sink.
    let cands1 (j : Nat) (_ : Array UInt8) : UInt8 :=
      let cs := Codec.packedCands one hOne arr c hc
      cs.foldl (fun (s : UInt8) x => s * 31 + x.val.1) ((j % 251).toUInt8 + 1)
    let cands2 (j : Nat) (_ : Array UInt8) : UInt8 :=
      let cs := Codec.packedCands twoCands hTwo arr c hc
      cs.foldl (fun (s : UInt8) x => s * 31 + x.val.1) ((j % 251).toUInt8 + 1)
    -- premise: one candidate for `k=1`, two for `k=2`, at the same cursor
    let k1 : Nat := (Codec.packedCands one hOne arr c hc).length
    let k2 : Nat := (Codec.packedCands twoCands hTwo arr c hc).length
    if k1 != 1 || k2 != 2 then
      throw (IO.userError s!"packedCands k lane: premise failed — got {k1} and {k2} candidates, expected 1 and 2")
    if c >= arr.size then
      throw (IO.userError "packedCands k lane: premise failed — cursor is at the end of the buffer")
    -- **The arithmetic consistency gate.** `packedCands` is *one component* of one
    -- decode step, and it is rebuilt on every step, so a standalone measurement of it
    -- cannot exceed the whole decode step that contains it. This lane exists because
    -- that constraint was violated and nobody checked: the old row read 3 ns/call
    -- (a length-only sink, folded away) and the first version of this lane read 75,
    -- while a *standalone* probe of the same codec costs ~800 ns — so both numbers
    -- were artifacts of a partially-folded closure, and neither was stated against
    -- the constraint that would have caught it.
    --
    -- Comparing across lanes is unsound here (different codecs, different cache
    -- state), so the gate is on what this lane can prove on its own: the sink must
    -- move. A folded closure returns the same value for every call.
    let probe1 := (List.range 12).map (fun j => cands1 j arr)
    let probe2 := (List.range 12).map (fun j => cands2 j arr)
    if (probe1.eraseDups).length < 2 then
      throw (IO.userError "packedCands k=1 lane: the sink is invariant across calls — the closure was folded, this is not a measurement")
    if (probe2.eraseDups).length < 2 then
      throw (IO.userError "packedCands k=2 lane: the sink is invariant across calls — the closure was folded, this is not a measurement")
    -- **Vary the BUFFER, not just the seed.** With a fixed buffer and the per-call
    -- variation carried only by the seed, the closure's *data* arguments are
    -- loop-invariant, so the optimiser keeps most of the computation and the row is
    -- not a measurement. Rotating the buffer is what defeats it. (A `lean --run`
    -- probe of this same call reads ~850–1050 ns/call — that is the *interpreter*,
    -- not the compiled cost; `lake build bench` compiles to C. The two are not
    -- comparable and only the compiled row below may be quoted.)
    -- The 8 buffers must differ **at the cursor**, not only at byte 0: the candidate
    -- `packedCands` produces is `(byte at cursor, cursor+1)`, so buffers differing
    -- only at index 0 yield the *same* candidate and an invariant sink. That is a
    -- property of the codec, not of the optimiser, and it is why the gate must be
    -- satisfied by real data variation rather than by a seed.
    let pool : Array (Array UInt8) :=
      (Array.range 8).map fun k =>
        Array.mk (List.ofFn (fun (i : Fin 4096) =>
          UInt8.ofNat ((k * 7 + i.val) % 251)))
    let bufs : Array (Array UInt8) := pool
    let cOf (a : Array UInt8) : Nat := a.size / 2
    have hcOf : ∀ (a : Array UInt8), cOf a ≤ a.size := by
      intro a; unfold cOf; omega
    let c : Nat := cOf arr
    let cands1 (j : Nat) (_ : Array UInt8) : UInt8 :=
      let a := bufs[j % 8]!
      let cs := Codec.packedCands one hOne a (cOf a) (hcOf a)
      cs.foldl (fun (s : UInt8) x => s * 31 + x.val.1 + x.val.2.toUInt8) cs.length.toUInt8
    let cands2 (j : Nat) (_ : Array UInt8) : UInt8 :=
      let a := bufs[j % 8]!
      let cs := Codec.packedCands twoCands hTwo a (cOf a) (hcOf a)
      cs.foldl (fun (s : UInt8) x => s * 31 + x.val.1 + x.val.2.toUInt8) cs.length.toUInt8
    -- premise: one candidate for `k=1`, two for `k=2`, at the same cursor
    let k1 : Nat := (Codec.packedCands one hOne arr c (hcOf arr)).length
    let k2 : Nat := (Codec.packedCands twoCands hTwo arr c (hcOf arr)).length
    if k1 != 1 || k2 != 2 then
      throw (IO.userError s!"packedCands k lane: premise failed — got {k1} and {k2} candidates, expected 1 and 2")
    -- **The invariance gate.** A partially-folded closure returns a *constant*; if
    -- the sink cannot be made to differ across buffers, the lane is not measuring.
    if (List.range 8).all (fun j => cands1 j arr == cands1 0 arr) then
      throw (IO.userError "packedCands k=1 lane: sink invariant across buffers — the closure was folded, this is not a measurement")
    if (List.range 8).all (fun j => cands2 j arr == cands2 0 arr) then
      throw (IO.userError "packedCands k=2 lane: sink invariant across buffers — the closure was folded, this is not a measurement")
    Codec.Bench.benchBurst "packedCands k=1 " n 200 (fun _ => arr) cands1
    Codec.Bench.benchBurst "packedCands k=2 " n 200 (fun _ => arr) cands2

/-! ## The hand-written C reference parser (benchmark only, **not** Layer 2)

`AGENTS.md` records that every ratio in this repository is against the repo's own
pure-Lean floor, and that the honest reference for a per-element codec is a
**hand-written C parser over the same bytes** — not `memcpy`, which moves a byte
and does no per-element work. This section is that reference.

Three properties make it a *reference* rather than a flattering straw man:

* **Same job.** `decodeWhole Codec.byte` decodes a whole `n`-byte buffer as many
  `Codec.byte`: one value per byte, consuming the buffer exactly. The C side
  allocates an `n`-element value array, fills it from the input, and returns it —
  deliberately not an output-free checksum loop, which would skip the allocation
  the Lean side pays for and flatter C by exactly the term under discussion.
* **Value-checked at run time** against the Lean decoder, so a divergence fails
  the lane instead of silently changing what "the same bytes" means.
* **Not part of the library.** No `@[extern]` in `Codec/`; this declaration lives
  in the bench, `Codec/CRef.c` is linked only into `bench`, and the library stays
  pure Lean. It is excluded from the `#print axioms` gate by construction — it is
  not a proof, it is a yardstick. -/

/-- The C reference parser: decode `a` as many `Codec.byte`, one value per byte.
`@[extern]` swaps the emitted call for `codec_cRefByteMany` in `Codec/CRef.c`; the
Lean body below is what the *kernel* sees, and it is the specification the C must
match (the same arrangement as the Layer-2 seams, but with no trust claim: nothing
proven depends on it). -/
@[extern "codec_cRefByteMany"]
opaque cRefByteMany (a : ByteArray) : Option (Array UInt8)

/-- **The honest C-vs-Lean figure**, with the value check that makes it meaningful.

The lane reports C's ns/step next to the Lean decoder's, and refuses to print if
the two disagree — a C reference that computes something *else* faster is not a
reference. The C call is timed through the same `benchBurst` machinery (median of
rounds, one L1-resident buffer, input varied per call) so the two numbers are
produced the same way. -/
unsafe def benchCReference (n : Nat) : IO Unit := do
  let bytesAt (j : Nat) : Bytes n :=
    fun i => if i.val = 0 then UInt8.ofNat (j % 8 + 1) else (1 : UInt8)
  let arrayAt (j : Nat) : Array UInt8 := Array.mk (List.ofFn (bytesAt j))
  -- **Value check first.** The C must decode to the same list the Lean decoder
  -- returns, for several inputs, before any number from it is trustworthy.
  for j in [0:4] do
    let a := arrayAt j
    let ba := ByteArray.mk a
    let c := cRefByteMany ba
    let l := decodeWhole Codec.byte byteConsumesByte a
    match c, l with
    | some ca, some xs =>
        if ca.toList != xs then
          throw (IO.userError s!"C reference disagrees with decodeWhole at input {j}: {ca.size} vs {xs.length} values")
    | none, none => return ()
    | _, _ => throw (IO.userError "C reference and decodeWhole disagree on Some/None")
  -- Same input shape, same burst machinery, both sides.
  -- Both lanes decode a **different `n/8`-byte window** of the same hot buffer per
  -- call, so neither closure is loop-invariant (a fixed input is folded away — the
  -- trap that cost two of this repo's withdrawn figures) and both pay the same
  -- `Array.extract` per call. `n` in the label is the decoded byte count.
  let window (j : Nat) (a : Array UInt8) : Array UInt8 :=
    if a.size = 0 then a
    else
      let off := (j * 8) % a.size
      a.extract off (off + (a.size / 8))
  let cLane (j : Nat) (a : Array UInt8) : UInt8 :=
    let w := window j a
    match cRefByteMany (ByteArray.mk w) with
    | some out => sinkOfList out.toList + UInt8.ofNat w.size
    | none => 200
  let lLane (j : Nat) (a : Array UInt8) : UInt8 :=
    let w := window j a
    match decodeWhole Codec.byte byteConsumesByte w with
    | some xs => sinkOfList xs + UInt8.ofNat w.size
    | none => 200
  Codec.Bench.benchBurst "C reference (hand-written)" (n / 8) 200 (fun _ => arrayAt 0) cLane
  Codec.Bench.benchBurst "Lean decodeWhole       " (n / 8) 200 (fun _ => arrayAt 0) lLane

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
  -- **Cap the lanes that are super-linear or allocation-dominated so a default
  -- run terminates.** `n = 1 MiB` was the default and the run did not finish in
  -- 500 s (measured 2026-11-03): `benchEncodeRepeat` allocates a `ByteArray` per
  -- byte and runs at 20 reps across a ×4 scale, and `decodeRepeat`/`decodeFull`
  -- are quadratic in the input. A bench whose default invocation never reaches
  -- its last lanes is the defect R2.2 records, so the caps below are not a
  -- convenience: they are what makes the evidence reachable. Pass explicit `n`/`m`
  -- to override; the ratio lane caps itself at 64 KiB regardless.
  let nCapped := min n 65536
  let mCapped := min m 4096
  IO.println s!"codec bench — requested n = {n}, m = {m}; using n = {nCapped}, m = {mCapped}, reps = {reps}"
  -- Layer-2 seam proof: the only runtime C↔Lean evidence, and it needs no scaling
  -- parameter. It runs FIRST, before any lane whose cost or success depends on
  -- `n`/`m`, so it is reached on every invocation — including a default run.
  Codec.Bench.benchSeamBoundaries
  -- `count`'s inductive step, value-checked at two concrete `n` (§1.1.3). It needs no
  -- `n`/`m` scale parameter — it builds its own 1- and 3-byte vectors — so it runs
  -- here, alongside the other scale-free lanes, and is reached on every invocation.
  Codec.Bench.benchCountStep
  -- Machine calibration baseline (memset/memcpy at the same byte count), once at
  -- startup so every lane below is relative to this machine's raw memory speed.
  Codec.Bench.benchCalibration nCapped reps
  -- Linear paths, scaled ×1/×2/×4 to show O(n) growth.
  for size in [nCapped / 4, nCapped / 2, nCapped] do
    Codec.Bench.benchScalarIndexRead size reps
    Codec.Bench.benchDecodeByte size reps
    Codec.Bench.benchEncodeLength size reps
    -- Bulk fast path (proved `= encodeRepeat`, value-checked here at run time).
    Codec.Bench.benchFastEncodeRepeat size reps
    if size = 1 then
      -- `size = 1` is not evidence of anything: every lane below is one `Nat`
      -- allocation away from a `0 ns/op` reading, and `benchDecodeByte`'s own
      -- check (`t.remaining = n - 1`) is `0 - 1 = 0` at `n = 1`, so it cannot
      -- distinguish a real decode from a wrong one. Previously the whole
      -- ×1/×4 scale factor also reached `size = 0` at the default `n`, where a
      -- `Bytes 0` read has no byte at all — the lane's value check then aborted
      -- the process and silently killed every later lane (R2.2(b)), which is why
      -- the seam checks above no longer run last.
      continue
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
  Codec.Bench.benchDecodeRepeat mCapped
  -- Full-consumption repetition decoder + fused single-step decoder.
  Codec.Bench.benchDecodeFull mCapped reps
  -- The fast full-consumption decoder: value- AND bridge-checked, ratio-printing.
  Codec.Bench.benchDecodeFullFast mCapped
  Codec.Bench.benchDecodeFullArray mCapped
  -- The wired fast surface (6.3): correct, and it *is* the packed path.
  Codec.Bench.benchDecodeWhole mCapped
  Codec.Bench.benchDecodeWholeBytes mCapped
  -- The wired encode surface (6.5): correct, round-trips, and measured.
  Codec.Bench.benchEncodeWhole mCapped reps
  Codec.Bench.benchEncodeWholeRatio mCapped 15
  -- Task 6.7: the seam-vs-List-transport comparison behind the "not wired" decision.
  -- its own size: the `List` transport's cost is dominated by re-materializing the
  -- *whole* backing list, so the comparison is only meaningful on a large buffer.
  Codec.Bench.benchRemainderTransports (max mCapped 65536) 9
  Codec.Bench.benchDecodeFast nCapped reps
  -- Task 6.4: the ratio lanes. Run LAST, so a slow or aborting lane above cannot
  -- silently hide them, and read their output next to `uptime` (rule 5).
  --
  -- `min m 65536`: `decodeFull` (the specification shape) is super-linear — it
  -- re-walks the whole suffix per step, so a 1 MiB run takes tens of minutes and
  -- would make the lane useless in a default invocation. The ratio is flat in `n`
  -- once the per-step cost dominates, so capping the input costs nothing and keeps
  -- a default run terminating.
  -- `reps = 3` per sample: `decodeFull` (the spec shape) is super-linear, so a
  -- large rep count would dominate the run. The per-call figure is `dt / reps`.
  Codec.Bench.benchDecodeShapes mCapped 15 3
  -- **The hand-written C reference** (`AGENTS.md` names it as the honest yardstick:
  -- a `memcpy` ratio for a per-element codec is a category error). Value-checked
  -- against `decodeWhole` before it prints anything.
  Codec.Bench.benchCReference mCapped
  -- TEMPORARY: ISO 8601 timestamp (AST-shaped) speed test.
  Codec.Bench.benchIso8601Encode reps
  Codec.Bench.benchIso8601Decode reps
  IO.println "done"
