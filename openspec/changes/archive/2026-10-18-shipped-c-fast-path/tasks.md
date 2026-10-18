# Tasks

> **ABANDONED (this session).** This change was **misguided**. Its central plan —
> ship per-format specialized decoders/encoders (WAV, protobuf, JSON, PNG, QR) and
> per-format C seams (zlib `deflate`/`inflate`, numeric-parse) — runs directly
> counter to the settled direction: **all codecs are pure Lean**; the only C is a
> small fixed set of **generic bulk byte-movement seams** (`byteSlice`/`blitBytes`/
> `findByte`/`commitRemainder` = `memcpy`/`memchr`); there is **no per-format C and
> no C that parses digits/numbers/fields**. The generic seams this change _did_ ship
> (`blitBytes`, `findByte`) are fine and stay; the per-format half is abandoned. The
> format-oriented seams it added (`VarintFast`, `NumParse`) and the in-core `VarBinary`
> were since **removed** from core (they belong in downstream packages). The one still-live
> item — `decodeArray_unambiguous_value` (Task 3.1's outstanding half) — is carried forward
> independently, not under this change.
>
> Archived rather than completed; spec deltas NOT synced (the per-format requirements
> they add are themselves part of the misguided scope).

> The plan: keep the pure `Bytes n` interpreter as the slow spec, and ship a fast C
> surface — `@[extern]` seams (each `byteSlice`-shaped: reducible Lean body + trusted
> C) plus per-format specialized decoders/encoders, all proved `[propext, Quot.sound]`-equal
> to the spec or named as runtime-only trust. The review's strategic conclusion is the
> anchor: do **not** try to make the generic interpreter fast; make the shipped C fast and
> prove _agreement with the slow spec_. Start with WAV + protobuf (clearest `memcpy`-shaped
> hot paths), then generalize.

> **Status (this session): Task 1 (bulk copy + scan seams) is DONE (3/13).**
> `blitBytes`/`findByte` landed in `Codec/ByteSlice.lean` + `.c`, both `USize`-indexed with
> reducible `Array`-spelled bodies; `blitBytes_spec` is axiom-free (`rfl`), `findByte_spec` is
> `[propext]` (`rfl`). Both bench lanes value-check byte-for-byte against their Lean bodies.
> `[measured]` (128 KiB): `blitBytes L2` 23225 MiB/s (vs `calib memcpy` 30033), `findByte L2` 697
> ns/op. **Session win:** the `findByte` C first returned `lean_box(idx+1)` for `some (idx : USize)`
> — wrong; the value-check caught it (returned `none`), and it was fixed to the correct
> `lean_alloc_ctor(1,1,0)` + `lean_ctor_set(_, 0, lean_box_usize(idx))` (verified against the IR's own
> `some (off+i)` construction). This is recorded in the `lean` skill (§ Append).
> **Next session (Task 2):** the varint-span (2.1) + numeric-parse (2.2) + zlib (2.3) seams — same
> shape, new `.c` files. **Known latent gotcha:** the lakefile `byteSliceO` target's
> `buildLeanO oFile (Job.pure srcFile)` does **not** rebuild the `.o` on a `.c` mtime change in
> _incremental_ dev (needs `rm .lake/build/ByteSlice.o`, or a clean `nix build .#bench`); the new
> `.c` targets in Task 2 (varint/numparse/zlib) must use the same `target … (pkg) : FilePath` shape
> and be git-tracked before `nix build` sees them. Decide up-front whether to consolidate all seams
> into one `.c`/object (simpler incremental story) or one target per seam (cleaner isolation).

## 1. The bulk copy + scan seams (generalize `byteSlice`)

- [x] 1.1 Add `blitBytes (dst : ByteArray) (dstOff : USize) (src : ByteArray) (srcOff : USize)
(len : USize) : ByteArray` — a buffer-to-buffer `memcpy`, Lean body the reducible
      `Array.extract`+`append` composition, C symbol a single `memcpy`, in `Codec/ByteSlice.lean`
      (+ `.c`). `USize`-indexed so its body is `rfl`-clean.
- [x] 1.2 Add `findByte (a : ByteArray) (off : USize) (b : UInt8) : Option USize` — a span
      scan via `memchr`, Lean body a `List`/`Array` `find?` reference, C one `memchr`. Document
      both contracts verbatim (the `ByteSlice.lean` posture), excluded from the axiom gate.
- [x] 1.3 Prove `blitBytes_spec`/`findByte_spec` (Lean body = spec; any index web stays
      `[propext, Quot.sound]`-only), and value-check both in a bench lane byte-for-byte.

## 2. Varint span + numeric parse + zlib seams

- [x] 2.1 Add `varintEncodeInto`/`varintDecodeFrom` span ops (LEB128 into/from
      `lean_sarray_cptr`), Lean body reducible-equal to the existing `VarBinary`; C a scalar
      `size_t`+`uint8_t` loop (no bignum cursor). Prove the spec law and `#print axioms` clean.
- [x] 2.2 Add `parseNumber` (wraps `strtod`/`strtoll`) for JSON/TOML literals, Lean body a slow
      reference parse; prove it agrees with the reference on the bench.
- [ ] 2.3 Add `deflate`/`inflate` (link zlib) for PNG IDAT, Lean body the raw/stored reference;
      note the zlib dependency boundary in the module header. (This is "unusable → usable", not
      a micro-opt.)

## 3. Deterministic decode under `Unambiguous`/`Functional`

- [ ] 3.1 Add `decodeOne {α} (d : Codec α) (a : Array UInt8) (i : Nat) : Option (α × Nat)` that
      commits each `|` choice, **gated** by a `Functional d` (or `Unambiguous d`) hypothesis, so
      no alternative is silently discarded. Prove it equals the (unique) `decodeArray` result
      under that hypothesis, `[propext, Quot.sound]`-only. Leave the unconditional `decode (d₁|d₂)`
      law untouched.
      _(In progress this session: `Codec/DecodeOne.lean` adds `decodeOne` (committed `alt` via
      `orElse`, `seq` via first-`d₁` `bind`), proves `decodeOne_mem` (unconditional soundness:
      committed result ∈ backtracking) and `decodeArray_functional_count` (`Functional d ⇒` same
      value ⇒ same consumed count), both `[propext, Quot.sound]`-only. Found (and recorded) that
      `decodeOne = (decodeArray ·).head?` is **false** — committed `seq` uses only the first `d₁`
      result, while `head?` skips dead-end first branches. The remaining sub-obligation is
      `decodeArray_unambiguous_value` (`Unambiguous d ⇒` same count ⇒ same value), whose
      `splice`/`prepend`-prefix transport is documented but not yet discharged in `DecodeOne.lean`.)_
- [x] 3.2 Confirm `#print axioms Codec.roundtrip` ⇒ `[propext, Quot.sound]` is unchanged after 3.x.

## 4. Per-format specialized paths (proved equal to spec)

- [ ] 4.1 WAV: `wavDecode` (44-byte header struct + one `blitBytes`/`memcpy` PCM block) and
      `wavEncode`, proved `[propext, Quot.sound]`-equal to the generic `decode`/`encode` of a
      WAV description by a `decodeArray_eq`-style lemma.
- [ ] 4.2 protobuf: tag/varint loop + length-delimited `blitBytes` body, proved equal to the
      spec; value-checked byte-for-byte including the varint seam (2.1).
- [ ] 4.3 JSON/TOML scanner (delimiter `findByte`/`memchr`, numbers via `parseNumber`), PNG
      (header + zlib seam), QR (byte matrix fill) — prove-agree-with-spec lemmas where structural,
      seam-backed where raw.

## 5. Bench + gate

- [ ] 5.1 Per-format lanes (WAV raw PCM, protobuf blobs, JSON scan) value-checked byte-for-byte
      against the spec, recording `[measured]` ns/op + MiB/s vs the `memcpy`/`byteSlice` baseline.
- [ ] 5.2 `lake build` zero `sorry`/warnings; `#print axioms Codec.roundtrip` ⇒ `[propext,
Quot.sound]`; every new seam's Lean body axiom-clean; every refinement `[propext,
Quot.sound]`-only. Update `README.md` §Performance and `AGENTS.md` with the shipped-C
      surface and the spec-vs-shipped two-layer framing (Layer 1 proven, Layer 2 trusted C,
      never conflated).
