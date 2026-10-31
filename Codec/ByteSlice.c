// Copyright 2026 Department of Code LLC.
// SPDX-License-Identifier: AGPL-3.0-or-later
//
// The Layer-2 named trust seam: `codec_byteSlice`.
//
// This is the hand-written C behind the `@[extern "codec_byteSlice"]` Lean
// primitive `Codec.byteSlice (a : ByteArray) (i : USize) : ByteArray` (see
// `Codec/ByteSlice.lean`). Contract: return a fresh ByteArray holding the bytes
// of `a` at-or-after index `i` (empty when `i` is at-or-past the end), copied
// with a single `memcpy`.
//
// This C is TRUSTED, NOT PROVEN — it is Layer 2 of the two-proof-layer split and
// is excluded from the `#print axioms` gate. The Lean body in ByteSlice.lean is
// the specification; this symbol must match it byte-for-byte on every input.

#include <lean/lean.h>
#include <string.h>

LEAN_EXPORT lean_obj_res codec_byteSlice(lean_obj_arg a, size_t i) {
    size_t n = lean_sarray_size(a);
    size_t len = (i < n) ? (n - i) : 0;
    lean_obj_res r = lean_alloc_sarray(1, len, len);
    if (len > 0) {
        memcpy(lean_sarray_cptr(r), lean_sarray_cptr(a) + i, len);
    }
    return r;
}

// The Layer-2 named trust seam: `codec_blitBytes`.
//
// Behind `@[extern "codec_blitBytes"]` Lean primitive
// `Codec.blitBytes (dst : ByteArray) (dstOff : USize) (src : ByteArray)
// (srcOff : USize) (len : USize) : ByteArray`.
//
// Contract — equal to the Lean body (`ByteSlice.lean`) **value-for-value**, not
// term-for-term.
//
// The Lean body computes, in `Nat`, with `n := dst.data.size`, `slen :=
// src.data.size`:
//   dc := min dstOff.toNat n            (destination cursor, clamped to [0, n])
//   sc := min srcOff.toNat slen          (source cursor, clamped to [0, slen])
//   lc := min len.toNat (min (n-dc) (slen-sc))   (copied run, clamped to fit both)
// and returns `dst[0,dc) ++ src[sc,sc+lc) ++ dst[dc+lc,n)` — the full length `n`
// of `dst`, with the `[dc, dc+lc)` window overwritten by `src[sc, sc+lc)`.
// `lc` is the single shared copied-length: the window replacement must agree on
// `lc` across the middle and the trailing part.
//
// The code below does **not** write that expression out. It clamps in a
// *different order* — destination cursor, then dest-side length, then source
// cursor, then source-side length:
//   dstOff := min dstOff n ; copyLen := min len (n - dstOff)
//   srcOff := min srcOff slen ; copyLen := min copyLen (slen - srcOff)
// and the two agree because `min` is associative and commutative: the body's
// `min len (min (n - dc) (slen - sc))` and the C's `min (min len (n - dc))
// (slen - sc)` are the same `Nat`. Worth stating because the clamps are *not*
// textually the same, and a reader comparing line by line would "fix" a
// mismatch that is not one. Verified exhaustively (`n, slen < 6`, offsets and
// `len < 9`) rather than by eye.
//
// **Allocation-length invariant (implicit above, stated here).** `copyLen` is
// clamped to `n - dstOff` *before* it is clamped to `slen - srcOff`, and
// `dstOff ≤ n`, so `dstOff + copyLen ≤ n` always holds. The buffer is therefore
// allocated and returned at the full `n` — total length `n`, never
// `dstOff + copyLen` — and the trailing `memcpy` of the source window can never
// write past it. That invariant is what makes the trailing part of the body's
// `dst[dc+lc, n)` well defined in the C as "the rest of the `n` bytes".
//
// TRUSTED, NOT PROVEN (Layer 2, excluded from the `#print axioms` gate); must
// match the Lean body value-for-value on every input, including every
// out-of-range clamp above (empty source, `off` at/past either end, `len` past the
// end). Agreement is by `min`'s associativity and commutativity — see above — not
// by the code being a transcription of the body.
LEAN_EXPORT lean_obj_res codec_blitBytes(lean_obj_arg dst, size_t dstOff,
                                          lean_obj_arg src, size_t srcOff,
                                          size_t len) {
    size_t n = lean_sarray_size(dst);
    size_t copyLen = len;
    // Clamp the copied run to avoid reading past `src` or writing past `dst`;
    // this mirrors the `Array.extract` bounds in the Lean body (which truncate
    // at the array end). The Lean body is total in the same sense: `extract`
    // clamps its stop index. The `> n - dstOff` / `> slen - srcOff` forms are
    // used (not `dstOff + copyLen > n`) so the comparison is overflow-stable
    // even for a pathological `len` near `SIZE_MAX` — the Lean `Nat` never wraps
    // (`min len (n - dc) (slen - sc)`), so the C must not either.
    if (dstOff > n) dstOff = n;
    if (copyLen > n - dstOff) copyLen = n - dstOff;
    {
        size_t slen = lean_sarray_size(src);
        if (srcOff > slen) srcOff = slen;
        if (copyLen > slen - srcOff) copyLen = slen - srcOff;
    }
    lean_obj_res r = lean_alloc_sarray(1, n, n);
    if (n > 0) {
        memcpy(lean_sarray_cptr(r), lean_sarray_cptr(dst), n);
    }
    if (copyLen > 0) {
        memcpy(lean_sarray_cptr(r) + dstOff, lean_sarray_cptr(src) + srcOff, copyLen);
    }
    return r;
}

// The Layer-2 named trust seam: `codec_findByte`.
//
// Behind `@[extern "codec_findByte"]` Lean primitive
// `Codec.findByte (a : ByteArray) (off : USize) (b : UInt8) : Option USize`.
// Contract: return the first index `i >= off` (as a boxed `Option USize`, i.e.
// `some(i)` as a `lean_box(i)` / `none` as `lean_box(0)`) at which `a[i] == b`,
// or `lean_box(0)` (none) when there is no such index; a single `memchr` over
// the suffix. TRUSTED, NOT PROVEN (Layer 2, excluded from the `#print axioms`
// gate); must match the Lean body (the `Array.findIdx?` scan) on every input.
// Side condition: the Lean body re-offsets with USize addition (mod 2^64) while
// this returns a raw absolute `size_t`, so the two agree whenever
// `off + idx` does not wrap — see the docstring on `Codec.findByte`.
LEAN_EXPORT lean_obj_res codec_findByte(lean_obj_arg a, size_t off, uint8_t b) {
    size_t n = lean_sarray_size(a);
    if (off >= n) {
        return lean_box(0); // none
    }
    const uint8_t* base = (const uint8_t*)lean_sarray_cptr(a);
    const void* hit = memchr(base + off, b, n - off);
    if (hit == NULL) {
        return lean_box(0); // none
    }
    size_t idx = (size_t)((const uint8_t*)hit - base);
    // some (idx : USize): an Option USize is a tag-0 `none` (lean_box(0)) or a
    // tag-1 `some` constructor holding one scalar field, itself the boxed USize
    // (`lean_box_usize(idx)`), matching how the Lean-generated code constructs it.
    lean_obj_res r = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(r, 0, lean_box_usize(idx));
    return r;
}
