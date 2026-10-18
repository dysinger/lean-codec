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
// Contract — identical to the Lean body (`ByteSlice.lean`), clause by clause.
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
// The code below reproduces exactly those three clamps:
//   dc   = `dstOff > n  ? n     : dstOff`         (mirrors `min dstOff n`)
//   copyLen = clamped first by `n - dc` (dst side), then by `slen - sc` (src side)
//   sc   = `srcOff > slen ? slen : srcOff`        (mirrors `min srcOff slen`)
//   copyLen = `min(len, n-dc, slen-sc)`            (= the body's `lc`)
// and materializes `n` bytes = full `dst` with `[dc, dc+copyLen)` overwritten by
// `src[sc, sc+copyLen)` (a single `memcpy` of the untouched prefix/suffix back to
// back plus one window `memcpy`).
//
// TRUSTED, NOT PROVEN (Layer 2, excluded from the `#print axioms` gate); must
// match the Lean body byte-for-byte on every input, including every out-of-range
// clamp above (empty source, `off` at/past either end, `len` past the end).
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
