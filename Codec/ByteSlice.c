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
// (srcOff : USize) (len : USize) : ByteArray`. Contract: copy `len` bytes from
// `src[srcOff..srcOff+len)` into `dst[dstOff..dstOff+len)`, returning the full
// length of `dst` as a fresh ByteArray (prefix/suffix unchanged); the middle
// window is a single `memcpy`. TRUSTED, NOT PROVEN (Layer 2, excluded from the
// `#print axioms` gate); must match the Lean body byte-for-byte on every input.
LEAN_EXPORT lean_obj_res codec_blitBytes(lean_obj_arg dst, size_t dstOff,
                                          lean_obj_arg src, size_t srcOff,
                                          size_t len) {
    size_t n = lean_sarray_size(dst);
    size_t copyLen = len;
    // Clamp the copied run to avoid reading past `src` or writing past `dst`;
    // this mirrors the `Array.extract` bounds in the Lean body (which truncate
    // at the array end). The Lean body is total in the same sense: `extract`
    // clamps its stop index.
    if (dstOff > n) dstOff = n;
    if (dstOff + copyLen > n) copyLen = n - dstOff;
    {
        size_t slen = lean_sarray_size(src);
        if (srcOff > slen) srcOff = slen;
        if (srcOff + copyLen > slen) copyLen = slen - srcOff;
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
