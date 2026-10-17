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
