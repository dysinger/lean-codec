/* Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later */

/*
 * The trusted, GC-less C fast path for the codec's `ByteArray` run-model.
 *
 * These symbols back the `@[extern]` primitives in `Codec/ExternFastPath.lean`.
 * Each has a *Lean body that still elaborates* (pinning the meaning — see that
 * module); this C is trusted to satisfy the declared contract, and is a named,
 * isolated trust seam at the buffer edge (the F*-trusts-KaRaMeL posture). It
 * introduces no proof axiom and no new dependency on `lean_rt` beyond the inline
 * sarray primitives already provided by `<lean/lean.h>`.
 *
 * Calling convention (Lean C ABI, 4.34.1):
 *   - a `ByteArray` is a `lean_object *` pointing at a `lean_sarray_object`
 *     (`elem_size = 1`): `lean_sarray_size(a)`, `lean_sarray_cptr(a)` (uint8_t *).
 *   - a `Nat` argument/return is a boxed pointer-sized scalar: `lean_unbox` /
 *     `lean_box`; a `bignum` (> mpt limit) is an object, guarded here.
 *   - a `UInt8` argument is passed unboxed as `uint8_t`.
 */

#include <lean/lean.h>
#include <string.h>

#if defined(__cplusplus)
extern "C" {
#endif

/*
 * codec_byte_array_slice : ByteArray → Nat → ByteArray
 *
 * Copy the suffix `a[i .. a.size)` into a fresh packed `ByteArray` in one
 * bounds-checked `memcpy` (the `Codec.byte` full-consumption hot path). The
 * Lean body is `a.extract i a.size`, so the contract is: result bytes = the
 * `a.size - i` bytes starting at `a[i]` (i.e. `a.data.toList.drop i`), empty
 * when `i ≥ a.size` (and for any non-scalar/bignum index, which cannot address
 * a real array).
 */
LEAN_EXPORT lean_object * codec_byte_array_slice(lean_object * a, lean_object * i) {
    if (lean_is_scalar(i)) {
        size_t idx = lean_unbox(i);
        size_t size = lean_sarray_size(a);
        if (idx >= size) {
            return lean_alloc_sarray(1, 0, 0);
        }
        size_t len = size - idx;
        lean_object * r = lean_alloc_sarray(1, len, len);
        memcpy(lean_sarray_cptr(r), lean_sarray_cptr(a) + idx, len);
        return r;
    }
    /* bignum index: cannot address any real array — the empty suffix. */
    return lean_alloc_sarray(1, 0, 0);
}

/*
 * codec_encode_append : ByteArray → UInt8 → ByteArray
 *
 * Append one byte into a packed accumulator, growing it amortized-O(1). The
 * Lean body is `a.push b`, whose own `@[extern]` symbol is
 * `lean_byte_array_push`; this is the dedicated, named wrapper so the encode
 * accumulation stays on the packed `uint8_t *` path (no per-byte box, no
 * `List` cell).
 */
LEAN_EXPORT lean_object * codec_encode_append(lean_object * a, uint8_t b) {
    return lean_byte_array_push(a, b);
}

#if defined(__cplusplus)
}
#endif
