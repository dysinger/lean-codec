// Copyright 2026 Department of Code LLC.
// SPDX-License-Identifier: AGPL-3.0-or-later
//
// The Layer-2 named trust seams: `codec_varintEncodeInto` / `codec_varintDecodeFrom`.
//
// Behind the `@[extern]` Lean primitives (see `Codec/VarintFast.lean`):
//
//   Codec.varintEncodeInto (dst : ByteArray) (off : USize) (n : Nat) : ByteArray
//   Codec.varintDecodeFrom (a : ByteArray) (off : USize) : Option (Nat × USize)
//
// Contract (verbatim, mirrors the Lean body):
//
//   * `codec_varintEncodeInto dst off n` writes the canonical LEB128 bytes of `n`
//     into `dst[off .. off+k)` (k = `varintBytes n`'s length) and returns `dst`
//     with that span overwritten and every other byte unchanged.
//   * `codec_varintDecodeFrom a off` returns `Some (n, k)` exactly when the `k`-byte
//     run from `off` is the canonical LEB128 encoding of `n`, and `None` otherwise.
//
// These C symbols are TRUSTED, NOT PROVEN — Layer 2 of the two-proof-layer split,
// excluded from the `#print axioms` gate. The Lean bodies in VarintFast.lean are
// the specifications; these symbols must match them byte-for-byte on every input.
//
// REPRESENTATION CONTRACT (small Nat only): the `Nat` values flowing through both
// seams are the *small* (immediate) `Nat`s that the bench value-checks (LEB128 keys,
// lengths, counts — all well under 2^63). A `Nat` larger than `LEAN_MAX_SMALL_NAT`
// is a bignum (`mpz`) and is NOT unboxed here; the Lean body — which is the spec —
// remains total over all `Nat`, but the trusted C is only exercised (and only
// claims to match) on the small-`Nat` span the caller uses. The byte-for-byte
// bench value check fails loudly if the C ever diverges from the Lean body.

#include <lean/lean.h>
#include <string.h>

// Unbox a *small* (immediate) `Nat` to `size_t`. Bignum (`mpz`) `Nat`s are out of
// scope for this seam (see the representation contract above).
static size_t nat_small_to_size_t(b_lean_obj_arg n) {
    // A small Nat is a scalar (immediate) object; `lean_unbox` reads the tag bits off.
    // A non-scalar (bignum/mpz) has the low bit clear and would be misread here.
    return lean_unbox(n);
}

// Encode `n` as LEB128 in-place at `dst[off..off+k)`, returning the full-length
// `dst`. Matches the Lean body: splice the canonical little-endian 7-bit encoding.
LEAN_EXPORT lean_obj_res codec_varintEncodeInto(lean_obj_arg dst, size_t off, b_lean_obj_arg n) {
    size_t v = nat_small_to_size_t(n);
    size_t dlen = lean_sarray_size(dst);
    uint8_t tmp[10]; // max LEB128 length for a 64-bit value
    size_t k = 0;
    do {
        uint8_t byte = (uint8_t)(v & 0x7f);
        v >>= 7;
        if (v != 0) byte |= 0x80;
        tmp[k++] = byte;
    } while (v != 0);

    // Clamp to dst bounds (mirrors Array.extract truncation in the Lean body).
    size_t clen = k;
    if (off > dlen) off = dlen;
    if (off + clen > dlen) clen = dlen - off;

    lean_obj_res r = lean_alloc_sarray(1, dlen, dlen);
    if (dlen > 0) memcpy(lean_sarray_cptr(r), lean_sarray_cptr(dst), dlen);
    if (clen > 0) memcpy((uint8_t*)lean_sarray_cptr(r) + off, tmp, clen);
    return r;
}

// Decode one canonical LEB128 varint from `a[off..]`. Return `Some (n, k)` or
// `None`. Matches the Lean body: `varintDecodeStep 0 1` on the suffix, consumed
// count `k`. `n` is boxed as a *small* Nat (see contract), `k` as a `USize`.
//
// Box of `some (n, k)` where `n : Nat`, `k : USize`:
//   - `Prod Nat USize` is a tag-0 pair with 2 object fields (both `Nat` and
//     `USize` box as objects: `Nat` via `lean_usize_to_nat`, `USize` via
//     `lean_box_usize`).
//   - `some` wraps the pair in the `Option`'s tag-1 constructor with one object
//     field. `None` is `lean_box(0)` (tag 0).
LEAN_EXPORT lean_obj_res codec_varintDecodeFrom(lean_obj_arg a, size_t off) {
    size_t n = lean_sarray_size(a);
    if (off >= n) return lean_box(0); // none: empty span
    const uint8_t* base = (const uint8_t*)lean_sarray_cptr(a);
    const uint8_t* p = base + off;
    const uint8_t* end = base + n;

    uint64_t v = 0;
    unsigned shift = 0;
    size_t k = 0;
    while (p < end) {
        uint8_t byte = *p++;
        k++;
        if (shift >= 64) return lean_box(0); // overflow (non-canonical)
        v |= ((uint64_t)(byte & 0x7f)) << shift;
        if ((byte & 0x80) == 0) {
            // Terminating byte: (byte & 0x80) == 0 means this is the last byte.
            // Box the result: some (n, k).
            lean_obj_res pair = lean_alloc_ctor(0, 2, 0); // Prod, 2 obj fields
            lean_ctor_set(pair, 0, lean_usize_to_nat((size_t)v)); // Nat (small)
            lean_ctor_set(pair, 1, lean_box_usize(k));           // USize
            lean_obj_res opt = lean_alloc_ctor(1, 1, 0);         // some, 1 obj field
            lean_ctor_set(opt, 0, pair);
            return opt;
        }
        shift += 7;
    }
    return lean_box(0); // none: unterminated
}
