// Copyright 2026 Department of Code LLC.
// SPDX-License-Identifier: AGPL-3.0-or-later
//
// The Layer-2 named trust seam: `codec_parseNumber`.
//
// Behind the `@[extern]` Lean primitive (see `Codec/NumParse.lean`):
//
//   Codec.parseNumber (a : ByteArray) (off : USize) : Option (Nat × USize)
//
// Contract (verbatim, mirrors the Lean body): parse the longest nonempty run of
// ASCII decimal digits (`0x30`–`0x39`) from `a[off ..)`, returning `Some (n, k)`
// (value + byte count consumed), or `None` when the span has no leading digit.
//
// This C is TRUSTED, NOT PROVEN — Layer 2 of the two-proof-layer split, excluded
// from the `#print axioms` gate. The Lean body in NumParse.lean is the
// specification; this symbol must match it byte-for-byte on every input.
//
// REPRESENTATION CONTRACT (small Nat only): the parsed value `n` is boxed as a
// *small* (immediate) `Nat` via `lean_usize_to_nat`. A decimal numeral too large
// to fit a `size_t` would overflow the C accumulator (and diverge from the Lean
// body, which is total over all `Nat`); the bench value-checks small values and
// would fail loudly on any divergence. The value box is `some (n, k)` where the
// pair `Prod Nat USize` has two object fields (Nat via `lean_usize_to_nat`, USize
// via `lean_box_usize`), wrapped in the `Option`'s tag-1 constructor.

#include <lean/lean.h>

LEAN_EXPORT lean_obj_res codec_parseNumber(lean_obj_arg a, size_t off) {
    size_t n = lean_sarray_size(a);
    if (off >= n) return lean_box(0); // none: no span
    const uint8_t* base = (const uint8_t*)lean_sarray_cptr(a);
    const uint8_t* p = base + off;
    const uint8_t* end = base + n;

    size_t v = 0;
    size_t k = 0;
    while (p < end) {
        uint8_t byte = *p;
        if (byte < 0x30 || byte > 0x39) break; // not an ASCII digit
        v = v * 10 + (size_t)(byte - 0x30);
        p++;
        k++;
    }
    if (k == 0) return lean_box(0); // none: no leading digit

    // some (n : Nat, k : USize)
    lean_obj_res pair = lean_alloc_ctor(0, 2, 0);       // Prod Nat USize, 2 obj fields
    lean_ctor_set(pair, 0, lean_usize_to_nat(v));       // Nat (small)
    lean_ctor_set(pair, 1, lean_box_usize(k));          // USize
    lean_obj_res opt = lean_alloc_ctor(1, 1, 0);        // some, 1 obj field
    lean_ctor_set(opt, 0, pair);
    return opt;
}
