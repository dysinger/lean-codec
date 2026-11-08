// Copyright 2026 Department of Code LLC.
// SPDX-License-Identifier: AGPL-3.0-or-later
//
// The hand-written C reference parser: `codec_cRefByteMany`.
//
// WHY THIS FILE EXISTS
//
// Every performance figure in this repository is currently relative to the
// repository's own pure-Lean cursor loop (`idealCursor`). That answers "how much
// per-step work does the codec do above the cheapest possible Lean loop", but not
// the question a reader actually asks: **how far is this from a hand-written C
// parser over the same bytes?** `AGENTS.md` records that quoting a ratio against
// `memcpy` is a category error — `memcpy` moves a byte, a parser does per-element
// work — and that "the honest reference is a hand-written C parser, which this repo
// does not yet measure". This is that reference, and nothing else.
//
// WHAT IT DOES — and it must be the SAME job, or the ratio is meaningless:
//
// `Codec.decodeWhole Codec.byte byteConsumesByte a` decodes a whole `n`-byte buffer
// as *many* `Codec.byte`: one value per byte, consuming the buffer exactly, and
// yielding `some [b0, b1, …, b(n-1)]` when that succeeds and `none` otherwise. So
// the C side allocates an `n`-element value array and fills it with the input
// bytes, then returns it. That is deliberately the *minimum* a conforming
// implementation of this codec must do: read every byte, produce one value per
// byte, hand back the result list. It does **not** skip the output, because the
// Lean side does not either — an output-free C loop would be comparing a decoder
// against a checksum and would flatter C by exactly the allocation cost under
// discussion.
//
// WHAT IT IS NOT. It is not Layer 2. This is not a trust seam: nothing in the
// proven library calls it, it carries no `@[extern]` primitive, and it is **not**
// part of the `#print axioms` gate. It is a benchmark *reference* linked only into
// the `bench` executable. The library remains pure Lean with C only for generic
// bulk byte movement; this file parses bytes and is therefore deliberately
// outside `Codec/`'s design rule — it exists to be measured against, never used.
//
// The result is a `lean_object` array of `UInt8` values, matching what the Lean
// lane folds over, so both sides pay the same value-materialisation cost.

#include <lean/lean.h>
#include <stdlib.h>

// Decode `a` (a `ByteArray`) as many `Codec.byte`: one value per byte.
//
// Always returns `some` of a freshly allocated `Array UInt8` of the same length.
//
// There is deliberately **no `none` arm**, and an earlier version of this comment
// claimed one "kept so the caller's `match` is real" that the code does not contain
// (`codec-audit-round-nine` §7.11). The reason there is none is the fact: this codec
// is total. `n == 0` allocates a zero-length array and the loop body never runs, so
// an empty buffer decodes to `some #[]` — the same value `decodeWhole Codec.byte`
// returns. Adding a `none` arm would make the reference disagree with the Lean side
// on exactly the input the bench's `n = 0` cross-check now covers (§1.6), which is
// why the mismatch between this comment and the code was worth fixing rather than
// leaving as prose.
LEAN_EXPORT lean_obj_res codec_cRefByteMany(b_lean_obj_arg a) {
    size_t n = lean_sarray_size(a);
    const uint8_t *src = lean_sarray_cptr(a);

    // One value per input byte — the same output the Lean lane accumulates.
    // `lean_alloc_array(size, capacity)` already sets `m_size`; no separate
    // `lean_array_set_size` (that only *shrinks*, and is not exported).
    lean_object *arr = lean_alloc_array(n, n);
    lean_object **data = lean_array_cptr(arr);
    for (size_t i = 0; i < n; i++) {
        data[i] = lean_box_uint32((uint32_t)src[i]);
    }

    lean_object *some = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(some, 0, arr);
    return some;
}
