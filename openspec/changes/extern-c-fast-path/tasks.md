# Tasks

> Stopgap change: speed up encode/decode maximally with trusted `@[extern]` C
> patches, landing **before** the full GC-less C extraction backend
> (`compiler-tier-extraction`). Additive; no change to codec semantics or laws.

## 1. Author the `@[extern]` primitives (trusted C, elaborating Lean bodies)

- [x] 1.1 Add `Codec/ExternFastPath.lean`: the `@[extern]` primitives, each a
      `def` with a **Lean body that still elaborates** (pinning meaning) and an
      `@[extern "codec_…"]` symbol — the `Init/Data/ByteArray/Basic.lean`
      `ByteArray.get`/`size` pattern. Surface (minimal): - `codec_decode_byte_loop` — full-consumption `uint8_t *` byte loop; - `codec_slice_len` / `codec_slice_data` — `(ptr, len)` result accessors; - `codec_encode_append` — append into a pre-sized `uint8_t *` buffer.
- [x] 1.2 Add `Codec/ExternFastPath.c`: the hand-written, **GC-less** C
      (bounds-checked `while`/`for` over `uint8_t *`, `memchr`-style; libc only,
      no `lean_rt`).

## 2. Route the run-model hot path through the primitives

- [x] 2.1 Route `decodeByteArray`'s `byte` case to a `uint8_t *` read + index
      increment (no `List` cell, no `Nat`-measure recomputation).
- [x] 2.2 Route `decodeFullByteArray`'s `WellFounded.fix` recursion to the C
      loop, producing the slice result; the `Nat` measure is erased on the C side.
- [x] 2.3 (encode) Route `encodeByteArray`'s accumulation to appends into a
      pre-sized `uint8_t *` buffer (amortized O(n), no per-byte box).

## 3. Wire the build + benchmark

- [x] 3.1 Link the `.c` via `leanc` (lakefile `moreLinkArgs` / the existing clang
      19 toolchain from `llvm-lean4-toolchain`); verify the emitted `.c` calls the
      `codec_…` symbols, not the Lean bodies.
- [x] 3.2 Add a `Bench.lean` **extern tier lane** driving the new primitives on
      `decodeByteArray byte` / `decodeFullByteArray byte` / `encodeByteArray byte`,
      plus a `memchr` (or equivalent) baseline for the head-to-head.
- [x] 3.3 Run it; record per-byte figures vs the `List` spec, the boxed
      `ByteArray`, and the `memchr` baseline. Acceptance: raw-byte path within ~2×
      of `memchr`; no regression on existing interpreter lanes.

## 4. Integration gate + documentation

- [x] 4.1 `lake build` (zero `sorry`/warnings), `#print axioms Codec.roundtrip` ⇒
      `[propext, Quot.sound]`, and `nix build .#checks.<system>.lean` + `nix build
  .#bench` green.
- [x] 4.2 Record the measured numbers and the **prove-vs-trust seam decision**
      (named trust, as F\* trusts KaRaMeL) in the README and the `AGENTS.md`
      handoff / ledger.
