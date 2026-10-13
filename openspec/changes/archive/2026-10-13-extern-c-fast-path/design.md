# Design

## Context

`compiler-tier-extraction` plans the _full_ GC-less C target (a new Lean backend).
That is weeks of work. This change is the **`@[extern]` stopgap** that lands first:
hand-written, GC-less C for the `ByteArray` run-model's hot path, spliced in via
Lean's existing FFI, reaching the `memchr` ballpark now without touching the
extraction pipeline.

Two references ground the mechanism:

1. **Lean's own stdlib** already uses `@[extern]` to make `ByteArray` fast:
   `Init/Data/ByteArray/Basic.lean` declares `def get : (@& ByteArray) → (@& Nat)
→ … → UInt8 | ⟨bs⟩, i, _ => bs[i]` tagged `@[extern "lean_byte_array_fget",
implicit_reducible]` — the Lean body _elaborates_ (pinning the meaning), and
   codegen emits a call to the runtime's trusted `lean_byte_array_fget` C symbol.
   `size` → `lean_sarray_size`, `get!` → `lean_byte_array_get`,
   `copySlice` → `lean_byte_array_copy_slice`, `hash` → `lean_byte_array_hash`.
2. **Karamel/Pulse** use the identical posture for their no-GC memory model:
   `[@@noextract_to "krml"] // primitive` declarations (`scalar_t t → t`,
   `base_array_t t tn n → t[tn]`, `ptr_gen t → *t`, `read0 → *p`) whose comment is
   the C lowering, implemented by hand-written C in `krmllib`.

So the pattern is settled: **declare the primitive with a real Lean body (proof
pinned), tag `@[extern "symbol"]`, and supply the symbol in a trusted `.c` file
linked by `leanc`.**

## Goals / Non-Goals

### Goals

- Maximally speed up `decodeByteArray` / `decodeFullByteArray` / `encodeByteArray`
  on the `byte`/`many` hot path via **hand-written GC-less C** (`uint8_t *` +
  `size_t` loop, `(ptr, len)` slice result), reaching within ~2× of `memchr`.
- Keep the proofs **unchanged and green**: the `@[extern]` Lean bodies elaborate,
  so `decodeByteArray_eq` / `decodeFullByteArray_spec` still hold
  `[propext, Quot.sound]`-only; the trust seam is _named and isolated_ at the
  buffer edge.
- Land a **`Bench.lean` extern tier lane** reporting per-byte figures against the
  `List` spec, the boxed `ByteArray`, and a `memchr` baseline.

### Non-Goals

- **Not** the full GC-less C target (that is `compiler-tier-extraction`) — no new
  backend, no `EmitNoGC`, no patched `lean`.
- **Not** a proof that the hand-written C matches the symbol's contract (the F\*
  trust seam); if a _per-function_ refinement proof is later reachable it is a
  follow-up, not this stopgap.
- **Not** changing codec semantics, the `Bytes` substrate, or any law.

## Decisions

1. **Trusted C via `@[extern]`, with Lean bodies that still elaborate.** Each
   primitive is a `def` whose body reduces in Lean (so `simp`/`rfl` still see the
   meaning and the refinement lemmas transfer), tagged `@[extern "symbol"]` so the
   _emitted_ code calls trusted C. This is Lean stdlib's own `ByteArray.get`
   pattern, not a bare `opaque`.

2. **The primitives are the hot path only.** We add the smallest set:
   - a full-consumption `ByteArray → Option (ByteArray × Nat)` _native loop_
     (`uint8_t *` read + index step, `memchr`-style), and
   - slice/`(ptr, len)` accessors (or a `ByteArray` sub-view) so the result is a
     packed buffer, not a `List UInt8` of cons cells.
     `decodeByteArray`'s `byte` case, `decodeFullByteArray`'s `WellFounded.fix`
     recursion, and `encodeByteArray`'s accumulation route through these; everything
     else stays on the boxed path.

3. **The trust seam is named and isolated at the buffer edge.** We record, in the
   README and ledger, that "the C symbol `…` is trusted to satisfy its declared
   contract" — the F\* stance toward KaRaMeL. The codec's laws remain
   `[propext, Quot.sound]`; the seam does not leak a new proof axiom.

4. **`skip_specs: true`.** The codec denotation is unchanged; this is a
   performance seam.

5. **Linking via `leanc`, no `lean_rt` for the new code.** The new `.c` uses only
   libc (`memchr`, `malloc`/`free` as needed); it is compiled and linked by the
   existing `leanc`/clang 19 toolchain (`llvm-lean4-toolchain`).

6. **`Bench.lean` extern tier lane is the acceptance gate.** "Maximally fast" is
   a measured number, acceptance ~2× of `memchr` on the raw-byte path.

## The primitives (concrete surface)

Modeled on `Init/Data/ByteArray/Basic.lean`:

- `@[extern "codec_decode_byte_loop"]` — a `def` over `ByteArray`/`Nat` with a
  Lean body mirroring `decodeFullByteArray`'s `byte` consumption (so the `_spec`
  law still reduces), whose C symbol is the hand-written loop:
  ```c
  // bounds-checked: while (i < size) { *dst++ = data[i++]; }  — returns (ptr, len)
  ```
- `@[extern "codec_slice_len"]` / `@[extern "codec_slice_data"]` — `(ptr, len)`
  accessors so the result is a packed `ByteArray` sub-view rather than a `List`.
- (encode) `@[extern "codec_encode_append"]` — appends into a pre-sized
  `uint8_t *` buffer (amortized O(n)).

Each `def` body reduces over `ByteArray.data`/`size` (the reducible path already
used by `decodeByteArray_eq`), keeping the refinement lemmas intact.

## Risks / Trade-offs

- _[The C symbol may not match its contract]_ → this is the named trust seam
  (F\*-trusts-KaRaMeL). Mitigation: the Lean body still elaborates and is tested;
  the C is minimal (a `memchr`-style loop), and the bench lane checks byte-exact
  output.
- _[A slice result may dangle after the source buffer is freed]_ → documented
  ("slice valid while the source `ByteArray` lives").
- _[`@[extern]` bodies that elaborate may still be codegen-overridden wrongly]_
  → we follow the stdlib pattern exactly (`implicit_reducible` where needed) and
  verify the emitted `.c` calls the symbol, not the body.
- _[Returning a slice breaks the existing `decodeByteArray : List (α × Nat)`
  signature]_ → the public `decodeByteArray` still returns `List (α × Nat)`; the
  C primitive is an _internal_ fast path wrapped by it, materializing the list at
  the boundary (or a new `decodeByteArraySlice` entry point for zero-copy callers).
- _[Blending FFI into a git history that once recorded "no FFI"]_ → this change is
  the deliberate reversal; recorded plainly (see proposal).

## Migration Plan

1. Author `Codec/ExternFastPath.lean` (+ `Codec/ExternFastPath.c`): the
   `@[extern]` primitives with elaborating Lean bodies, and the hand-written C.
2. Route `decodeByteArray`'s `byte` case, `decodeFullByteArray`'s recursion, and
   `encodeByteArray`'s accumulation through the new primitives.
3. Wire the `.c` into the build (`lakefile` `moreLinkArgs`/`leanc` link) and add
   the `Bench.lean` extern tier lane + `memchr` baseline.
4. Run it; record per-byte before/after; verify the proof gate (`lake build` zero
   `sorry`, `[propext, Quot.sound]`) and `nix build .#bench`.
5. Record the prove-vs-trust seam decision in the README + `AGENTS.md` handoff.

## Open Questions

- Whether to expose a new `decodeByteArraySlice` zero-copy entry point or keep the
  C primitive internal and materialize `List` at the boundary.
- The exact C symbol set / whether `memchr` itself is inlined or called.
- The measured acceptance threshold (confirm ~2× of `memchr` from the first run).
