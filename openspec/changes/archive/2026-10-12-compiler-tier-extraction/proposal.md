# Proposal

## Why

The codec is **100% proven**: every law is stated over the `Bytes = List UInt8`
spec and holds with `[propext, Quot.sound]` only. There is also a **committed
`ByteArray` run-model** proved equal to that spec (`decodeByteArray` /
`decodeFullByteArray` / `encodeByteArray`, each with a refinement lemma). But
"proved equal to the spec" still does not mean "fast", and the reason is now
precisely understood:

Lean 4 has exactly **one** C code generator — `Lean.Compiler.LCNF.EmitC` — and
it emits a **boxed, GC'd, reference-counted** representation unconditionally:

- every `Nat` (including loop indices and `WellFounded.fix` measures) is a
  bignum `lean_object *` (`lean_nat_add`, `lean_nat_dec_lt`, …),
- every `List UInt8` is a chain of `lean_ctor` cons cells with `lean_inc_ref` /
  `lean_dec_ref` churn,
- every higher-order value (the `WellFounded.fix` recursion's `ih`, `attach`,
  `decodeFullByteArrayStep`) is a `lean_alloc_closure`.

The F\* world solved exactly this problem twice, and both are directly
transferable:

- **KaRaMeL** shows that "extract to C" can mean _no runtime, no GC_: its
  generated C links only `krmllib.h` (≈7 headers of macros + `typedef`s), maps
  machine ints to plain `uint8_t`/`uint32_t`/`uint64_t`, `Prims_string` to
  `const char *`, and `FStar_Bytes_bytes` to the slice `{ uint32_t length;
const char *data; }`. Allocation is libc `malloc`/`free`; stack `push_frame`
  is plain C stack. There is no garbage collector anywhere.
- **KaRaMeL's mechanism** is primitive _type mapping_ written as
  `[@@noextract_to "krml"] // primitive` annotations whose comment is the
  lowering: `scalar_t t → t`, `base_array_t t tn n → t[tn]`, `ptr_gen t → *t`,
  `null_gen → NULL`, `read0 → *p`.
- **Pulse** (`pulse/lib/pulse/c/Pulse.C.Types.{Base,Scalar,Array}.fsti`) reuses
  exactly this staircase of primitive declarations to give a separation-logic
  view of a **No-GC C memory model** (typed pointers, `pts_to`, `emplace`,
  `free`, `read0`) that extracts to the same unboxed C.

The gap on the _speed_ axis is therefore **not** a proof cost and **not** a
language limit: it is that Lean has **no "unboxed C" target** to select. This
change plans — and, over its tasks, begins — the **separate backend** that fills
that gap: a _real, additional Lean code-generation target_ that lowers a proved
subset of LCNF to **GC-less C** in the KaRaMeL mould, so the _same_
`decodeByteArray`/`decodeFullByteArray`/`encodeByteArray` functions compile to
the `uint8_t *`/slice C the benchmark needs instead of the boxed C they get
today.

The proofs are unchanged. The tier is a _backend choice_ applied to the same,
already-proved run-model; the refinement lemmas (`decodeByteArray_eq`,
`decodeFullByteArray_spec`) still pin the denotation. The only new artifact is
the backend and a _named, isolated trust seam_ at the buffer edge (exactly as
F\* trusts KaRaMeL, and as the Pulse C primitives trust `read0`/`emplace`).

## What Changes

No change to `Codec`/`Rel`/`decode`/`encode`/`Sound`, the `Bytes` substrate, or
any existing law. The deliverable is a **separate extraction backend** with
three properties, mirroring KaRaMeL:

1. `ByteArray` lowers to a **`uint8_t *` + `size_t`** buffer (a real buffer, no
   `lean_object`).
2. The decoder's **result is a slice `(ptr, len)`** over a destination buffer
   (or, for full-consumption, returned directly), _not_ a `List UInt8` of linked
   `lean_object` cells.
3. The hot byte loop lowers to a **bounds-checked `while`/`for` over `uint8_t *`**
   that the C compiler can vectorize — no GC, no per-byte allocation, no
   `Nat`-measure recomputation.

Concretely the change delivers:

- A **design for a real separate target** (this is the primary plan artifact):
  a new `EmitNoGC` emitter parallel to `Lean.Compiler.LCNF.EmitC`,
  a **representation/boxing pass** (the KaRaMeL type-map: `Nat → size_t`,
  `List UInt8 → (uint8_t *, size_t)`, no closures), a **minimal no-GC runtime
  header** (`krmllib.h`-shaped), a **driver switch** selecting the new target,
  and — because this is a _compiler backend_, not a library law — a **separate
  project/repository** (the KaRaMeL-to-F\* relationship, not a `lake` lib).
- A **prove-vs-trust decision** for the `ByteArray ↔ uint8_t *` correspondence
  (named-trust, as KaRaMeL/Hydropus-does-not-prove-the-backend-itself, unless a
  per-function refinement proof is reachable), isolated at the buffer edge so the
  codec laws stay `[propext, Quot.sound]`.
- A **benchmark acceptance gate** (`Bench.lean` tier lane) that drives the
  new target's output on the `decodeByteArray` / `decodeFullByteArray` /
  `encodeByteArray` workloads and records per-byte figures against the `List`
  spec, the boxed `ByteArray`, and a hand-tuned `memchr` baseline.

## Capabilities

### New Capabilities

_(None in the codec's observable denotation — `skip_specs: true`. The change
adds a *performance backend*, not a new decode/encode behavior; the codec still
decodes and encodes exactly the same values over exactly the same bytes.)_

### Modified Capabilities

_(None.)_

## Impact

- A new **separate extraction backend** — new Lean compiler modules
  (`EmitNoGC` + representation/boxing pass + minimal runtime header +
  driver flag), held in their own project (the KaRaMeL relationship), not in the
  `codec` library.
- The `ByteArray` run-model (`decodeByteArray`/`encodeByteArray`/
  `decodeFullByteArray`) gains a **fast, GC-less C backend** — same functions,
  different emitted code.
- `Bench.lean` gains a **tier lane** reporting the new target's per-byte
  throughput against `List`, the boxed `ByteArray`, and a `memchr` baseline.
- **Depends on** `llvm-lean4-toolchain` (the `@[extern]` primops already on) and
  the committed `ByteArray` run-model from `bytearray-carrier-decoders`.
- **Non-goals:** no change to codec semantics; no `Classical`; no new proof
  axioms beyond `[propext, Quot.sound]` _in the codec_ (the backend's own
  correctness — like KaRaMeL's — is a _named trust seam_, not a library law;
  fully verified compilation à la Hydropus/CompCert is a longer-term goal, out
  of scope here).

## Supersedes earlier "no FFI / compiler tier deferred" notes

An earlier handoff recorded the compiler tier as _deferred_. That is superseded:
the compiler tier is now the **active plan**, and this change is its plan of
record. The historical "deferred" notes in `AGENTS.md` and the archived change
ledgers remain accurate _as history_ (those changes genuinely shipped without a
backend) and are **not** rewritten; this change is the forward-looking
replacement.
