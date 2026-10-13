# Proposal

## Why

The codec is **100% proven** (`Bytes = List UInt8` spec, `[propext, Quot.sound]`
only) and has a **committed `ByteArray` run-model** proved equal to it
(`decodeByteArray` / `decodeFullByteArray` / `encodeByteArray`, each with a
refinement lemma). But "proved equal" is not "fast", and the reason is now
precisely diagnosed (see `compiler-tier-extraction`): Lean 4's single C generator
(`Lean.Compiler.LCNF.EmitC`) emits a boxed, GC'd, reference-counted representation
— `Nat` as bignum `lean_object *`, `List UInt8` as cons cells, higher-order values
as `lean_alloc_closure`.

The **full** fix — a real, separate, GC-less C target (the KaRaMeL move) — is a
compiler-backend project, planned in `compiler-tier-extraction`, and is on the
order of weeks. This change is the **stopgap that lands first**: it uses the
_existing_ `@[extern]` FFI to splice hand-written, GC-less C into the _already
proved_ `ByteArray` run-model's hot path, reaching the `memchr`/`simdjson`
per-byte ballpark **now**, without touching the extraction pipeline at all.

The mechanism is exactly the one F\* uses for its own trusted primitives, and the
one Lean's stdlib already uses for `ByteArray` itself:

- The stdlib `ByteArray` surface is already a set of `@[extern]` primops
  (`lean_byte_array_fget`, `lean_sarray_size`, `lean_byte_array_get`,
  `lean_byte_array_copy_slice`, … — `Init/Data/ByteArray/Basic.lean`), each a
  `def` whose Lean body still elaborates (so the _meaning_ is pinned in Lean) and
  whose C symbol is supplied by the runtime as trusted C.
- Karamel's `[@@noextract_to "krml"] // primitive` + handwritten C is the same
  posture: declare the primitive in the trusted language, hand-write the C, name
  the trust seam.

So this change adds **a small set of our own `@[extern]` C primitives** — a
`uint8_t *` + `size_t` full-consumption byte loop, and slice-result
`(ptr, len)` accessors — wired into `decodeByteArray` / `decodeFullByteArray` /
`encodeByteArray`, links them via `leanc` (no `lean_rt` dependency for the new
code), and benchmarks them against a `memchr` baseline.

The proofs are unchanged: the `@[extern]` bodies still elaborate in Lean, so the
refinement lemmas (`decodeByteArray_eq`, `decodeFullByteArray_spec`) keep holding
`[propext, Quot.sound]`-only. The _only_ new trust is that the C symbol matches
its declared contract — a **named, isolated trust seam** at the buffer edge,
exactly as F\* trusts KaRaMeL / the Pulse C `read0`/`emplace` primitives.

## What Changes

- **A small `Codec/ExternFastPath.lean` (or `.c` + `@[extern]` decl) module**
  declaring the new primitives: a full-consumption `uint8_t *` byte loop returning
  a slice, and `(ptr, len)` result accessors — with Lean `def` bodies that still
  elaborate (pinning meaning) and `@[extern "c_symbol"]` names for the trusted C.
- **Hand-written, GC-less C** implementing those symbols (a bounds-checked
  `while`/`for` over `uint8_t *`, `memchr`-style), linked by `leanc` without
  pulling in the Lean runtime for the new code.
- **Rewiring of the run-model hot path**: `decodeByteArray`'s `byte` case,
  `decodeFullByteArray`'s `WellFounded.fix` recursion, and `encodeByteArray`'s
  accumulation route through the new primitives so the hot loop is the C loop, not
  the boxed `List`/`Nat` recursion.
- **A `Bench.lean` extern tier lane** driving the new primitives on the same
  `decodeByteArray byte` / `decodeFullByteArray byte` / `encodeByteArray byte`
  workloads, against the `List` spec, the boxed `ByteArray`, and a hand-tuned
  `memchr` baseline.
- **Zero change** to `Codec`/`Rel`/`decode`/`encode`/`Sound`, the `Bytes`
  substrate, or any law.

## Capabilities

### New Capabilities

_(None in the codec's observable denotation — `skip_specs: true`. The change adds
a *performance* seam, not a new decode/encode behavior; the codec still decodes
and encodes exactly the same values over exactly the same bytes.)_

### Modified Capabilities

_(None.)_

## Impact

- New `@[extern]` FFI + a `.c` file (trusted whole-cloth, like F\* trusts KaRaMeL),
  with a named trust seam recorded.
- `Bench.lean` gains an extern tier lane; the prove-vs-trust seam decision and the
  measured per-byte numbers are recorded in the README/ledger.
- **Depends on** `llvm-lean4-toolchain` (the `@[extern]` primops already on) and
  the `ByteArray` run-model from `bytearray-carrier-decoders`.
- **Non-goals:** no compiler backend (that is `compiler-tier-extraction`); no
  change to codec semantics; no `Classical`; no new proof axioms beyond
  `[propext, Quot.sound]` in the codec (the `@[extern]` C is a named trust seam,
  not a library law).

## Relationship to `compiler-tier-extraction`

This is the **stopgap** that lands before the full GC-less C target. It is the
"lighter-weight `@[extern]` C fast path" noted in
`compiler-tier-extraction/tasks.md` task 4.3. It de-risks the full backend by
validating the `memchr` baseline and the slice `(ptr, len)` representation up
front, and it gives a measured fast number _before_ the compiler to produce it
automatically is built. The full target remains the end goal; this change is
additive and does not preclude it.
