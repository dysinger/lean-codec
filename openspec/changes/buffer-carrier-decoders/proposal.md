# Proposal

## Why

The provable core decodes over `Bytes = List UInt8` because `List` reduces under
`simp`/`rfl`/`induction` — every byte of every input is a heap-allocated
`lean_object` cons cell. That is the *right* substrate for proofs, but it caps the
running interpreters at ~30–100 ns/byte even after the `efficient-backtracking-decoder`
fusion pass (Tier A), because the byte-list carrier itself is the ceiling.

F\* (the paper's sibling line of work: miTLS, EverCrypt, HACL\*) solves exactly this
with a **two-tier split**: a pure `Seq`/list *spec* plus a `LowStar.Buffer`-backed
*run-model* that operates natively on an array with an index — never materializing
the list — and a single **refinement/equality proof** binding the run-model to the
spec. Every spec-level law then transfers by rewriting, not re-proving. This change
carries that same move into `codec`, *without* FFI or a code generator: the F\*
substrate analogy here is `Array UInt8` (via the reducible `ByteArray.data`), which
Lean reasons about by `List`-adjacent lemmas and which extraction turns into a flat,
contiguous region.

The repo already gestures at this — `Codec/Buffer.lean` defines `decodeBuffer`/
`encodeBuffer` — but they are a **transport barrier**, not a faster carrier: they call
`Buffer.toBytes` (materializing the full `List`) and then run the list interpreter on
it. The byte-list cost is still there. The missing piece is the F\*-style
**native-array recursion with an index**, defined directly over the array, plus its
equality proof against `decode d (arr.data.drop i)`.

## What Changes

- A **new module `Codec/DecodeArray.lean`** (plus `Codec/EncodeArray.lean`, or one
  combined `Codec/ArrayCodec.lean`) defining the indexed, array-carrier interpreters:
  - `decodeArray {α} (d : Codec α) (a : Array UInt8) (i : Nat) : List (α × Nat)`
    — the *same* recursion as `decode`, reading `a.getD i`/`a[i]` instead of
    cons-peeling; the remainder is a `Nat` index, not a byte list.
  - `encodeArray {α} (d : Codec α) (x : α) : Option (Array UInt8)` — the same
    recursion as `encode`, extending an `Array` (or an accumulator) instead of
    appending `List`s.
- **Equality laws** — the F\*-style refinement, proved once and only once, in the
  existing `rfl`/`simp`/`induction` style (`[propext, Quot.sound]`, no `Classical`,
  no `extern`):
  - `decodeArray_eq : decodeArray d a i = decode d (a.data.drop i)` (with remainders
    re-indexed), and its `= []` remainder reading.
  - `encodeArray_eq : encodeArray d x = some a ↔ encode d x = some a.data` (or the
    `Option`-morphism form).
- **Transferred laws** in `Codec/Sound.lean` (`decodeArray_spec`,
  `encodeArray_rel`, `roundtripArray`, and the full-consumption/repetition law
  `decodeArrayFull_spec`) — each a one-line rewrite through the `_eq` laws into the
  existing unconditional `Bytes`-level laws. No new semantics, no new induction.
- **Benchmark legs** in `Bench.lean` comparing `decodeArray`/`encodeArray` against
  the §10.5/Tier-A baselines, so the carrier swap is *measured*, not asserted.

## Capabilities

### New Capabilities

_(None — this is a proof-of-equivalence refactor: behavior unchanged by construction.)_

### Modified Capabilities

_(None — `Rel`, `decode`, `encode`, and every existing theorem statement are untouched.)_

## Impact

- New module(s) under `Codec/`, added to the `Codec.lean` aggregate import.
- `Codec/Sound.lean` gains transfer lemmas (derived, no new induction).
- `Bench.lean` gains `decodeArray`/`encodeArray` legs.
- No API breakage: existing names are untouched; the array carriers are additive, and
  every new law is stated as equality *to* the existing proven interpreter.

## Non-goals

- **No FFI, no `@[extern]`, no code generator, no `HashMap`/`Hashable`, no SIMD.**
  The "as fast as possible" tier (compiler/FFI/leaf-format `extern`) is a *separate,
  later* change, gated on real usage. This change is "work faster" via carrier swap,
  not "fastest."
- **No memoizing/chart parser.** Ambiguous-grammar DP is irrelevant to this carrier
  swap and remains out of scope.
- **No change to `Bytes = List UInt8`.** It stays the proof substrate forever; the
  array is the run-model that is *proved equal* to it.
