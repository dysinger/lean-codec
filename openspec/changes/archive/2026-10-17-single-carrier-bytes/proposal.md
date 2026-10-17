# Proposal

## Why

Five consecutive efficiency attempts (`buffer-carrier-decoders`,
`bytearray-carrier-decoders`, `llvm-lean4-toolchain`, `extern-c-fast-path`,
`slice-returning-run-model`) all failed for one shared, now-precise reason: the
library runs on an opaque, packed `ByteArray` slab but proves on a `List UInt8`
spec, and the **representation transfer** between them is the entire cost —
the `List` materialization at the decode edge, the O(n²) `List.append` encode
fold, the `Nat`-vs-`USize` index mismatch, and, decisively, the stdlib
`Array.extract` lemmas that leak `Classical.choice` into the very refinement
laws we swore to keep `[propext, Quot.sound]`-only. Each attempt treated a
symptom of the split; the split itself is the defect.

## What Changes

- **BREAKING** Replace the provable substrate `Bytes := List UInt8` with a
  single **length-indexed** byte string `Bytes n := Fin n → UInt8` (a reducible
  alias over `Fin`-indexed functions, equivalently `Vector UInt8 n`). There is
  one byte-string type: it reduces under `simp`/`rfl`/`induction` for proofs
  **and** lowers to a scalar indexed load in the emitted IR — no second
  carrier, no transfer lemma, no `Classical.choice`.
- **BREAKING** Thread the length index `n` through the core: `Rel d x (s : Bytes
n)`, `decode d (s : Bytes n) : List (α × ({m} × Bytes m))`, `encode d x : Option
({n} × Bytes n)`, and likewise `relRepeat`/`decodeRepeat`/`encodeRepeat`.
  The "remaining buffer" of a decode is a `Σ`/subtype of a shorter `Bytes m`
  together with a prefix proof, not a bare tail of a `List`.
- **Remove** the two-tier apparatus that the single carrier makes vestigial:
  `Codec/DecodeArray.lean`, `Codec/EncodeArray.lean`,
  `Codec/DecodeByteArray.lean`, `Codec/EncodeByteArray.lean`,
  `Codec/DecodeByteArraySlice.lean`, `Codec/EncodeByteArraySlice.lean`,
  `Codec/ExternFastPath.{lean,c}`, `Codec/Buffer.lean`, the `lakefile.lean`
  `externFastPathO` target, and the matching `Bench.lean` lanes. The
  `defaultTargets`/`lean_exe` wiring returns to a single `lake build`.
- **Preserve** every _semantic_ law (Invertibility, backtracking union,
  byte-exact roundtrip, lossless capture, partiality, inverse-preserving
  composition, least-fixpoint repetition). Only their **carrier** changes: from
  `List UInt8` to the length-indexed byte string.

## Capabilities

### New Capabilities

- `codec/byte-string`: the length-indexed byte string `Bytes n := Fin n → UInt8`
  and its structural operations (index, slice/prefix, concat, empty singleton) —
  the one substrate both interpretations and `Rel` are stated over.

### Modified Capabilities

- `codec`: the `decode`/`encode`/`Rel` signatures and every law move from an
  unspecified-length `List UInt8` byte string to a length-indexed `Bytes n`; the
  two-tier (`List` spec vs `ByteArray`/`Array`/`Buffer` run-model) representation
  is collapsed to the single carrier.

## Impact

- Core rewrite: `Codec/Codec.lean` (`Bytes`, `Rel`, `relRepeat`), `Codec/Decode.lean`
  (`decode`, `ConsumesByte`, `decodeRepeat`, `decodeFull`*), `Codec/Encode.lean`
  (`encode`, `encodeRepeat`), `Codec/Sound.lean` (all laws re-stated over the
  length-indexed carrier), `Codec/Combinators.lean`, `Codec/Iso.lean`,
  `Codec/VarBinary.lean`.
- Deletions: the seven carrier/transport modules listed above; `Codec.lean`
  (root) drops the deleted imports and re-exports the single substrate.
- `lakefile.lean`: drop the `externFastPathO` target and `moreLinkObjs`;
  `Bench.lean`: replace the array/byte-array/slice/extern lanes with a length-
  indexed-substrate lane and the roundtrip/law smoke checks.
- Axiom record unchanged and enforced: `#print axioms Codec.roundtrip` ⇒
  `[propext, Quot.sound]`, zero `Classical.choice`, zero `sorry`.
