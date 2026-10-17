# Design

## Context

`codec` decodes/encodes real binary formats (JSON, PNG, QR, WAV, FLAC, Protobuf) as
`Codec α` descriptions. Two requirements must hold at once:

1. **Correct by proof**: the unconditional laws — `Rel`, `decode_spec`, `bidir`,
   `roundtrip`, `decodeRepeat_spec`, `decodeFull_spec`, the `Combinators` `_spec`/`_rel`
   laws, and the `varint` denotation — hold, `[propext, Quot.sound]`-only.
2. **Fast (direction of travel)**: the cost to remove is the interpreter's _result
   carrier_, not the byte loop. This change lands the packed carrier and its proof; the
   near-C performance of the general interpreter for arbitrary `α` is a follow-up, out of
   scope here.

The specification substrate is `Bytes n := Fin n → UInt8`, a length-indexed pure function.
Its read (`s ⟨i,·⟩`) is a scalar indexed load. Its _bulk write_ is a nested `concat`
closure per element, and the decoder's _result_ is a `List (α × Suffix n)` — a cons cell
and a `Suffix`/`Bytes` closure per result. The cost to remove is the result carrier, not
the byte loop.

This design has one job and states it once: give the interpreter a **packed `USize`-cursor
result carrier**, prove it equal to the `Bytes n` spec, and report two proof layers
honestly.

## The lever, stated once

The byte loop is already near `memcpy`. The cost is the result carrier. Therefore the fix
is a **result-carrier swap**, not a compiler and not more `@[extern]` C. Both of those are
already ruled out by prior, recorded work:

- `compiler-tier-extraction` (archived): "erase `Nat→size_t`" is a semantic change Lean's
  IR cannot express.
- `extern-c-fast-path` (archived, recorded as a no-op): hand-written C was a shim over the
  stdlib's own externs; the speed came from `ByteArray.push` replacing a `List.append`
  fold, needing no new C.

`USize` is the scalar index that matters: it _is_ a scalar in Lean's IR (unlike bignum
`Nat`), so the existing `EmitC` prints a `size_t` loop with no backend. (This is verified
by IR inspection as a task, not asserted.)

## The packed interpreter

### Decoder — full backtracking preserved

`decodeArray : Codec α → Array UInt8 → USize → List (α × USize)`, structurally identical
to `decode` but reading `a[i]` by index and threading `i + m` through `seq`:

- `alt` is `decodeArray d₁ a i ++ decodeArray d₂ a i` (the union).
- `seq` is the `flatMap` cross-product over all `d₁` results cross all `d₂` results.
- `byte` is one `a[i]` read plus one integer increment.

The result is `List (α × USize)`. The `List` is the **non-determinism multiplicity**,
which a faithful `decode` cannot drop without losing completeness; the packed carrier
removes only the **per-branch** `Suffix`/`Bytes` closure. A greedy (single-result) variant,
if wanted, is a separate `decodeGreedy` labeled **sound-not-complete**, never substituted
for `decode`.

### Full-consumption — packed suffix

`decodeFullArray : … → Option (ByteArray × USize)` — the packed suffix, one copy, never
`Option (List α × Suffix n)`. Its body is the `rfl`-clean
`ByteArray.mk ((a.data.toList.drop i.toNat).toArray)`, a list-materializing transport
chosen precisely so the refinement stays `Classical.choice`-free.

### Encoder — `ByteArray.push` accumulator

`encodeArray : Codec α → α → Option (Array UInt8)`, accumulating with `ByteArray.push`
(amortized O(n)) instead of the `concat`-closure fold. `encodeByteArrayBytes : List UInt8 →
ByteArray` is the byte-sequence packer (a `List UInt8`-to-`ByteArray` fold, not a general
`Codec α` encoder over arbitrary `α` — that is `encodeArray`).

## The refinement bridge (the real proof work)

Re-grounding the packed law onto `Bytes n` is **not** a cheap substitution. Today's
`decode : … → List (α × Suffix n)` carries `{ remaining : Nat, hle : remaining ≤ n,
bytes : Bytes remaining }`; a `USize`-cursor produces a _consumed_ count `c`. The bridge
reconstructs:

```
{ remaining := n - c, hle := Nat.sub_le n c, bytes := bdrop c s }
```

plus a proof `c ≤ n` (the cursor's stay-in-bounds invariant) — that is, both the length
(`n - c`) and the bytes (`bdrop`, a `Fin`-reindex), not a bare cast on a count.

The clean readback lemmas already in `Codec/Encode.lean` carry over for the _encode_ side:
`list_ofFn_getElem_clean` (`(List.ofFn s)[i] = s ⟨i,·⟩`), `ofFn_concat` (`List.ofFn`
distributes over `concat`), `pushBytesFrom_eq` (counter-indexed push equals the `List.drop`
enumeration), `array_readback` (`Array UInt8 → Bytes` pointwise). Each is verified
`[propext, Quot.sound]`-only. The decode-side `Suffix n` bridge does **not** exist yet and
is listed as from-scratch proof work.

## Two proof layers (both shipped, never conflated)

### Layer 1 — proven, zero trusted C

`decodeArray` / `decodeFullArray` / `encodeArray` / `encodeByteArrayBytes`, with
refinement laws `[propext, Quot.sound]`-only, proof body
`ByteArray.mk ((a.data.toList.drop i.toNat).toArray)`. This is the only layer admitted to
the `#print axioms` gate.

### Layer 2 — named trust seam

`byteSlice a i : ByteArray` (a `memcpy`-style suffix copy; `i : USize`). It does **not**
exist in the current tree — the extern tier was deleted — so it is **re-introduced fresh**,
wired onto a packed path. Its Lean body elaborates, so `#print axioms` reports the
proof-only body as `[propext, Quot.sound]`; but the running C is **trusted, not proven**,
so Layer 2 is **excluded** from the `#print axioms` gate and documented as a named trust
seam (F\*-vs-KaRaMeL posture).

## Measurement and acceptance

Every numeric figure SHALL be tagged `[measured]`, `[historical]`, or `[target]`, and
SHALL be produced by running the current `bench` (never a hand-typed number from a prior
draft). The bench reports both layers as distinct lanes, value-checked byte-for-byte, with
a ×1/×2/×4 sweep against the calibrated `memcpy` lane. Acceptance is: Layer 1 is a genuine
refinement (not greedy), `[propext, Quot.sound]`-only, and measurably faster than the
unpacked spec on the linear spine; Layer 2 reaches the `byteSlice` copy floor on a packed
path under its documented trust contract.

## What this design does not do

- Does **not** claim a compiler backend or new `@[extern]` C as the win.
- Does **not** silently substitute a greedy decoder for `decode`.
- Does **not** conflate "no axiom" with "no trust" for Layer 2.
- Does **not** claim near-C performance of the _general_ interpreter for arbitrary `α` on
  real workloads — the carrier and its proof land here; that performance claim is out of
  scope.
- Does **not** weaken the axiom gate or the bench value checks.
