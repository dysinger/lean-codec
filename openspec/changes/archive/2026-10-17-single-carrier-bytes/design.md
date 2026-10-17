# Design

## Context

`Codec/Codec.lean` currently defines `abbrev Bytes : Type := List UInt8` and
states `Rel`, `decode`, `encode`, `relRepeat`, `decodeRepeat`, `encodeRepeat`,
and every law over it. Seven further modules (`DecodeArray`, `EncodeArray`,
`DecodeByteArray`, `EncodeByteArray`, `DecodeByteArraySlice`,
`EncodeByteArraySlice`, `ExternFastPath`, `Buffer`) exist only to transport
between that `List` spec and a packed `ByteArray`/`Array` run-model, and each
transport lemma or `Array`-content lemma (`Array.toList_extract`,
`Array.getElem_extract`) pulls in `Classical.choice` — which the codec's
`[propext, Quot.sound]`-only axiom discipline forbids. The design collapses the
two tiers into one length-indexed substrate; the change is fully subtractive
once the core is re-derived.

## Goals / Non-Goals

**Goals**

- One byte-string type `Bytes n := Fin n → UInt8` that is structurally reducible
  (proofs) and a scalar indexed load (IR), with zero `Classical.choice` in any law.
- Re-state `Rel`/`decode`/`encode`/repetition and re-prove every semantic law over
  it, preserving the existing departure/strengthening anchors `[D1]`–`[D8]`/
  `[S1]`–`[S6]` unchanged in _meaning_.

**Non-Goals**

- Not changing `Iso`, the `Codec` AST constructors, or any combinator's semantics.
- Not re-adding a second carrier, a `@[extern]` seam, a compiler backend, or a
  `USize` slice surface — all are deleted, not replaced.
- Not weakening any law to gain ease; the roundtrip stays unconditional.

## Decisions

### 1. `Bytes n := Fin n → UInt8` (reducible alias), length as a type index

The substrate is `abbrev Bytes (n : Nat) : Type := Fin n → UInt8`. It is
_reducible_, so every `Fin`/`funext` lemma applies, and `s i` for `i : Fin n` is
a structural read (the `byte` decoder is `s ⟨0, _⟩` plus a suffix shift). The
length `n` is a _type_ index, not a value, so there is no `Nat` box in the hot
path and no `USize.toNat` correspondence to prove.

_Alternative considered:_ `Vector UInt8 n` (mathlib-style) — rejected only
because it is not in the stdlib; the `Fin n → UInt8` spelling is the stdlib-only
equivalent and keeps the project mathlib-free.

### 2. Remaining buffer is a named `Suffix`, not a bare tail

`decode` has type `decode d (s : Bytes n) : List (α × Suffix n)` where

```
structure Suffix (n : Nat) where
  consumed : Nat
  remainder : Bytes (n - consumed)
```

A decode result carries `consumed` explicitly and the tail `remainder : Bytes
(n - consumed)`; the "remaining buffer" is a shorter `Bytes`, never a `List` tail
whose length must be recomputed. Sequentially `seq` composes suffixes by
`consumed₁ + consumed₂` with the `Nat` sub arithmetic closed by a prefix lemma
(the analogue of the current `decode_suffix`/`drop_add_length_of_append`).

_Alternative considered:_ returning `Σ m, m ≤ n × Bytes m` — equivalent but
less ergonomic; the `Suffix` record with `n - consumed` encodes `m ≤ n` by
construction and avoids an explicit `≤` proof field in every result.

_Implementation refinement (this session):_ the `Suffix n` structure is spelled
`{ remaining : Nat, hle : remaining ≤ n, bytes : Bytes remaining }` — the spec's
`({m : Nat} × Bytes m)` with the `m ≤ n` witness — rather than
`{ consumed, remainder : Bytes (n - consumed) }`. Reason: `seq` composes two
suffixes (`d₁` leaves `t : Suffix n`, `d₂` runs on `t.bytes : Bytes t.remaining`)
by threading the nested witness `r.hle ∘ t.hle : r.remaining ≤ n` transitively,
with **no** `Nat.sub` re-derivation of `(n - c₁) - c₂`. The `consumed` length is
still the named quantity `Suffix.consumed = n - remaining` (recoverable, never a
recomputed `List.length`); the spec's "consumed length is a named witness" is
satisfied by that accessor.

### 3. `Rel` is stated over the length-indexed string directly

`Rel {α} (d : Codec α) (x : α) {n : Nat} (s : Bytes n) : Prop`, with the
`seq` case splicing two substrings into `s` by a finitary `Fin`-indexed split.
`relRepeat` follows unchanged in structure, over `Bytes`-valued steps. This keeps
`Rel` the _whole-string_ relation the paper states, with `n` implicit.

### 4. Encode returns a length-indexed string, not a bare `List`

`encode d x : Option ({n : Nat} × Bytes n)` — the encoded bytes _and_ their
length, in one value, so `roundtrip` can name the empty remainder `Bytes 0`
without a separate length. `encodeRepeat p xs` likewise returns the `Sigma` of
the total length and the concatenated bytes, built by a `Fin`-sum concat (O(n)
in the _type_ index, no quadratic `List.append`).

### 5. Delete the transfer tier wholesale

`DecodeArray`/`EncodeArray`/`DecodeByteArray`/`EncodeByteArray`/
`DecodeByteArraySlice`/`EncodeByteArraySlice`/`ExternFastPath` (+ `.c`)/
`Buffer`, the `lakefile.lean` `externFastPathO` target, and the matching
`Bench.lean` lanes are removed. The root `Codec.lean` re-exports only `Iso`,
`Codec`, `Decode`, `Encode`, `Sound`, `Combinators`, `VarBinary`. `Sound.lean`
is re-derived in place over the single carrier.

## Risks / Trade-offs

- _[The `Fin n → UInt8` functions don't `induction` like a `List`]_ → proofs use
  `Fin`-extensionality (`funext`) + `fin_cases`/`interval_cases`, all of which are
  constructive and `Classical.choice`-free (the exact property `List.ext` lacked).
- _[`Nat.sub`/`Nat.add` arithmetic in `Suffix`/seq gets fiddly]_ → reuse the
  existing `drop_add_length_of_append`/`decode_suffix` shape, re-proved for the
  `Fin`-shift; the consuming-`n`-bytes witness is carried explicitly (Decision 2).
- _[Vector equality needs funext over `Fin n`]_ → `Fin n → UInt8` equality is
  decidable via `funext`; `propext`/`Quot.sound` are already in the accepted
  axiom set (they are _not_ `Classical.choice`).
- _[The rewrite is broad, touching every law]_ → do it as one backwards-
  incompatible change with the old modules deleted, not shimmed; the proof gate
  (`lake build`, zero `sorry`) is the acceptance, so a partial rewrite is
  as visible as none.
- _[Bench acceptance for the carrier swap]_ → a `Bytes`-substrate lane in
  `Bench.lean` demonstrates the scalar-index read and empty-remainder roundtrip;
  the prior `List`/`ByteArray` lanes are deleted with their modules, so there is
  no regression surface.

## Migration Plan

Single atomic change: rewrite the core (`Codec`/`Decode`/`Encode`/`Sound`/
`Combinators`/`VarBinary`), delete the transfer modules, simplify the `lakefile`
and `Bench`, then `lake build` (zero `sorry`) + `#print axioms Codec.roundtrip`
⇒ `[propext, Quot.sound]`. No in-between state is published; the old carrier
modules are removed in the same change that introduces the new substrate.
