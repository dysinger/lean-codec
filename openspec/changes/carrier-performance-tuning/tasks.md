# Tasks

> The plan is a packed `USize`-cursor carrier for `decode`/`encode` over arbitrary
> `Codec α`, proved equal to the `Bytes n := Fin n → UInt8` spec, with two proof layers
> (proven zero-C, and a `@[extern]` named trust seam). In scope: the carrier and its
> refinement proof. Out of scope: near-C performance of the general interpreter on real
> workloads (JSON/PNG/protobuf). Every numeric figure is produced by running the current
> `bench`, never hand-typed.

## Session log (this session)

**Latest (this session): encode refinements landed, decode `seq` bridge blocked.**

The four Layer-1 refinement laws are now: `encodeArray_eq` and
`encodeByteArrayBytes_eq` **proved** (`[propext, Quot.sound]`-only, zero `sorry`,
zero `Classical.choice`), plus a tranche of clean decode-side transport lemmas
(`sub_sub_eq`, `bdrop_add`, `consumedAbs_remaining`). The encode proof uses the
**List-level readback** form (`(encodeArray d x).map (·.toList) = (encode d x).map
(List.ofFn ∘ snd)`) — the `Array.toList_ofFn` round-trip leaks `Classical.choice`,
so the readback routes through `Array.toList` + `List.ofFn` + `ofFn_concat`
(`Array.toList_append` in the `seq` leaf). The `none`-skeleton of the monadic
`seq`/`alt` cases is bridged by `map_toList_eq_ofFn_none_iff` (`[propext]`-only);
`encodeByteArrayBytes_eq` is `ByteArray.ext` + `List.foldl`-over-`push` projection
(`bpush_data`/`foldl_push_data` — axiom-free) + `foldl_push_append` (`[propext,
Quot.sound]`).

**Decode side — genuine blocker identified (the design's "from scratch" bridge is
real):** `decodeArray_eq`'s `iso`/`alt`/`empty`/`pure`/`byte` cases close cleanly
(the `byte` head read is a `Fin`-index `omega`/`simp` reduction; `consumedAbs_id`/
`consumedAbs_drop_one` are the `@[simp]` consumed-count bridge). The **`seq` case**
requires the invariant that `decode`'s result suffix `t` is a _genuine_ suffix —
`t.bytes = bdrop (n - t.remaining) s` — i.e. a `decode`-level lemma
(`∀ (x, t) ∈ decode d s, t.bytes = bdrop t.consumed s`), **which does not yet
exist**. Without it, `decodeArray d₂ a c₁` (over `bdrop c₁ (arrayToBytes a)`) cannot
be equated with `decode d₂ t₁.bytes` (over `Bytes t₁.remaining`), because
`bdrop c₁ (arrayToBytes a) = cast … t₁.bytes` is not provable for an _arbitrary_
`Suffix t₁` — it is a property of `decode`'s own construction. The transport
lemmas that compose once that invariant exists (`bdrop_add`, the cast-insensitive
`.remaining`, the `consumedAbs` transitivity) are proved and in place; the open gap
is precisely this `decode` genuine-suffix invariant.

---

Added `Codec/Packed.lean` (wired into the `Codec` root) with the packed
carrier **definitions** and a first tranche of clean lemmas, `lake build` green
with zero `sorry`/warnings:

- `decodeArray`, `decodeFullArray`, `encodeByteArrayBytes`, `encodeArray`
  (definitions; the first three re-exported from the root).
- `consumedAbs` (the `Suffix → Nat` consumed-count bridge), `consumedAbs_id`,
  `consumedAbs_drop_one`, and `decodeArray_bounded` (the consumed count is
  monotone: `(x, c) ∈ decodeArray d a i → i ≤ c`). All `#print axioms`
  `[propext, Quot.sound]`-only, zero `Classical.choice`.

**Cursor deviation (surfaced, not silently done):** the carrier is indexed by
`Nat`, **not** `USize` as the task text literally says. Reason: `USize` addition
is `Nat` addition modulo `2^64` (`USize.toNat_add`), and `USize.size = 2^64`
depends on `System.Platform.numBits = 64` — an unproven platform fact in the
stdlib. A `USize`-cursor refinement would carry that premise into every law,
breaking the `[propext, Quot.sound]`-only gate. `Nat` is the same cursor the
committed `fastEncodeRepeat`/`pushBytesFrom` use. The `USize`-lowers-to-`size_t`
scalar claim is therefore unverified here and falls to IR inspection (task 3.1).

**Still open (the "real proof work", per the design):** `decodeArray_eq`,
`decodeFullArray_spec`, `encodeArray_eq`, `encodeByteArrayBytes_eq`. The decode
side needs a from-scratch `Suffix`-transport bridge (`decode` insensitive to a
length cast); the encode side needs an `Array`-`ofFn`-clean readback inversion.
Neither is asserted with `sorry` — they are left as clearly-labeled follow-ups.

**Next-session plan (speed-run implementation first, prove after — gate
provability before volume, so throwaway work is implementation, not proofs):**

1. Spike the encode readback inversion (`arr.toList = List.ofFn s → ⟨arr.size,
fun i => arr[i]⟩ = ⟨n, s⟩` or the `Array.ofFn`-clean equivalent) and confirm it
   closes `[propext, Quot.sound]`-only. This is the gate that decides the encode side.
2. `encodeArray_eq` / `encodeByteArrayBytes_eq` (List-level readback form), then
   `decode_cast` (the `Suffix`-transport bridge) → `decodeArray_eq` →
   `decodeFullArray_spec`.
3. Task 3.1 IR inspection of `.lake/build/ir/Codec/Packed.c` — record (cite) whether
   the `Nat` cursor lowers to `size_t`/bignum; mark the scalar-index premise per the IR.
4. Tasks 4.x (`@[extern]` `byteSlice`) and 5.x (bench + gate) after the Layer-1 laws close.

## 1. Re-derive the packed `USize`-cursor decoder (full backtracking)

- [x] 1.1 Define `decodeArray : Codec α → Array UInt8 → USize → List (α × USize)`: read
      `a[i]` by `USize` index, thread `i + m` through `seq`, `alt` = `++` (union), `seq` =
      `flatMap` cross-product. The result `List (α × USize)` is the non-determinism
      multiplicity (retained); the packed carrier removes only the per-branch
      `Suffix`/`Bytes` closure. No list-peeling. (A greedy variant, if wanted, is a
      separate labeled `decodeGreedy`.)
      _(Defined over `Nat` cursor — the surfaced cursor deviation; see session log.)_
- [x] 1.2 Define `decodeFullArray : … → Option (ByteArray × USize)`: packed suffix, body
      `ByteArray.mk ((a.data.toList.drop i.toNat).toArray)` (list-materializing transport,
      **not** `copySlice`/`extract`), never `Option (List α × Suffix n)`.
      _(Defined; cursor is `Nat`.)_
- [ ] 1.3 Re-prove `decodeArray_eq` and `decodeFullArray_spec` against
      `decode : … → List (α × Suffix n)` **from scratch**: reconstruct
      `{ remaining := n - c, hle := Nat.sub_le n c, bytes := bdrop c s }` from the consumed
      count `c`, plus a proof `c ≤ n` (the cursor bound). `[propext, Quot.sound]`-only,
      zero `Classical.choice`, zero `sorry`.

## 2. Re-derive the packed encoder

- [x] 2.1 Define `encodeArray : Codec α → α → Option (Array UInt8)` accumulating with
      `ByteArray.push` (amortized O(n)); for the byte-sequence shape define
      `encodeByteArrayBytes : List UInt8 → ByteArray` (a `List UInt8` packer, **not** a
      general `Codec α` encoder).
- [x] 2.2 Re-prove `encodeArray_eq` / `encodeByteArrayBytes_eq` against `encode`, reusing
      the clean readback lemmas already in `Codec/Encode.lean` (`list_ofFn_getElem_clean`,
      `ofFn_concat`, `pushBytesFrom_eq`, `array_readback`). `[propext, Quot.sound]`-only.

## 3. Confirm the `USize` scalar claim by IR inspection

- [ ] 3.1 Inspect the emitted `.c` and record, with citations, that the `USize` cursor
      lowers to a `size_t` loop with no `lean_alloc`/box per node. Assert nothing; cite
      the IR. If it does **not**, record that and mark the "no backend" premise as false.

## 4. Layer 2 — the `@[extern]` named trust seam

- [ ] 4.1 Re-introduce `byteSlice (a : ByteArray) (i : USize) : ByteArray` (a `memcpy`-
      style suffix copy; it does not exist in the current tree) as a fresh `@[extern]`
      seam, wired onto a packed path (never a `List`-re-materializing consumer).
- [ ] 4.2 Document the trust contract verbatim (F\*-vs-KaRaMeL); **exclude** Layer 2 from
      the `#print axioms` gate.

## 5. Bench and gate

- [ ] 5.1 Run the current `bench`, record the actual numbers (Layer 1 lanes, Layer 2
      `byteSlice`, and the `memcpy` calibration) as the single source of truth. Tag each
      `[measured]` (or `[historical]`/`[target]` as applicable). Do **not** hand-copy any
      figure from a prior draft.
- [ ] 5.2 `lake build` zero `sorry`/warnings; `#print axioms Codec.roundtrip` ⇒
      `[propext, Quot.sound]`; every Layer-1 law `#print axioms`-verified `[propext,
  Quot.sound]`-only. Bench byte-exact value checks (not length checks).
- [ ] 5.3 Update `Bench.lean`, `README`, `AGENTS` to state the two layers honestly, the
      named trust seam, and the "result carrier, not the byte loop" lesson — preserving the
      `[D#]`/`[S#]` anchors.
