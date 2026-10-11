# Design

## Context

The proven core (`Codec/Decode.lean`, `Codec/Encode.lean`) is the *specification*:
`decode d s : List (α × Bytes)`, `encode d x : Option Bytes`, over `Bytes = List UInt8`.
The §4.4/§10.5/Tier-A work (`efficient-backtracking-decoder`) fused the interpreters
(`decodeFast`, `decodeFull`) but left them on the `List` substrate — every byte is a
cons cell, so the running cost is bounded below by list allocation, ~30–100 ns/byte.
`Codec/Buffer.lean` already ships `Buffer` (a `ByteArray` newtype) and `decodeBuffer`/
`encodeBuffer`, but those *compose* `decode`/`encode` with a `toBytes`/`ofBytes`
transport — they still materialize the full `List` and run the list interpreter on it.
The byte-list cost is untouched.

This is precisely the F\* two-tier situation. F\*'s spec is a pure `Seq`; its run-model
is `LowStar.Buffer` + an index; the proof is *one refinement lemma* (`impl ≡ spec ∘ view`),
and every spec law transfers. The Lean analogue is `Array UInt8` (reachable through the
reducible `ByteArray.data`, which is why `Buffer.toBytes` already routes that way): an
`Array` reduces to its `List` content (`a.data`), so equality proofs stay `rfl`/`simp`/
`induction`. This change supplies the missing half — a native, indexed array recursion —
and proves it equal to the list spec.

## Goals / Non-Goals

**Goals:**

- Define `decodeArray` (indexed, `Array UInt8`-carrier, remainder as `Nat`) and
  `encodeArray` (`Array UInt8`-accumulating) as the *run-model*, structurally identical
  to `decode`/`encode` but never cons-peeling a `Byte` list.
- Prove, once, `decodeArray_eq` / `encodeArray_eq` against the list spec, in the core's
  `rfl`/`simp`/`induction` style (`[propext, Quot.sound]`, no `Classical.choice`).
- Transfer every existing unconditional law by rewriting (no new induction).
- Measure the carrier swap in `Bench.lean` against the §10.5/Tier-A baselines.

**Non-Goals:**

- No FFI/`extern`, no code generator, no `HashMap`, no SIMD, no chart parser. The
  "fastest possible" tier is explicitly deferred to a later change once there is real
  usage. (Decision 1 in `AGENTS.md` — "Bytes for proofs, Buffer for transport" — is
  extended, not reversed: `Bytes` remains the only proof substrate; `Array` is a
  *proved-equal run-model*.)

## Decisions

1. **`Array UInt8`, not `ByteArray`, is the run-model carrier.** `Array.toList`/`List.toArray`
   and `a.data` reduce under `simp`/`rfl`, so the equality proofs stay mechanical;
   `ByteArray` itself is FFI-opaque (the §2 `lean`-skill lesson) and would stall every
   law. Touch `ByteArray` only at the outermost `Buffer` boundary (already done in
   `Buffer.lean`), and reach it via `ByteArray.data`.
1. **The remainder is a `Nat` index, not a byte list.** `decodeArray d a i : List (α × Nat)`
   where the `Nat` is the position after the match. This avoids re-slicing/extracting an
   `Array` per step (which would re-allocate). The equality law re-phrases the index as a
   `List.drop`: `(x, j) ∈ decodeArray d a i ↔ (x, a.data.drop j) ∈ decode d (a.data.drop i)`
   (the clean, transfer-friendly form), or the function-level `decodeArray_eq : decodeArray d a i = (decode d (a.data.drop i)).map (map remainder to index)` when the index/remainder
   correspondence is total.
1. **Equality is denotational, not definitional (same rule as Tier A).** `decodeArray_eq` is
   a theorem proved by induction on `d` + `Array`/`List` lemmas (`Array.getD_eq_data_get?`,
   `Array.data_drop`, `List.map_*`). Never a `[irreducible]` `partial`; never `simp [decodeArray]`
   on a recursion equation (the §2 `WellFounded`/`fix_eq` lesson applies to any array recursion
   over `Nat`).
1. **Repetition over the array carrier gets its own full-consumption law, in the same shape as
   Tier A.** `decodeFullArray p h a i : Option (List α × Nat)` (or the `Option (List α)` +
   index form) mirrors `decodeFull`, well-founded on the *remaining* length `a.size - i`, so it
   inherits the `decodeFull_spec` full-consumption-uniqueness hypothesis (`huniq`). This is the
   carrier-swapped analogue of the just-archived `decodeFull`/`decodeRepeatFull`.
1. **The transfer laws live in `Sound.lean` and are one-line rewrites.** `decodeArray_spec`,
   `encodeArray_rel`, `roundtripArray`, `decodeArrayFull_spec` — each `rw [<the>_eq]` then the
   existing law. No new induction, matching the `decodeFast_spec`/`bidir_decodeFast` pattern.

**Alternatives considered:**

- *Change `decode`/`encode` themselves to `Array`.* Rejected — `Bytes = List UInt8` is the
  proof substrate (decision 1, AGENTS.md); swapping the spec's carrier would force every one
  of the ~30 existing `Bytes`-level laws to be re-stated. Additive, proved-equal run-models
  keep the spec frozen.
- *Use `ByteArray` + `offset` directly.* Rejected — `ByteArray` ops (`.get!`, `.extract`) are
  FFI-backed and opaque to `simp`/`rfl` (the `lean`-skill §2 lesson); the equality proof would
  become a buffer-invariants argument far heavier than the `Array`↔`List` reformulation.
- *Skip `encodeArray`, decode-only.* Rejected — roundtrip needs both directions on the carrier;
  encoding is the cheaper half (`encode` already appends, only the accumulator type changes) and
  its `_eq` law is structural-induction on `d` plus `List.append`↔`Array.push` lemmas.

## Risks / Trade-offs

- *\[`Array` indexing proves hairier than `List` cons\]* → Use `getD` (total) or `getElem` with an
  explicit `i < a.size` obligation, and keep the remainder-`Nat` so `a.size - i` is the only
  well-founded measure. If a step stalls, fall back to expressing `a[i]` as `a.data[i]` and proving
  via `List.drop`/`get?` lemmas, matching the core's existing tactics.
- *\[The `map`-index correspondence in `decodeArray_eq` needs a small lemma\]* → State the law in the
  membership form first (`(x, j) ∈ decodeArray … ↔ … drop …`), which is what the transfer lemmas
  actually consume, and derive the function-level form only if it's `rfl`-clean.
- *[The speedup may under-deliver vs. expectations]* → The win is bounded by how much of the hot
  path is list-allocation; expect ~5–20× (not the Tier-A ~20000×, which was removing Θ(n²)). The
  measurement leg makes the real number explicit rather than promised.

## Migration Plan

Additive only: a new module under `Codec/` + transfer lemmas in `Sound.lean` + `Bench.lean` legs.
No existing symbol changes signature; `Buffer`/`decodeBuffer`/`encodeBuffer` are untouched but can
later be re-expressed as `decodeArray` (the packed `ByteArray` fed through `.data`) — noted, not done
here. Rollback = revert the new module + bench legs.

## Open Questions

- Whether `encodeArray` should accumulate into a single `Array` by `push` (O(n²) without amortization
  guarantees in the *proof* model) or keep an `Array` + explicit `push` list and fold at the end.
  The decoder (index +=1, no reallocation) is clearly O(n); the encoder's accumulator is the one
  place to be careful, and it can stay `List`-accumulating internally and materialize the `Array`
  once — the carrier win is on the *decode* hot path, which is where parsing lives.
