# Design note — the fifth move is not a carrier, it is a return-type decision

> Status: proposal-level design note for the _next_ change. Written before the
> openspec planning artifacts, so the proposal/design/tasks below can be authored
> against a concrete decision rather than re-litigated.

## The four carriers that came before, and why #5 is different

The repository has tried, in order, four **result carriers** for the interpreter:

1. `List UInt8` (the original paper spec substrate),
2. `Buffer`/`ByteArray` (`buffer-carrier-decoders` → `bytearray-carrier-decoders`),
3. `Bytes n := Fin n → UInt8` (`single-carrier-bytes`),
4. the packed `Array UInt8` / `Nat`-cursor carrier (`carrier-performance-tuning`, active).

All four share one property, and it is the property that caps them all at the same
place: **they return a pure, immutable, length-indexed value.** The bulk write is
therefore always a _per-element_ append/cons/closure into a pure value, and a pure
value cannot be produced by `memcpy` — `memcpy` needs a pre-sized **contiguous
mutable buffer**, which is a different kind of thing than a pure carrier.

Measured (`./.lake/build/bin/bench`, `[measured]`):

- `encodeRepeat` (pure spec, carrier #3) — **~31 MiB/s**, flat across sizes;
- `fastEncodeRepeat` (Layer-1 packed, carrier #4) — **~42 MiB/s**;
- `encodeRepeat iso` (the _same byte loop_, carrier bookkeeping elided) — **~750 MiB/s**;
- `byteSlice` (the `@[extern]` `memcpy`) — **~80 GiB/s**;
- `calib memcpy` — **~53 GiB/s** (full-buffer copy).

The gap between 42 MiB/s and 750 MiB/s is the _return carrier_, not the byte loop
(the thesis of the active change, confirmed). The gap between 750 MiB/s and 80 GiB/s
is a _category_ gap, not a speed gap: a pure fold cannot reach a `memcpy`, and no
fifth pure carrier will close it.

**Conclusion.** Carrier #5 — a _fifth_ pure carrier — would fail for exactly the
reason carriers #1–#4 did. The next move is **not a new carrier**; it is a
**return-type and proof-position decision**: stop returning the pure `Bytes n`
carrier on the hot path, and let `byteSlice` be the single trusted `memcpy` in a
`ByteArray`-returning path.

## The decision (the one thing this note pins down)

Two invariants must hold, and they force the shape:

1. **The specification never changes.** `decode`/`encode`/`decodeFull`/`encodeRepeat`
   stay `Bytes n`-typed, with their `[propext, Quot.sound]`-only laws untouched.
   `Bytes n` is the _denotation_; it is not on trial again.

2. **The only trusted step is `byteSlice`.** Every other step of the fast path is
   proved `[propext, Quot.sound]`-only; the refinement lemma's _sole_ non-proven step
   is the `byteSlice = extract` contract, which is the named Layer-2 trust seam
   (excluded from the `#print axioms` gate, per the active change's two-layer rule).

Given those, the decision is:

**The packed fast path returns `ByteArray`, not `Bytes n`.** The refinement lemma
equates the fast path to the spec _up to the `byteSlice`/`Array.extract` readback_,
never by reconstructing a pure `Bytes n` on the hot path.

## The concrete return types (to be written into the proposal/spec)

Current (unchanged, spec — the `Bytes n` denotation):

```lean
decode      : Codec α → {n} → Bytes n → List (α × Suffix n)      -- value + remainder
decodeFull  : Codec α → ConsumesByte p → (n : Nat) → Bytes n → Option (List α)
encode      : Codec α → α → Option (Σ n, Bytes n)
encodeRepeat: Codec α → List α → Option (Σ n, Bytes n)
```

Current (unchanged, the **proven** packed carrier — Layer 1, from the active change):

```lean
decodeArray     : Codec α → Array UInt8 → Nat → List (α × Nat)      -- value + consumed Nat
decodeFullArray : Codec α → Array UInt8 → Nat → Option (ByteArray × Nat)  -- suffix + consumed, NO α
encodeArray     : Codec α → α → Option (Array UInt8)                -- contiguous buffer, already packed
```

Note a deliberate asymmetry already present in Layer 1: `decodeArray` returns the
value `α` **plus** the consumed count (needed for `seq` cross-product), but
`decodeFullArray` returns **only** the suffix `ByteArray` + consumed `Nat` — the
decoded value `α` is _dropped_ (full consumption means there is nothing to thread
onward). `encodeArray` returns the contiguous buffer; the input `α` is a parameter,
not part of the result.

New (Layer-2 fast path, distinct names — never `decode`/`encode`):

```lean
-- full-consumption, packed, returns the contiguous suffix directly (one memcpy)
decodeFullArrayFast : Codec α → Array UInt8 → USize → Option (ByteArray × USize)
-- encode, packed, returns the contiguous buffer directly (already the carrier)
encodeArrayFast     : Codec α → α → Option ByteArray
```

where:

- `decodeFullArrayFast d a i` runs the packed decoder (the `Nat`-cursor `decodeArray`),
  takes the **first** full-consumption match (the existing `decodeFullArray`
  head-projection), and materializes its suffix as `byteSlice a c` — **not**
  `ByteArray.mk ((a.toList.drop c).toArray)`. It keeps the existing `decodeFullArray`
  result shape `(ByteArray × consumed)`, so the _only_ change vs Layer 1 is the body
  of the suffix: a trusted `memcpy` instead of a `List.toArray.drop` fold.
- `encodeArrayFast d x` is the existing `encodeArray` (already `Option (Array UInt8)`),
  wrapped as `Option ByteArray` via `ByteArray.mk`.

Both keep the Layer-1 signatures' result _skeleton_; they change only the suffix /
packing materialization from a pure fold to a trusted `memcpy`. No new carrier type
is introduced — `ByteArray` is already the packed result type in Layer 1.

## The single refinement lemma (the only new proof work)

```lean
theorem decodeFullArrayFast_spec (d : Codec α) (a : Array UInt8) (i : USize) :
    decodeFullArrayFast d a i
      = (decodeFullArray d a i.toNat).map
          (fun (suffix, c) => (byteSlice (ByteArray.mk suffix) 0, c))
```

Hmm — the precise form depends on whether `decodeFullArrayFast` is defined _over_
`decodeFullArray` (composing `byteSlice` outward) or _as_ a copy of `decodeFullArray`
with the suffix body swapped. The honest statement for the notes author is:

- If `decodeFullArrayFast d a i := (decodeFullArray d a i.toNat).map (fun (s, c) =>
(byteSlice s 0, c))`, then the refinement is definitional up to `byteSlice`'s own
  contract, and the law to state is exactly the trust seam:

  ```lean
  byteSlice b i = ByteArray.mk (b.data.extract i.toNat b.data.size)   -- the trust contract
  ```

  — which is the named Layer-2 seam, **excluded** from the `#print axioms` gate (it
  appears on the RHS as an uninterpreted `@[extern]`; no `[propext, Quot.sound]` law
  is proved _through_ it).

- If `decodeFullArrayFast` instead replaces the _body_ of `decodeFullArray`'s suffix
  (so the two are not definitionally related), the law is `decodeFullArrayFast d a i
= (decodeFullArray d a i.toNat).map (fun (s, c) => (byteSlice s 0, c))`, proved by
  `decodeFullArray`'s existing `decodeFullArray_spec` + the `byteSlice` trust
  contract — the _only_ non-`[propext, Quot.sound]` step being that contract.

The proposal must pick one of these two shapes and state it. The design note records
both as options precisely so the proposal does not silently choose the easy one
(definitional-transparent, which hides the `byteSlice` call from `#print axioms` and
could be misread as "no trust").

### A sharper observation the proposal must confront

`decodeFullArray d a i : Option (ByteArray × Nat)` **already returns the
full-consumption suffix as a `ByteArray`** (via `ByteArray.mk ((a.toList.drop
c).toArray)`). So for _full consumption_ there is no remainder to slice — `byteSlice`
adds nothing there, and `decodeFullArrayFast` would be a pure re-type of
`decodeFullArray` (ignoring the `Nat → USize` cursor), not a real `memcpy` win.

`byteSlice`'s natural consumer is the **partial** decode: `decodeArray d a i : List (α ×
Nat)` returns `(value, consumed)` where the _remainder_ `[c, a.size)` still has to be
sliced out of the contiguous buffer to hand back a `ByteArray` remainder. That is the
one place a `memcpy` suffix copy is actually required — and it is currently **not**
presented anywhere in the API (the active change ships only the full-consumption
`decodeFullArray`, which materializes the whole suffix by `List.toArray.drop`, not by
`byteSlice`).

The proposal must therefore answer a question the note has _not_ decided: **does the
next change add a partial-decode `fast` surface — e.g.
`decodeArrayFast : Codec α → Array UInt8 → USize → List (α × USize)` where each
yielded remainder is `byteSlice a c` — or does it only re-type the full-consumption
case (where `byteSlice` is a no-op and the honest result is "no further win without a
partial remainder surface")?** The benchmark predicate in the next section should be
restated against whichever of these is chosen, because the `byteSlice` floor is only
reachable from a partial remainder.

## What this note deliberately does NOT decide (leave for the proposal)

- The _exact_ name (`decodeArrayFast` vs `decodeSuffix` vs `decodeRemainder`), and
  the **partial-remainder return type** if the partial surface is chosen — most likely
  `List (α × USize)` (value + consumed `USize` cursor) with the `ByteArray` remainder
  obtained by a separate `byteSlice a c`, versus `List (α × (ByteArray × USize))`
  (value + already-sliced remainder). The latter bakes one `byteSlice` per result
  into the decoder; the former leaves the caller to slice. The proposal must pick
  one and justify it against the benchmark predicate (a per-result `byteSlice` may
  dominate and make the "suffix floor" claim misleading when there are many results).
- Whether to keep the `USize` vs `Nat` cursor on the public API (the proof cursor is
  `Nat`; the extern is `USize`; the public wrapper can be either and the proposal must
  pick one and justify it), and whether `byteSlice`'s `USize` index needs a
  `Nat`/`USize` bridge lemma or the wrapper takes `Nat` and does `i.toUSize`
  internally.
- The benchmark predicate that decides success, **restated against whatever surface
  is chosen**: if the partial-remainder `decodeArrayFast` surface is picked, does it
  on a real (non-`byte`-repetition) description come within ~2× of the `byteSlice`
  floor _per yielded result_, and does the per-result `byteSlice` cost stay bounded as
  the number of results grows? If the full-consumption-only surface is picked, the
  honest expected outcome is "no further win over the already-packed `decodeFullArray`",
  and the note records that as a _possible conclusion_, not a failure to paper over.

## Why this is the right framing (and not "carrier #5")

The four carriers answered the question "which pure value should the interpreter
return?" and the answer is now closed: _any_ pure value caps at the accumulator floor,
and `memcpy` lives only behind a trusted `@[extern]`. This move is the smallest change
that uses that answer: keep the spec, keep the proven packed decoder, and let the one
trusted `memcpy` (`byteSlice`) produce the one contiguous result a `memcpy` can
produce. It is a **return-type + wiring** change, not a carrier change.
