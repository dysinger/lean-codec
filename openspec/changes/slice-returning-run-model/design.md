# Design

## Context

The `bytearray-carrier-decoders` change shipped a **native** `ByteArray` run-model
(`decodeByteArray`/`decodeFullByteArray`/`encodeByteArray`) proved equal to the
`Bytes` spec `[propext, Quot.sound]`-only. Its internal decoder
`decodeByteArrayRel` already reads `a[i]` by index (the O(1)
`lean_byte_array_fget`) and threads `i + m` through `seq` — it never cons-peels a
list. The _only_ `List` cost is the **boundary**: `decodeByteArray d a i :=
(decodeByteArrayRel d a i).map fun (x,n) => (x, i+n)` materializes a
`List (α × Nat)`, and `decodeFullByteArray` builds an `Option (List α × Nat)`.

Two failed attempts established where the cost is _not_:

1. `extern-c-fast-path` (shipped, then corrected): hand-written `@[extern]` C was
   a shim over stdlib externs (`byteSlice` = suffix `copySlice`,
   `encodeAppend` = `byte_array_push`); it removed no cost because the byte loop
   was already C.
2. `compiler-tier-extraction` (archived as unsound): "erase `Nat→size_t` and
   `WellFounded.fix`→loop" is a semantic change Lean's IR cannot express
   (`Nat` is a bignum `lean_object *`, not a scalar; `decodeFullByteArray`'s
   `WellFounded.fix` is a backtracking search threading an `ih` continuation, not
   a tail loop).

So the lever is neither C nor the compiler. It is the **result carrier**: return
a packed `ByteArray` span, not a `List`.

## Goals / Non-Goals

### Goals

- A **slice-returning decode** whose `byte` case is O(1) (one indexed read +
  index increment) and whose full-consumption case returns the packed suffix in
  **one** `ByteArray` copy — no `List` cons, no `Nat` box per element.
- A **packed, amortized-O(n) encode** accumulator (replace the O(n²)
  `List.append` fold).
- **Prove each equal** to the existing `Bytes` spec refinement, `[propext,
Quot.sound]`-only, reusing `decodeByteArrayRel_eq` / the `foldl push`
  lemmas — no new axiom.

### Non-Goals

- **Not** a compiler backend (archived: `compiler-tier-extraction`).
- **Not** more `@[extern]` C (the stdlib already owns the byte loop).
- **Not** changing `Codec`/`Rel`/`decode`/`encode`/`Sound`, the `Bytes`
  substrate, or any law. The `List` APIs stay as the proved _spec_.
- **Not** a proof that the C compiler's output refines the source (that was the
  unsound plan); this change is a _type-level_ carrier swap inside Lean.

## Decisions

1. **The fast surface returns a packed `ByteArray` span, not a `List`.** The
   decode result is a sub-view (start index + consumed length, or a
   `ByteArray.extract` at the boundary), so the `byte` hot loop lowers to
   `lean_byte_array_fget` + `size_t` arithmetic under the _existing_ `EmitC` —
   near-C with no backend. The `List` APIs remain for callers that genuinely
   pattern-match elements.

2. **Index with `USize` (or a machine-int abstraction) in the new surface.** This
   is the decisive fix the failed plans missed: `USize` _is_ a scalar in Lean's
   IR (unlike bignum `Nat`), so the existing emitter already prints a
   `ulong`/`size_t` loop with no representation fiction. The refinement to the
   `Nat`-indexed spec is a one-line `USize.toNat` correspondence.

3. **Zero-copy is the win; make its lifetime a named trust seam.** The slice
   aliases the source `ByteArray`'s `data`. Lean's value model has no observable
   aliasing, so this is recorded as a **documented contract** ("the span is valid
   while the source `ByteArray` is referenced; the C symbol must not
   `lean_dec_ref`/realloc the source within that span") — the same named-trust
   posture as the `@[extern]` seam, at the buffer edge, not a new proof axiom.

4. **Encode: `ByteArray.push` fold, proved = `List.toArray`.** The
   `foldl_push_toArray` / `foldl_ba_push` lemmas already in
   `Codec/ExternFastPath.lean` close this; promote them to the committed surface
   (drop the misleading "extern" framing — `ByteArray.push` is the stdlib
   extern, no custom C needed).

## Risks / Trade-offs

- _[Zero-copy span dangles]_ → documented named-trust contract (Decision 3); the
  bench lane checks byte-exact output, and refinement pins the _meaning_, not the
  aliasing.
- _[`USize` vs `Nat` mismatch]_ → the correspondence lemma is a finite
  `USize.toNat` fact; the `Nat`-indexed spec is unchanged.
- _[Callers that need `List`]_ → the `List` API is unchanged; the slice surface
  is additive.
- _[The speedup still isn't `memchr`-class]_ → honesty: the goal is to remove the
  `List`/`Nat`-boxing cost; if the packed copy itself is the floor, that's
  measured and recorded, not papered over.

## The primitives (concrete surface)

```lean
-- zero-copy span decode (byte case: one a[i] read + index increment)
decodeByteArraySlice (d : Codec α) (a : ByteArray) (i : USize) :
  Option (α × USize)  -- value + consumed count, source `a` aliased

-- full-consumption byte span: packed suffix + length, no List
decodeFullByteArraySlice (a : ByteArray) (i : USize) :
  Option (ByteArray × USize)

-- packed encode accumulator (amortized push, not List.append)
encodeByteArrayBytes (xs : List UInt8) : ByteArray
```

Each `def` elaborates (so refinement lemmas reduce), and each carries a
`_eq`/`_spec` law closing against the existing `decodeByteArray_eq` /
`decodeFullByteArray_spec` / `encodeByteArrayBytes_eq`.
