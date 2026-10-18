# Tasks

## 1. Deduplicate the full-consumption decoder (DecodeByteArray)

- [x] 1.1 Re-expressed `decodeFullByteArray p h a i = decodeFullArray p h a.data i` (composed
      through the reducible `ByteArray.data`); deleted the duplicated `decodeFullByteArray_lt` /
      `decodeFullByteArrayStep` / `decodeFullByteArrayStep_some` / `decodeFullByteArrayStep_ne_none` /
      `decodeFullByteArray_some` / `decodeFullByteArray_ne_none` locals (plus the
      `mem_decodeByteArrayRel_to_decode`/`_of_decode`/`drop_of_mem_decode_byteArray`/`decodeByteArrayRel_pos`/
      `_le_size`/`_bounds` lemmas) — ~320 → ~39 lines. The native _read_ recursion
      `decodeByteArrayRel` is left native (where the O(1) packed read wins).
- [x] 1.2 Transferred `decodeFullByteArray_spec` from `decodeFullArray_spec` in one reduction
      over `a.data` (preserving the exact `_spec` statement for `ExternFastPath.lean`).
- [x] 1.3 `lake build` clean, zero warnings/sorries; `#print axioms decodeFullByteArray_spec`
      = `[propext, Quot.sound]` (same as `decodeFullArray_spec`).

## 2. Tighten the `@[extern]` trust seam

- [x] 2.1 Documented the scalar/`USize`-representable index domain on `byteSlice` and
      `byteSlice_data_toList` docstrings (the bignum-index ⇒ empty-suffix coincidence is
      now explicit in both the `.lean` side and the law statement).
- [x] 2.2 No C change (mechanism-only seam); the `slice-returning-run-model`
      `USize`-indexed entry point is noted in the `byteSlice` docstring as the
      structural fix.

## 3. Varint uniqueness structural (`Option`)

- [x] 3.1 Change `decodeVarint : ByteArray → Nat → Option Nat` (drop the redundant `j`),
      proved via the existing membership lemmas.
- [x] 3.2 Re-state `decodeVarint_eq`/`roundtripVarint` as `Option` equations projecting
      through the `List`-membership result; keep `varint`/`varintBytes` spec unchanged.
- [x] 3.3 Update `Bench.lean` varint legs (if any reference the list) to project the
      single result; `lake build bench` still links.

## 4. Minor clarity/naming nits

- [x] 4.1 `encodeBuffer_eq`: kept the convention-consistent statement (`b = Buffer.ofBytes l`,
      matching `decodeBuffer_eq`'s `r' = Buffer.ofBytes r`); added a docstring note
      explaining the convention. The `rw [eq_comm]` is retained as the clearest close
      (the reconstructed value naturally sits on the RHS); no behavioral change.
- [x] 4.2 `byte_consumesByte`: no rename needed (snake_case theorem, consistent with
      `decode_spec`/`encode_rel`); its docstring already states "the `ConsumesByte
  Codec.byte` witness", which is the framing the review flagged as ambiguous.

## 5. Gate

- [x] 5.1 `lake build` clean (zero `sorry`/warnings); `lake build bench` links.
- [x] 5.2 `#print axioms` on `Codec.roundtrip`, `Iso.foldl`, `Iso.foldr`,
      `decodeFullByteArray_spec`, `roundtripVarint` — all `[propext, Quot.sound]`-only.
- [x] 5.3 No public denotation/law statement changes (`decode_spec`, `bidir`, `roundtrip`,
      chain laws, and `decodeFullByteArray_spec` all byte-identical to before).
