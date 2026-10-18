# Tasks

## 1. Single-valued `decode` (committed `|`)

- [ ] 1.1 Rewrite `decode : Codec α → {n : Nat} → Bytes n → Option (α × Suffix n)`
      — committed `alt` (first success), no `List`, no backtracking union.
- [ ] 1.2 Keep `encode : Codec α → α → Option (Σ n, Bytes n)` unchanged.
      Update `Codec.alt` docstring text to committed-choice semantics.

## 2. Delete the relational band-aids

- [ ] 2.1 Remove `Functional`, `Unambiguous`, `relFunctional`, `relUnambiguous`
      (`Sound.lean` ~534–622); remove `encode_ne_none` (absorbed into the
      unconditional laws).

## 3. Re-derive the laws as unconditional `Option` equalities

- [ ] 3.1 `roundtrip : encode d x = some ⟨n, s⟩ → decode d s = some (x, Suffix.empty n)`.
- [ ] 3.2 `decode_of_encode : decode d s = some (x, Suffix.empty n) → encode d x =
    some ⟨n, s⟩` (unconditional).
- [ ] 3.3 `encode_injective : encode d x = encode d y → x = y` (unconditional).
- [ ] 3.4 Re-state `bidir`/`decode_spec` over `some`/`none` (committed `alt`).

## 4. Repetition + combinators over single-result `Option`

- [ ] 4.1 Re-shape `decodeRepeat`/`encodeRepeat`/`decodeFull` to the
      single-result `Option`/committed-`|` shape.
- [ ] 4.2 Update `Combinators.lean` (`many`, `*>`, `<*`, …) to the committed
      `alt`/`Option` shape.

## 5. Concrete codecs become `Codec` values

- [ ] 5.1 Refactor `basen`'s `base16/32/64/…` into `Codec …` values composed from
      `byte`/`seq`/`iso`/`alt`/`many`; delete the bespoke `encode`/`decode`
      (`List UInt8 → Option (List UInt8)` etc.).
- [ ] 5.2 Prove each base's roundtrip through the inherited `Codec.roundtrip`, and
      each base's rejection (`decode base16 bad = none`) through the shared `decode`.

## 6. Demonstrate + gate

- [ ] 6.1 A compilable `#eval` demo: encode a value, decode it back
      (`decode c (encode c x) = some …`), plus a `none` case on a bad input.
- [ ] 6.2 `lake build` zero `sorry`/warnings; `#print axioms Codec.roundtrip` and
      the new laws = `[propext, Quot.sound]`; `nix flake check` green; commit +
      push.
