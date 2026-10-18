# Tasks

## 1. Core: add `satisfy`

- [x] 1.1 Add constructor `satisfy : (UInt8 → Bool) → Codec UInt8` to
      `Codec/Codec.lean`.
- [x] 1.2 Add the `Rel`/`decode`/`decodeFast`/`encode` cases for `satisfy`
      (`Rel (satisfy p) b s = p b = true ∧ s = single b`; decode one byte iff
      `p b` else `[]`; encode iff `p b` `some ⟨1, single b⟩` else `none`).
- [x] 1.3 Extend the `Sound` laws (`decode_spec`, `bidir`, `roundtrip`,
      `encode_rel`) with the `satisfy` case; `[propext, Quot.sound]`-only, zero
      `sorry`. Gate `lake build` + `#print axioms Codec.roundtrip`.

## 2. Derived run combinator

- [x] 2.1 Add `takeWhile p` / `many (satisfy p)` as a derived combinator using
      `decodeRepeat`/`encodeRepeat` (no new constructor), for alphabet runs and
      variable-length tokens (varint, UTF-8).

## 3. `basen` bases as `Codec` values

- [ ] 3.1 `base16 : Codec (List UInt8)` — `satisfy isHexDigit` run + pair/byte
      `iso`, single-digit decode honored.
- [ ] 3.2 `base2/4/8/10` as `Codec (List UInt8)` values (fixed-width digit
      `count`/`iso`).
- [ ] 3.3 `base32/base64 : Codec (List UInt8)` — alphabet `satisfy` runs + block
      `iso` + pad `alt`, preserving the 5.1 terminal-padding (`rest = []`).
- [ ] 3.4 Delete the seven bespoke `encode`/`decode` + duplicated `Nat↔UInt8`
      lifts; each base's roundtrip is `Codec.roundtrip`.

## 4. Facade + bench + gate

- [ ] 4.1 `BaseN.lean` facade re-exports the seven `Codec` values.
- [ ] 4.2 `Bench.lean` calls `Codec.decode baseXCodec …`; byte-exact vectors
      still `rfl`.
- [ ] 4.3 `lake build` zero `sorry`/warnings; `#print axioms` `[propext,
  Quot.sound]` for every law; `nix flake check` green; commit + push.

## Non-Goals (permanent)

- No BE/LE/fixed-width/`varint`/text/tagged-`sum`/lookahead in core; no
  `decode`/`encode` result-shape change; no error-position type.
