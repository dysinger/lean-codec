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

## 3. `basen` bases composed from `satisfy`/`count`/`iso` + the proven repetition layer

> **Note (2026-10-19):** tasks 3.x/4.x do **not** require a `many` constructor.
> The variable-width run primitive is `takeWhile p` (the already-landed
> `satisfy_many0` analogue), and `many` stays out of the AST — per the paper
> (§3.4: `many` is a derived combinator) and the F* reference (`satisfy_many0`
> scans the finite input, no `Productive` witness). See the design supersede.
>
> **Shape per base (fixed-width):** an _element_ `Codec UInt8 := iso <blockIso>
(count k (satisfy <digitPred>))` — `k` digits → one byte — plus the unbounded
> **run** triple `relBase := relRepeat (Rel elem)`, `decodeBase := decodeRepeat
elem <consumeWitness>`, `encodeBase := encodeRepeat elem`; the roundtrip is the
> **inherited** `decodeRepeat_spec`/`encodeRepeat_rel` law. `elem`'s productivity
> witness is one `ConsumesByte` proof (each step consumes exactly `k` bytes).
>
> **Boundary:** the `Bytes n ↔ List UInt8` bridge is `BaseN.Bridge` (landed).

- [x] 3.0 Add the `BaseN.Bridge` `Bytes n ↔ List UInt8` module (landed).
- [ ] 3.1 **Base8** (simplest fixed-width: 3 octal digits/byte) — establish the
      template: `octElem : Codec UInt8` (3-char `iso`+`count`), `octConsumesByte`,
      run triple, `roundtrip` inherited. `lake build` green.
- [ ] 3.2 **Base2** (8 bits/byte) — `count 8 (satisfy bitChar)` + `bitsVal`/`bitsOf`
      `iso`; run triple; roundtrip inherited. Delete bespoke `encode`/`decode`.
- [ ] 3.3 **Base4** (4 quartets/byte) — mirror Base8 with 4 chars/byte.
- [ ] 3.4 **Base10** (decimal digits/byte, variable width but byte-oriented) —
      `satisfy isDigit` run + block `iso` (no `=` padding).
- [ ] 3.5 **Base16** (2 hex digits/byte) — `count 2 (satisfy isHexDigit)` + pair/byte
      `iso`; run triple; roundtrip inherited. Delete bespoke `encode`/`decode`.
- [ ] 3.6 **Base32** (5-bit alphabet, `=` padding) — alphabet run + block `iso` +
      terminal-pad `alt` preserving 5.1 (`rest = []`).
- [ ] 3.7 **Base64** (6-bit alphabet, `=` padding) — same as Base32 with 64-alphabet.

## 4. Facade + bench + gate

- [ ] 4.1 `BaseN.lean` facade re-exports the seven `Codec` values / run triples.
- [ ] 4.2 `Bench.lean` calls `Codec.decode`/`decodeRepeat` per base; byte-exact
      vectors still `rfl`.
- [ ] 4.3 `lake build` zero `sorry`/warnings; `#print axioms` `[propext,
Quot.sound]` for every law; `nix flake check` green; commit + push.

## Non-Goals (permanent)

- No BE/LE/fixed-width/`varint`/text/tagged-`sum`/lookahead in core; no
  `decode`/`encode` result-shape change; no error-position type.
