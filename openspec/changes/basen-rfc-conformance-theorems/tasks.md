# Tasks

> **Surface (read first):** all seven bases are `Codec` values over
> `satisfy`/`count`/`iso` + the productive repetition layer (`basen-uniform-leaf-api`,
> archived). The whole-input decoder is `Codec.decodeFull {x}Elem {x}ConsumesByte`
> (fixed-width bases, result `List UInt8`) and
> `Codec.decodeFull b32Elem b32ConsumesByte` / `b64Elem b64ConsumesByte`
> (block bases, result `List (List UInt8)`); the encoders are `encode{X}` /
> `encodeB{X}` over the `Bytes n` substrate. There is **no** bespoke
> `encode : List UInt8 → List UInt8` / `decode : List UInt8 → Option (List UInt8)`
> facade. Every statement below uses the `decodeFull`/`encode` surface.
> **Base16 is uppercase-only** (`hexElem` is a strict `0-9A-F` bijection);
> lowercase `6f` is **not** a vector here — case-insensitivity is a non-goal
> (design D8).

## 1. Run-level terminal padding (the one code defect)

The block `iso` already rejects `=` in a non-terminal _intra-block_ position
(`b32BlockApply`/`b64BlockApply` re-check `…Unapply bs = some cs`). At the _run
level_, the current code **accepts** a `=`-terminated block followed by another
block: `count 4 (satisfy b64OrPad)` fixes the 4-byte _window_, not the value
length, so `decodeFull b64Elem … "Zg==AAAA"` is `some […]`. A guard is mandatory.

- [x] 1.1 **Resolve the guard mechanism** (design D3): **RESOLVED — mechanism 1,
      flattened.** Split the base32/64 run into `fullBlock*` (full-width element,
      `=` rejected in the element via `satisfy {b32,b64}Valid`) + an **optional
      terminal tail** (1–4 byte / 1–2 byte tails) via `seq`/`optional`/`subset`,
      flattened back to `List (List UInt8)` (no value-type break). Rejected:
      the unsound "post-condition theorem" (cannot prove `= none` for a case the
      decoder accepts) and the slower "second-pass filter" (decodes-then-discards,
      hides the invariant in a `Bool` check).
- [ ] 1.2 Implement the guard. Under mechanism 1-flattened: define
      `b32FullElem`/`b64FullElem` (full-width, `=` rejected in the element) and
      `b32TailElem`/`b64TailElem` (strict tail, value length 1–4 / 1–2), the
      whole-string relation `full* (tail)?` flattened to `List (List UInt8)`,
      the realizing `decodeB32Strict`/`decodeB64Strict` + `encodeB32`/`encodeB64`,
      and re-derive over the new value path: `roundtrip`,
      `b32DecodeFull_unambiguous`/`b64DecodeFull_unambiguous` (the
      full-consumption uniqueness witness `decodeFull_spec` needs), plus the
      converse (task 4.1) and injectivity (task 4.2). The flat value type
      `List (List UInt8)` is unchanged, so the public API shape survives.
- [ ] 1.3 Prove the run-level rejection theorem: `Codec.decodeFull … = none` for
      the trailing-data class (base64 `"Zg==AAAA"`, base32
      `"MY======" · "AAAAAAAA"`), and for each pad shape (base32 1–5 byte tails;
      base64 1–3 byte tails) as a concrete vector + theorem.

## 2. Canonical-encoding theorems (encoder is the RFC canonical form)

- [ ] 2.1 Fixed-width bases (2/4/8/10/16): `encode{X}` output is alphabet-only —
      every byte in the result satisfies the digit predicate
      (`bitDigit`/`quartetDigit`/`octDigit`/`digDigit`/`hexDigit`).
- [ ] 2.2 Base32 + Base64: `encodeB{X}` output is alphabet-or-pad, with the pad
      run terminal and of exactly the RFC arity for the block length
      (base32: 1 byte → 6 `=`, 2 → 4, 3 → 3, 4 → 1, 5 → 0; base64: 1 → 2 `=`,
      2 → 1, 3 → 0), and `=` never precedes a non-`=` byte in the whole output.

## 3. Rejection theorems (decoder rejects every malformed class)

Per base, restore the F* `decode_*_invalid` family, stated as
`Codec.decodeFull … = none` over `Bytes n`:

- [ ] 3.1 Base16: non-hex byte (including lowercase `6f`) → `none` (record
      lowercase as an _uppercase-only rejection_, not an accepted alias — see
      header note); wrong arity (odd whole length) → `none`.
- [ ] 3.2 Base32: invalid char → `none`; `=` in an illegal position → `none`;
      wrong arity → `none`; trailing data after terminal `=` → `none`
      (ties to §1).
- [ ] 3.3 Base64: the F* reference's `decode_invalid_char` (`!`),
      `decode_pad_first`, `decode_bad_length` vectors, plus trailing-data-after-`=`
      → `none` (ties to §1).
- [ ] 3.4 Base2/4/8/10: invalid alphabet byte → `none`; wrong arity → `none`;
      and (base8/10) the `> 255` overflow triple → `none`.

## 4. Converse / uniqueness theorems

- [ ] 4.1 Per base: `Codec.decodeFull {x}Elem {x}ConsumesByte n s = some ys →
  encode{X} ys = some ⟨n, s⟩` (and the `encodeB{X}` analogue for 32/64),
      via `Codec.decodeFull_spec` + `{x}DecodeFull_unambiguous` + `encodeRepeat_rel`.
- [ ] 4.2 Per base: `encode{X} bs = encode{X} bs' → bs = bs'`
      (and the `encodeB{X}` analogue), via roundtrip to both sides +
      `Option.some.inj`/`{x}DecodeFull_unambiguous`.
- [ ] 4.3 Facade `BaseN`: the `Base`-dispatched `decode_encode_inverse` and
      `encode_injective` are **net-new** (the facade has no dispatch theorem
      today); `cases` over all seven `Base` constructors, handling the two
      result shapes `List UInt8` vs `List (List UInt8)` per shape.

## 5. Bench lane + gate

- [ ] 5.1 `Bench.lean`: add a tiny `Bytes.ofList : List UInt8 → Bytes l.length`
      helper (or use the existing one if `codec` provides it), then an
      `example`/`#eval` per rejection class (F* vectors: base64
      `!`/pad-first/bad-length/`Zg==AAAA`; base32 `MY======AAAAAAAA`; base8/10
      overflow), plus canonical-encoding and converse vectors — each
      re-expressed as a `Bytes n` literal — closing review findings 5.1, 5.7
      (5.10 base16-lowercase is a recorded non-goal, not a vector).
- [ ] 5.2 `lake build` zero `sorry`/warnings; `#print axioms` = `[propext,
  Quot.sound]` for every new theorem (all seven bases + facade); `nix flake
  check` green.
- [ ] 5.3 Commit + push `lean-basen`; update `openspec/changes/lean-basen/`
      (mark review tasks 5.1/5.7/5.10 closed by this change; retire the
      bespoke-surface bullets as superseded by `basen-uniform-leaf-api`).
