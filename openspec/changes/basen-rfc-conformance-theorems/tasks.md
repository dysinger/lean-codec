# Tasks

## 1. Fix the decoder defect (non-terminal padding)

- [ ] 1.1 Add `rest = []` to the padded-tail guards in `BaseN/Base32.lean`
      `decodeN`/`decode` (the `=…`-terminated block branches) so `=` is
      terminal-only per RFC 4648 §3.2.
- [ ] 1.2 Same guard in `BaseN/Base64.lean` `decodeN`/`decode` (1-byte `= =` tail
      and 2-byte `=` tail).
- [ ] 1.3 Re-verify: `lake build` (no regressions), the existing roundtrip and
      byte-exact vectors still hold, and `#eval decode "Zg==AAAA"` / `"MY======"
    ++ "AAAAAAAA"` now return `none`.

## 2. Canonical-encoding theorems (encoder is the RFC canonical form)

- [ ] 2.1 Base16: `encode_allValid` (every output byte is `0-9A-F`).
- [ ] 2.2 Base32 + Base64: `encode` emits only the RFC alphabet, and the `=`
      pad run is exactly the §6.7/§4.7 arity at the very end (`paddingTerminal`/
      `paddingArity`).
- [ ] 2.3 Base2/4/8/10: `encode` output is alphabet-only (their own spec).

## 3. Rejection theorems (decoder rejects every malformed class)

Per base, restore the F* `decode_*_invalid` family and add the quantified forms:

- [ ] 3.1 Base16: `decode` rejects a non-hex byte (and accepts lowercase alias —
      record the `6f` lowercase vector); wrong arity (odd length) → `none`.
- [ ] 3.2 Base32: invalid char → `none`; `=` in an illegal position → `none`;
      wrong arity → `none`; trailing data after `=` → `none`.
- [ ] 3.3 Base64: the F* reference's `decode_invalid_char` (`!`), `decode_pad_first`,
      `decode_bad_length` vectors, plus trailing-data-after-`=` → `none`.
- [ ] 3.4 Base2/4/8/10: invalid alphabet byte, wrong arity, and (base8/10)
      `> 255` overflow triple → `none`.

## 4. Converse / uniqueness theorems

- [ ] 4.1 Per base: `decode xs = some ys → encode ys = xs`.
- [ ] 4.2 Per base: `encode_injective : encode bs = encode bs' → bs = bs'`.
- [ ] 4.3 Facade `BaseN`: dispatch `decode_encode_inverse` and
      `encode_injective` over all seven `Base` constructors by `cases`.

## 5. Bench lane + gate

- [ ] 5.1 `Bench.lean`: add an `example`/`#eval` per rejection class (F* vectors:
      base64 `!`/pad-first/bad-length/`Zg==AAAA`; base32 `MY======AAAAAAAA`;
      base16 lowercase `6f`; base8/10 overflow), plus canonical-encoding and
      converse vectors — closing review findings 5.1, 5.7, 5.10.
- [ ] 5.2 `lake build` zero `sorry`/warnings; `#print axioms` = `[propext,
    Quot.sound]` for every new theorem (all seven bases + facade); `nix flake
    check` green.
- [ ] 5.3 Commit + push `lean-basen`; update `openspec/changes/lean-basen/`
      (mark review tasks 5.1/5.7/5.10 closed by this change).
