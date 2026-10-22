# Tasks

> **Surface (read first):** every base is a **run value** decoded/encoded by the
> single `Codec.decode` / `Codec.encode` — "only the codec changes." The
> fixed-width bases (2/4/8/10/16) are `count k (satisfy p) ≫ <block iso>` made
> into a `Run` (bundling the derived `relRepeat`/`decodeRepeat`/`encodeRepeat`);
> the padded bases (32/64) are a full-block `Run` plus a terminal-tail `alt`/`iso`
> onto `B32`/`B64` (so illegal "data after `=`" states are **unrepresentable**).
> `many` is **derived** (never a constructor). There is **no** bespoke
> `encode`/`decode`, **no** `decodeB32Strict`/`encodeB64Strict` run triple, **no**
> per-format function. Base16 is uppercase-only.

## 0. Core: no `many` constructor — a first-class **run value** (downstream, no codec change) — NEW

> `many` is **derived** (paper §3.4; F\* `satisfy_many0`), never an AST node. A
> `many` constructor is verified un-implementable in Lean (definition-order cycle
> `Codec → Productive → Rel → Codec`, rejected mutual-inductive universe mismatch).
> The uniform surface is a **run value** bundling the already-proved
> `relRepeat`/`decodeRepeat`/`encodeRepeat` — **no** `codec`-core change. See
> `specs/codec/spec.md`.

- [ ] 0.1 Define `Run` (in `BaseN`, downstream `lean-basen`): a `structure` bundling
      `elem : Codec UInt8` + `step : ConsumesByte elem`, with `decode :=
    decodeRepeat elem step`, `encode := encodeRepeat elem`, `rel := relRepeat (Rel
    elem)`. Its laws are the inherited `decodeRepeat_spec`/`encodeRepeat_rel`.
- [ ] 0.2 Confirm `lake build` green with `Run` in place (no core change; zero
      `sorry`/warnings; `#print axioms Codec.roundtrip` still `[propext,
    Quot.sound]`).

## 1. The uniform `Codec (List UInt8)` bases, deleting the run triples

- [ ] 1.1 Delete the base32/64 bespoke run triples: `parseB64`/`encodeB64Strict`/
      `relB64Strict`/`decodeB64Strict` (and the base32 analogues), and their
      per-format lemmas. Keep the terminal-tail `B32`/`B64` value types and the
      digit math + block `Iso`s (`b32BlockIso`/`b64BlockIso`).
- [ ] 1.2 Re-express each fixed-width base as a `Run` over the element
      `Codec UInt8 := count k (satisfy p) ≫ blockIso` (Base16 `count 2`, base2
      `count 8`, base4 `count 4`, base8 `count 3`, base10 element run + block iso).
- [ ] 1.3 Re-express base32/64 as a `Run` over the full-block element plus a
      terminal-tail `alt`/`iso` onto `B32`/`B64`. The terminal-tail branch is
      terminal (empty continuation), so "data after `=`" is unrepresentable.
- [ ] 1.4 Prove `roundtrip` per base as the **inherited** `decodeRepeat_spec`/
      `encodeRepeat_rel` law (no bespoke law); `lake build` green.

## 2. Facade: uniform `encode (b : Base)` / `decode (b : Base)`

- [ ] 2.1 Restore the facade `encode (b : Base) : List UInt8 → List UInt8` /
      `decode (b : Base) : List UInt8 → Option (List UInt8)` dispatching `cases b`
      to the single `Codec` value per base, normalized through `BaseN.Bridge`.
- [ ] 2.2 Prove `roundtrip (b : Base) (bs) : decode b (encode b bs) = some bs`.
- [ ] 2.3 Add facade-dispatched `decode_encode_inverse`/`encode_injective` — now
      over the **single** value type (`List UInt8`), no three-shape signature
      decision, no `Base.val` family.

## 3. Rejection theorems (the illegal shape has no inhabitant)

- [ ] 3.1 Base64: `decode base64 (decodeFull …) "Zg==AAAA" = none` (structural:
      no `B64` term), plus invalid-char, pad-first, bad-length, and pad-shape
      vectors — all over the uniform decoder.
- [ ] 3.2 Base32: `decode base32 "MY======AAAAAAAA" = none` and the same family.
- [ ] 3.3 Fixed-width bases: the F\* rejection family per base (base16 non-hex +
      lowercase + odd arity; base2/4/8/10 invalid alphabet + wrong arity +
      base8/10 overflow).

## 4. Canonical + converse + injectivity

- [ ] 4.1 Fixed-width bases: `encode{X}` alphabet-only.
- [ ] 4.2 Base32/64: `encode` alphabet-or-pad, pad exactly the terminal tail's RFC
      arity, `=` never precedes non-`=`.
- [ ] 4.3 Per base: `decode … = some v → encode v = some ⟨n, s⟩` (converse).
- [ ] 4.4 Per base: `encode v = encode v' → v = v'` (injectivity).

## 5. Bench lane + gate

- [ ] 5.1 `Bench.lean`: rewire to the uniform surface — roundtrip `example`s,
      canonical vectors (`Zg==`/`Zm8=`/`Zm9v`, `MY======`/`MZXW6YTB`), rejection
      `example`s (`Zg==AAAA`/`MY======AAAAAAAA`), converse + overflow vectors, all
      through `Codec.decode`/`Codec.encode` (or the facade), never a bespoke fn.
- [ ] 5.2 `lake build` and `lake build bench` green, zero `sorry`/warnings;
      `#print axioms` = `[propext, Quot.sound]` (or `[propext]`) for the new laws;
      `nix flake check` green (checks.lean + checks.formatting).
- [ ] 5.3 Commit + push; update `openspec/changes/lean-basen/` (its §4.1 "no
      roundtrip dispatch" note → "facade dispatches over one `Codec` type").
