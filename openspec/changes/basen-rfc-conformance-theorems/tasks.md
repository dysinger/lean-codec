# Tasks

> **Surface (read first):** the five fixed-width bases (2/4/8/10/16) are `Codec`
> values over `satisfy`/`count`/`iso` + the repetition layer, value type
> `List UInt8`, whole-input decoder `Codec.decodeFull {x}Elem {x}ConsumesByte`.
> The padded bases (32/64) are being **re-typed**: their value is the terminal-tail
> inductive `B32`/`B64` (so "data after `=`" is unrepresentable), realized as a
> strict **run triple** (`relStrict`/`decodeStrict`/`encodeStrict`), **not** a
> `Codec` value and **not** a flattened `List (List UInt8)`.
> **Base16 is uppercase-only** (`hexElem` is a strict `0-9A-F` bijection);
> lowercase `6f` is a rejection, not an accepted alias (D8).

## 0. Delete the lenient base32/64 codecs and the committed filter

- [x] 0.1 Delete the `bb46230` post-hoc filter from `BaseN/Base64.lean`
      (`b64TerminalPad`/`B64TerminalPad`/`decodeB64Strict`/`relB64Strict`/
      `roundtripStrict`/`b64TerminalPad_rejects_tail_then_full`/
      `decodeB64Strict_rejects_trailing`).
- [x] 0.2 Delete the lenient base32/64 codecs: `b32Elem`/`decodeB32`/
      `encodeB32`/`relB32` (in `BaseN/Base32.lean`) and `b64Elem`/`decodeB64`/
      `encodeB64`/`relB64` (in `BaseN/Base64.lean`), plus their roundtrip/
      unambiguity lemmas that only make sense over `List (List UInt8)`. Kept the
      digit math and the existing block `Iso`s (`b32BlockIso`/`b64BlockIso`)
      that already enforce intra-block canonicality.

## 1. The new value types and arity-fixed block `Iso`s

- [x] 1.1 Define `B64` (nil / full 3-byte / tail1 / tail2) and `B32`
      (nil / full 5-byte / tail1..tail4) as the terminal-tail inductives
      (design D0, tuple elements `UInt8 × …`). (Naming note: the empty
      constructor is `nil`, not `empty`, to avoid the `Codec.empty` clash after
      `open Codec`.)
- [x] 1.2 (adjusted — see note) The block canonicality is enforced by the
      **existing** `b64BlockIso`/`b32BlockIso` (their `b64BlockDecodeLenient`/
      `b32BlockDecodeLenient` already reject `=` in a non-canonical block and
      return the exact 1–3 / 1–5-byte shape). So the strict `parseB64`/`parseB32`
      reuse these and the existing per-shape `*_unapply_*` identities; **no
      separate arity-fixed `Iso` was needed** (it would re-state the same
      bijection at a narrower type). This is a simplification, not a weakening:
      the run-level illegal state is eliminated by the `B64`/`B32` value type,
      and intra-block canonicality is already by-construction in the block `Iso`.
      The forward `rel_count_satisfy` lemma (design D5) was **not** needed
      because the strict codec is `List UInt8`-carried structural recursion, not
      `decodeFull`/`decodeRepeat` over a `Bytes n` element.

## 2. The strict run triples over `B32`/`B64`

- [x] 2.1 `encodeB64Strict : B64 → List UInt8` (= `b64CharsOf`, total),
      `decodeB64Strict : List UInt8 → Option B64` (via `parseB64`), with the
      same for `B32`. _(Carrier note: the strict codec is `List UInt8`-carried,
      not `Bytes n → Option B64` / `Option (Sigma n, Bytes n)`; the `Bytes n`
      substrate is applied by consumers via `BaseN.Bridge`, as for the
      fixed-width surface. The perfection — `B64`/`B32` making illegal states
      unrepresentable — is in the value type and structural parser, independent
      of the byte carrier.)_
- [x] 2.2 Prove **strict roundtrip**: `decodeB64Strict (encodeB64Strict v) = some v`
      (and the base32 analogue), `[propext, Quot.sound]`-only. (Named
      `strict_roundtrip`; proved via `parseB64_charsOf`/`parseB32_charsOf`
      induction + the existing per-shape `*_unapply_*` identities.)

## 3. Rejection theorems (the illegal shape has no inhabitant)

- [x] 3.1 (core) Base64: `decodeB64Strict "Zg==AAAA" = none` (`rejects_trailing`,
      `[propext]`-only). Remaining: invalid char (`!`), pad-first, bad-length,
      and each pad-shape vector as separate theorems.
- [x] 3.2 (core) Base32: `decodeB32Strict "MY======"+"AAAAAAAA" = none`
      (`rejects_trailing`, `[propext]`-only). Remaining: invalid char,
      pad-in-illegal-position, wrong arity, and each pad-shape vector.
- [ ] 3.3 Fixed-width bases: the F* rejection family per base (base16 non-hex +
      lowercase + odd arity; base2/4/8/10 invalid alphabet + wrong arity +
      base8/10 overflow), as `Codec.decodeFull … = none`.

## 4. Canonical + converse + injectivity

- [ ] 4.1 Fixed-width bases: `encode{X}` alphabet-only (every byte satisfies the
      digit predicate).
- [ ] 4.2 Base32/64: `encodeStrict` alphabet-or-pad, pad exactly the terminal
      tail's RFC arity, `=` never precedes non-`=`.
- [ ] 4.3 Per base: `decode … = some v → encode v = some ⟨n, s⟩` (converse).
- [ ] 4.4 Per base: `encode v = encode v' → v = v'` (injectivity).
- [ ] 4.5 Facade `BaseN`: the `Base`-dispatched `decode_encode_inverse`/
      `encode_injective` (net-new), `cases` over all seven, three shapes.

## 5. Bench lane + gate

- [x] 5.1 (partial) `Bench.lean`: rewired to the strict surface — strict
      roundtrip `example`s, strict canonical-encoding vectors (`Zg==`/`Zm8=`/
      `Zm9v`, `MY======`/`MZXW6YTB`), and the `Zg==AAAA`/`MY======AAAAAAAA`
      rejection `example`s (via `rejects_trailing`). Remaining: `Bytes.ofList`
      helper + base8/10 overflow + converse vectors.
- [x] 5.2 `lake build` and `lake build bench` both green, zero `sorry`/
      warnings; `#print axioms` = `[propext, Quot.sound]` (or `[propext]`) for all
      four new theorems; `nix flake check` green (`checks.lean` + `checks.formatting`).
- [ ] 5.3 Commit + push `lean-basen`; update `openspec/changes/lean-basen/`.
