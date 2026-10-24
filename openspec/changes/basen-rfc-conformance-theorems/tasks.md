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

- [x] 0.1 Define `Run` (in `BaseN`, downstream `lean-basen`): a `structure` bundling
      `elem : Codec UInt8` + `step : ConsumesByte elem`, with `decode :=
decodeRepeat elem step`, `encode := encodeRepeat elem`, `rel := relRepeat (Rel
elem)`. Its laws are the inherited `decodeRepeat_spec`/`encodeRepeat_rel`.
- [x] 0.2 Confirm `lake build` green with `Run` in place (no core change; zero
      `sorry`/warnings; `#print axioms Codec.roundtrip` still `[propext,
Quot.sound]`).

## 1. The uniform `Codec`-value bases (the `Run`/`many` repetition is a wrapper, not a base), deleting the run triples

- [ ] 1.1 Delete the base32/64 bespoke run triples: `parseB64`/`encodeB64Strict`/
      `relB64Strict`/`decodeB64Strict` (and the base32 analogues), and their
      per-format lemmas. Keep the terminal-tail `B32`/`B64` value types and the
      digit math + block `Iso`s (`b32BlockIso`/`b64BlockIso`).
- [x] 1.2 Re-express each fixed-width base as a `Run` over the element
      `Codec UInt8 := count k (satisfy p) ≫ blockIso` (Base16 `count 2`, base2
      `count 8`, base4 `count 4`, base8 `count 3`, base10 element run + block iso).
- [x] 1.3 Re-express base32/64 as a `Run` over the full-block element plus a
      terminal-tail `alt`/`iso` onto `B32`/`B64`. The terminal-tail branch is
      terminal (empty continuation), so "data after `=`" is unrepresentable.
      _(base64 foundation landed (`../lean-basen` `a71277c`): `b64BlockElem` /
      `b64TailElem` `Codec (List UInt8)` elements (with a new `b64TailIso` law
      restricting a block to 1–2 bytes), `b64Run`/`b64TailRun`, all
      unambiguity/functional/canonical lemmas, the uniform `decodeFullB64`/
      `encodeB64`, and `decodeFull_b64Tail_of_encode`. The whole-input
      `roundtrip` + conformance laws are still open.)_ Base32's Codec-value
      layer (`b32BlockElem`/`b32TailElem`/`b32Run`/`b32TailRun`/`decodeFullB32`/
      `encodeB32`/`decodeFull_b32Tail_of_encode`, 1–4-byte tail shapes) is now
      landed too.
- [ ] 1.4 Prove `roundtrip` per base as the **inherited** `decodeRepeat_spec`/
      `encodeRepeat_rel`/`decodeFull_spec` laws for each component **plus one
      named block-run/tail split-uniqueness composition lemma** (the D7 shape);
      `lake build` green.
      _(base64's roundtrip requires the `concat`-empty / `Suffix.drop`-then-
      `prepend` transport lemma family over the block-prefix-then-tail split.
      **The transport lemma family is now LANDED** in `BaseN/Common.lean`
      (`bdrop_concat` / `concat_eq_drop_prepend` / `decodeRepeat_prefix_concat`,
      all `[propext, Quot.sound]`-only, build green — `../lean-basen` `dd69bbf`).
      **This session added the base64 whole-input transport half**
      (`../lean-basen` `1ab89d4`): `decodeFull_cast` (decode insensitive to a
      length cast), `b64Split_shape`/`b64Split_ofBytes_ofBytes` (the direct
      `b64Split` re-labels `b64Split_ofBytes ∘ b64OfBytes`), and the
      `Suffix.drop`-then-`concat` tail lemmas
      (`decodeFull_b64Tail_suffix_nil`/`_cons`), plus the pad-dichotomy primitives
      (`b64Char_pad_false` / `not_rel_b64BlockElem_of_pad`) — all
      `[propext, Quot.sound]`-clean, build green. Base32 needs the mirror set.
      Per the **D7 correction** (settled this session), do **not** try to build a
      single `Codec B64`/`Codec B32` value (impossible: no repetition node in the
      `Codec` AST). The target shape is the **composition** — `decodeRepeat
b64BlockElem` (the full-block `Run`) then `decodeFull b64TailElem` (the
      terminal tail), `iso`-ed to `B64` — and the roundtrip law is the inherited
      per-component laws **plus one named, scoped split-uniqueness lemma** (the
      committed block prefix is unique). That one lemma is the open substep (and
      base32 mirrors it with 5 tail shapes); it needs (a) the content-extraction
      primitive and (b) the pad dichotomy. There is **no** `List.head? (...filterMap...)`
      in the target shape — the `head?` form is superseded by the direct `Run.decodeFull`/
      `Codec.decodeFull` composition. Both (a)/(b) are `[propext, Quot.sound]`-provable
      but need careful `List.ofFn`/`Fin`-cast reasoning in the stdlib-only (no
      `convert`/`conv`/`nth_rewrite`) tactic environment.)_
      _(**Session update (next session's starting state):** in `../lean-basen`
      `BaseN/Base64.lean` this session landed the **length/size invariants** the
      split-uniqueness lemma needs — `relB64Block_len`/`relB64Tail_len`
      (`relRepeat (Rel {x}Elem) xs n s → n = 4·xs.length`) and
      `Rel_b64TailElem_size` (a tail block value is 1–2 bytes) — all
      `[propext, Quot.sound]`-only, zero `sorry`, build green
      (`../lean-basen` `f8a3b30`). The roundtrip scaffolding also compiles
      (verified): `encodeB64 bs = some ⟨n,s⟩` unfolds to
      `encodeRepeat b64BlockElem blocks = some ⟨m₁, blkBytes⟩` +
      `encodeB64Tail tail = some ⟨m₂, tailBytes⟩` with
      `s = concat blkBytes tailBytes`; the flatten identity
      `blocks.flatten ++ tail = bs` (via `b64Split_ofBytes_shape`+
      `b64BytesOf_ofBytes`); and the committed block decode +
      `decodeRepeat_prefix_concat` lift. **The open substesp — the
      split-uniqueness lemma itself — still needs (in order):**
      (1) `Rel_b64BlockElem_size` (a full block relates to exactly **3 bytes**,
      i.e. `b64BlockApply` on 4 no-pad chars takes the 3-byte branch of
      `b64BlockDecodeLenient`); (2) the pad-dichotomy rejection — a no-pad
      4-char block decodes to 3 bytes so `Rel b64TailElem` (1–2 bytes) cannot
      hold; (3) pin `t.remaining = m₂` (both ∈ {0,4} — via `encodeB64Tail_len`,
      `relB64Tail_len` on `hxd`'s `decodeFull_some`, and the pad argument that
      rules out the `|x| = |blocks|−1` case, where `4·|tx| = 4(|blocks|−|x|) + m₂`
      forces a second `=` that does not exist); (4) `x = blocks` via
      `b64BlockDecodeFull_unambiguous` on the extracted prefix; (5) the
      `head?`/`filterMap` singleton step (all members `= bs` + non-emptiness);
      (6) rewrite `decodeFullB64`/`decodeFullB32` off the `head?`/`filterMap`
      shape per D7, then the **base32 mirror** (5 tail shapes, harder).)_
      _(**Session update (pad-dichotomy foundation landed):** substeps (1), (2),
      and the tail side of (3) are now **proved** and committed in
      `../lean-basen` `BaseN/Base64.lean`, all `[propext, Quot.sound]`-only,
      zero `sorry`, build green: * `Rel_b64BlockElem_size` — a `b64BlockElem` value is a 3-byte list
      (substep 1; pitch-forks `b64BlockUnapply x = some a` against the
      1/2-byte shapes, each embedding a `61`, via `Rel_count_satisfy_ofFn`
      content extraction for "`a` is pad-free") — `../lean-basen` `eb2c062`; * `Rel_b64BlockElem_not_tail` — a value cannot be both a full block
      (3 bytes) and a terminal tail (1–2 bytes) (substep 2, the pad-dichotomy
      rejection) — `../lean-basen` `eb2c062`; * `Rel_b64TailElem_has_pad` — a `b64TailElem`-related string contains a
      `=` byte (the tail side of substep 3's boundary pin; forward-direction
      dual of `Rel_b64BlockElem_size`) — `../lean-basen` `7febf2c`.
      With the already-landed `not_rel_b64BlockElem_of_pad` / `b64Char_pad_false` /
      `relB64Block_len` / `relB64Tail_len` / `Rel_b64TailElem_size`, the full
      pad-dichotomy foundation is complete. **Also landed (encoded-output
      structure, the boundary-pin's remaining inputs):** * `encodeB64Block_nopad` — `encodeRepeat b64BlockElem blocks = some ⟨n,s⟩`
      forces every byte `b64Char` (alphabet-only, never `=`), via
      `relRepeat_forall b64Char` + `Rel_b64BlockElem_canonical` —
      `../lean-basen` `3f1fb84`; * `encodeB64Tail_has_pad` — a non-empty `encodeB64Tail` output contains a
      `=` byte (via `encode_rel b64TailElem` + `Rel_b64TailElem_has_pad`) —
      `../lean-basen` `3f1fb84`; * `encodeB64Tail_len` — `encodeB64Tail tail = some ⟨n,s⟩` pins `n = 0 ∨
n = 4` (empty tail or one padded block) — `../lean-basen` `c0cf50d`.
      **Still open:** the split-uniqueness lemma itself (substeps 3–5: the
      boundary-pin `t'.remaining = m₂` via the 4-aligned no-pad-prefix argument,
      then `blocks' = blocks` via `b64BlockDecodeFull_unambiguous`, then the
      `head?`/`filterMap` singleton) and substep 6 (D7 rewrite of
      `decodeFullB64`/`decodeFullB32` off `head?`/`filterMap`) + the base32
      mirror.)_
      _(**Session update (next session's starting state):** two transport helpers
      landed in `../lean-basen` (uncommitted in the working tree, `lake build`
      green, `#print axioms` `[propext]`/`[propext, Quot.sound]` respectively): * `Codec.Common.head?_eq_some_of_mem_eq` — `b ∈ L → (∀ x ∈ L, x = b) → L.head? = some b`, the
      `head?`-of-`filterMap` wrap-up once the `filterMap` is shown a singleton/all-`bs`; * `Base64.prepend_concat_prefix_cast` — from `t'.prepend s₀ = concat a b` and
      `e : m₁+m₂-t'.remaining = m₁`, the cast `cast (congrArg Bytes e) s₀ = a` (the
      consumed-prefix half of the boundary-pin extraction).
      **Still open (in order):**

      > **NEXT SESSION — work THIS entry, nothing else.** Task **1.4**, substeps ~~(2) the
      > boundary pin~~ (LANDED `fedbda9`), ~~(3) `blocks' = blocks`~~ (LANDED `25c33cf`), and
      > ~~(4) the roundtrip assembly~~ (LANDED `ca91716`) are all **done for base64** —
      > `decodeFullB64 (encodeB64 bs) = some bs` is proved `[propext, Quot.sound]`-only, zero
      > `sorry`, `lake build` green, pushed. The base64 half of task 1.4 is complete.
      > The **next step** is the **base32 mirror** (substep 5): the whole-input roundtrip
      > `decodeFullB32 (encodeB32 bs) = some bs` needs the base32 lemma family
      > (`relB32Block_len`/`relB32Tail_len`/`Rel_b32BlockElem_size`/`Rel_b32TailElem_has_pad`/
      > `encodeB32Block_nopad`/`encodeB32Tail_len` — **none landed yet**, unlike base64) plus the
      > base32 boundary-pin + block-run-uniqueness + tail-pin analogues (5 tail shapes).
      > Substep (6) — the D7 rewrite of `decodeFullB64`/`decodeFullB32` off the `head?`/`filterMap`
      > shape — remains a *definition* change: the roundtrip **theorem** already closes over the
      > current shape (the D7 rewrite is not required for the law, only for the "no `head?`
      > superseded by direct composition" wording). **Do NOT touch 1.1 (delete strict triples)** —
      > it stays blocked behind 1.4 → 2.1. The full substep list follows:
      >
      (1) ~~`prepend_concat_suffix`~~ **LANDED** (`../lean-basen`
      `29a620e`, `[propext, Quot.sound]`-only, build green) — the `t'.bytes = tailBytes` half,
      proved via `bdrop_prepend t' s₀` + `bdrop`-of-`concat` in the `bdrop_prepend` natural form
      (conclusion `cast (sub_sub_self.symm) t'.bytes = cast (by omega) b`; the RHS goes through
      `Bytes.ext` + `cast_bytes_val'` + `dsimp [bdrop, concat]` + `hk : m₁+m₂-t'.remaining = m₁`
      so `simp [hk, hnot]` closes the `Fin`-reindexing defeq-clean); (2) ~~the boundary pin `t'.remaining = m₂`~~ **LANDED** (`../lean-basen`
      `fedbda9`, `[propext, Quot.sound]`-only, zero `sorry`, build green) — `b64_boundary_pin`,
      the block/tail split pin (via `s₀` alphabet-only vs
      `concat` `=`-in-`[m₁,m₁+m₂)`, `relB64Tail_len`, `encodeB64Tail_len`, and `Rel_b64TailElem_has_pad`
      for the `m₂=0` case, plus the private transport helpers `prepend_prefix_read`/
      `prepend_suffix_read`/`concat_tail_read`/`b64_first_tail_block_not_alphabet`/
      `four_mul_lt_of_lt`); (3) ~~`blocks' = blocks`~~ **LANDED** (`../lean-basen` `25c33cf`, `[propext, Quot.sound]`-only) —
      `b64_block_run_of_boundary` via `relB64Block_unambiguous` (`relRepeat_cast` +
      `prepend_concat_prefix_cast` + the `hrem : t'.remaining = m₂` boundary pin); (4) ~~roundtrip assembly~~ **LANDED** (`../lean-basen` `ca91716`, `[propext, Quot.sound]`-only,
      zero `sorry`) — `decodeFullB64_roundtrip : decodeFullB64 (encodeB64 bs) = some bs`, via the
      membership half `decodeFullB64_mem_encode` (`decodeRepeat_prefix_concat` +
      `decodeFull_b64Tail_suffix_nil/_cons` + the flatten identity) and the singleton half
      (`head?_eq_some_of_mem_eq` + boundary pin + `b64_block_run_of_boundary` + the tail pin
      `tail'.flatten = tail`, whose cast bridge `cast (congrArg Bytes hbnd) t'.bytes = tailBytes`
      uses `prepend_suffix_read`/`concat_tail_read`, and whose content pin uses
      `decodeFull_b64Tail_of_encode` per `tail` case); (5) the base32 mirror (needs `relB32Block_len`/`relB32Tail_len`/`Rel_b32BlockElem_size`/
      `Rel_b32TailElem_has_pad`/`encodeB32Block_nopad`/`encodeB32Tail_len` — none landed yet, unlike base64).)_

## 2. Facade: uniform `encode (b : Base)` / `decode (b : Base)`

- [ ] 2.1 Restore the facade `encode (b : Base) : List UInt8 → List UInt8` /
      `decode (b : Base) : List UInt8 → Option (List UInt8)` dispatching `cases b`
      to the base's `Run`/composition (full-block `Run` + terminal-tail `Codec`,
      `iso`-ed to `B32`/`B64`, then the byte transport), normalized through
      `BaseN.Bridge`.
      _(facade-half landed: the uniform `List UInt8` `encode`/`decode` exists in
      `BaseN.lean`, `cases b` across all seven; base32/64 still dispatch to the
      strict/parse `decodeB32Strict`/`encodeB32Strict` + byte transport, **not**
      the `Run`+tail composition — that half waits on tasks 1.1/1.3/1.4.)_
- [ ] 2.2 Prove `roundtrip (b : Base) (bs) : decode b (encode b bs) = some bs`.
      _(per-base `roundtripBytes` for the B32/B64 transport are done; the
      `Base`-dispatching `roundtrip` is not.)_
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
      roundtrip dispatch" note → "facade dispatches over one value type
      `List UInt8`").
