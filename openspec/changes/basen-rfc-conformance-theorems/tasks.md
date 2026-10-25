# Tasks

> **Surface (read first):** every base is a **run value** decoded/encoded by the
> single `Codec.decode` / `Codec.encode` — "only the codec changes." The
> fixed-width bases (2/4/8/10/16) are `count k (satisfy p) ≫ <block iso>` made
> into a `Run` (bundling the derived `relRepeat`/`decodeRepeat`/`encodeRepeat`);
> the padded bases (32/64) are a full-block `Run` plus a terminal-tail `alt`/`iso`;
> the `B32`/`B64` inductive is the **canonical block/tail spine** (a proved total
> bijective relabeling of `List UInt8`), and rejection is a `decodeFullB32`/
> `decodeFullB64 = none` inequation over the composition, not a type-level
> unrepresentability.
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

- [x] 1.1 Delete the base32/64 bespoke run triples: `parseB64`/`encodeB64Strict`/
      `relB64Strict`/`decodeB64Strict` (and the base32 analogues), their per-format
      lemmas, **and the `decodeBytes`/`encodeBytes`/`roundtripBytes` shims**, plus
      the `BaseN.Bridge` module (facade-only). Keep the terminal-tail `B32`/`B64`
      value types and the digit math + block `Iso`s (`b32BlockIso`/`b64BlockIso`).
      _(**now unblocked:** the facade was removed, so this is the immediate next
      task after 1.4; the strict triples are used only by the deleted facade and
      the bench, which 5.1 re-anchors.)_
- [x] 1.2 Re-express each fixed-width base as a `Run` over the element
      `Codec UInt8 := count k (satisfy p) ≫ blockIso` (Base16 `count 2`, base2
      `count 8`, base4 `count 4`, base8 `count 3`, base10 element run + block iso).
- [x] 1.3 Re-express base32/64 as a `Run` over the full-block element plus a
      terminal-tail `alt`/`iso`; the `B32`/`B64` inductive is the canonical
      block/tail spine (the terminal-tail branch is a terminal continuation).
      _(base64 foundation landed (`../lean-basen` `a71277c`): `b64BlockElem` /
      `b64TailElem` `Codec (List UInt8)` elements (with a new `b64TailIso` law
      restricting a block to 1–2 bytes), `b64Run`/`b64TailRun`, all
      unambiguity/functional/canonical lemmas, the uniform `decodeFullB64`/
      `encodeB64`, and `decodeFull_b64Tail_of_encode`. The whole-input
      `roundtrip` + conformance laws are still open.)_ Base32's Codec-value
      layer (`b32BlockElem`/`b32TailElem`/`b32Run`/`b32TailRun`/`decodeFullB32`/
      `encodeB32`/`decodeFull_b32Tail_of_encode`, 1–4-byte tail shapes) is now
      landed too.
- [x] 1.4 Prove `roundtrip` per base as the **inherited** `decodeRepeat_spec`/
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
      > superseded by direct composition" wording). **1.1 (delete strict triples) is now the next
      > task** — the facade (former 2.1/2.2/2.3) was removed, so 1.1 is unblocked by 1.4. The full
      > substep list follows:
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
      `decodeFull_b64Tail_of_encode` per `tail` case); (5) ~~the base32 mirror~~ **LANDED** (`../lean-basen`
      `c216e2f`, `[propext, Quot.sound]`-only, zero `sorry`, `lake build` + `lake build bench` green) —
      the base32 lemma family (`relB32Block_len`/`relB32Tail_len` = 8 chars/block, `Rel_b32BlockElem_size` = 5 bytes,
      `Rel_b32TailElem_size` = 1–4 bytes, `Rel_b32BlockElem_not_tail`, `Rel_b32TailElem_has_pad`,
      `b32Char_pad_false`/`not_rel_b32BlockElem_of_pad`, `encodeB32Block_nopad`/`encodeB32Tail_has_pad`/
      `encodeB32Tail_len` = m₂ ∈ {0,8}) plus the 8-aligned boundary pin `b32_boundary_pin` (via
      `eight_mul_lt_of_lt`), block-run uniqueness `b32_block_run_of_boundary`, and the whole-input
      assembly `decodeFullB32_mem_encode`/`decodeFullB32_roundtrip` (`decodeFullB32 (encodeB32 bs) = some bs`,
      5 tail shapes). **_Task 1.4 is now complete (base64 + base32 both have the whole-input roundtrip)._**)_

## 2. No facade — delete the radix-dispatch layer (removed)

> **Removed:** the `Base` enum and `encode (b : Base)` / `decode (b : Base)`
> facade was cut (no client, type-erases `B32`/`B64`, a bespoke function by
> another name). The uniform surface is `Codec.decode`/`Codec.encode` on each
> base's own value; the radix lives in the value, never a dispatch index. The
> work the facade would have carried (deleting the strict triples, re-anchoring
> the bench, re-stating conformance over the composition) is folded into tasks
> 1.1 and 3.x/4.x/5.x below.

## 3. Rejection theorems (proved as `= none` inequations over the composition)

- [x] 3.1 Base64: `decodeFullB64 … "Zg==AAAA" = none` (pad-dichotomy
      inequation: the full-block run stops at the first `=`, the leftover
      alphabet-only bytes cannot decode as a `b64TailElem`), plus invalid-char,
      pad-first, bad-length, and pad-shape vectors — all over the uniform decoder.
      _(**DONE + D8 completes it:** the flagship `decodeFullB64_reject_ZgAAAA` is `[propext, Quot.sound]`-clean
      (the `Classical.choice` leak was traced to `omega`'s `Nat.lt_or_gt_of_ne` trichotomy in the
      `hall` byte-extraction; replaced with the clean `BaseN.Common.nat_lt_four` case analysis).
      Added the full F\* rejection family over `decodeFullB64`: `decodeFullB64_reject_invalid_char`
      (`!g==`), `decodeFullB64_reject_pad_first` (`=g==`), `decodeFullB64_reject_bad_length` (`Zg`),
      plus the shared `decodeFullB64_reject_first_invalid` (4-byte first-byte-not-`b64Valid`) and
      `Rel_b64TailElem_first_char` (a tail's first byte is `valToB64`-valid, never `=`). All
      `[propext, Quot.sound]`-only, zero `sorry`, zero warnings.
      **D8 (this change) closes the remaining gap:** the above reject only the `Zg==AAAA` class
      (trailing alphabet-only data, not a tail). The single-block-tail decode rejects the
      `Zg==Zg==` class (data after terminal `=` that IS a valid padded block) too — see D8.)_
- [x] 3.2 Base32: `decodeFullB32 … "MY======AAAAAAAA" = none` and the same family.
      _(**DONE:** mirrors the base64 rejection family. Added `decodeFullB32_some` (the
      decomposition bridge), `nat_lt_eight`, the flagship `decodeFullB32_reject_MYAAAA`
      (`MY======AAAAAAAA`), `Rel_b32TailElem_first_char` (a tail's first byte is `b32Valid`,
      over the four 1–4-byte tail shapes), `decodeFullB32_reject_first_invalid`, and the
      vectors `decodeFullB32_reject_invalid_char` (`!==...`)/`_pad_first` (`===...`) /
      `_bad_length` (`MY`). All `[propext, Quot.sound]`-only, zero `sorry`, zero warnings,
      `lake build` green. `../lean-basen` `BaseN/Base32.lean`.
      **D8 (this change) closes the remaining gap:** the `MY======MY======` class (data
      after terminal `=` that IS a valid padded block) is rejected by the single-block-tail
      decode — see D8.)_
- [x] 3.3 Fixed-width bases: the F\* rejection family per base (base16 non-hex +
      lowercase + odd arity; base2/4/8/10 invalid alphabet + wrong arity +
      base8/10 overflow).

## 4. Canonical + converse + injectivity

- [x] 4.1 Fixed-width bases: `encode{X}` alphabet-only.
- [x] 4.2 Base32/64: `encode` alphabet-or-pad, pad exactly the terminal tail's RFC
      arity, `=` never precedes non-`=`.
      _(**DONE (4.2).** Landed `encodeB64_canonical`/`b64TailBlock_canonical` (base64) and
      `encodeB32_canonical`/`b32TailBlock_canonical` (base32) in `../lean-basen`, all
      `[propext, Quot.sound]`-only, zero `sorry`/warnings, `lake build` green. The canonical form
      is a decomposition over `List.ofFn`: alphabet-only full blocks (`encodeReplace`/`encodeBlock_nopad`
      lifted via `List.getElem_ofFn`) followed by a single padded tail whose `List.ofFn` is empty or exactly
      `[c₀,c₁,=,=]` / `[c₀,c₁,c₂,=]` (b64 — 1/2-byte tails → 2/1 pads) or `[c₀,c₁,=×6]`/`[c₀,c₁,c₂,c₃,=×4]`/
      `[c₀..c₄,=×3]`/`[c₀..c₆,=]` (b32 — 1/2/3/4-byte tails → 6/4/3/1 pads), so the output is alphabet-or-pad
      with terminal, RFC-arity-correct `=`. Uses the key helper `b32TailApply_block`
      (`b32TailApply a = some ys → b32BlockApply a = some ys`). `List.ofFn (concat s₀ s₁) =
List.ofFn s₀ ++ List.ofFn s₁` from `Codec.ofFn_concat`.)_
- [x] 4.3 Per base: `decode … = some v → encode v = some ⟨n, s⟩` (converse).
      _(**DONE (`../lean-basen` `9babcab`/`6d7ba52`), `[propext, Quot.sound]`-only, zero `sorry`.** The
      padded bases are `decodeFullB64_conv` (`decodeFullB64 s = some v → encodeB64 v = some ⟨n, s⟩`) and its
      `decodeFullB32_conv` mirror; the fixed-width bases already had `decode_encode_inverse` (Base2/4/8/10/16).
      The proof shape: `decodeFullB64_some` decomposes into `blocks`/`t`/`tails` (`tails.length ≤ 1`), the block
      run re-encodes via `encodeRepeat_of_rel b64BlockElem b64BlockElem_functional`, the tail via the new
      `encodeB64Tail_of_rel` (functionality of `b64TailElem` pins the bytes), and `concat s₀ t.bytes` reassembles
      to `s` via the `t.prepend s₀ = s` transport (`prepend_prefix_read`/`splice_apply`). Supporting lemmas:
      `relB64Block_all_size3` (every block is 3 bytes), `b64Split_blocks_tail` (split-back), `encodeB64Tail_of_rel`;
      the base32 mirror is `relB32Block_all_size3` (5 bytes), `b32Split_blocks_tail` (≤ 4-byte tail),
      `encodeB32Tail_of_rel`. The `Zg==Zg==`/`MY======MY======` class is rejected by the D8 `≤ 1` guard, so the
      converse holds unconditionally. **Note:** the `- (Suffix.empty t.remaining).remaining` length in the
      `decodeRepeat_spec` tail witness leaked `Classical.choice` via `simp at` on a list-length contradiction —
      replaced with explicit `simp only [List.length_cons] … ; omega` (the `nat_lt_four`-style discipline).)_

- [ ] 4.4 Per base: `encode v = encode v' → v = v'` (injectivity). **REOPENED by review (C2).**
      _(**Status: proved, but the statement is weaker than the spec — not done.** What landed
      (`../lean-basen` `9babcab`/`6d7ba52`, `[propext, Quot.sound]`-only, zero `sorry`):

      ```lean
      -- BaseN/Base64.lean:2538  (Base32.lean:2915 identical)
      theorem encodeB64_injective {v v' : List UInt8} {n : Nat} {s : Bytes n}
          (h : encodeB64 v = some ⟨n, s⟩) (h' : encodeB64 v' = some ⟨n, s⟩) : v = v'
      ```
      and the five fixed-width twins (`Base2:561`, `Base4:455`, `Base8:589`, `Base10:411`,
      `Base16:399`) have the same both-succeed shape, e.g. `Base16.encode_injective :
      encodeHex v = some ⟨n,s⟩ → encodeHex v' = some ⟨n,s⟩ → v = v'`. The proof is the clean
      roundtrip one: both encode to `⟨n,s⟩` ⇒ `decodeFull…_roundtrip` gives `some v` and `some v'`
      ⇒ `Option.some.inj`. No boundary-pin machinery needed.

      **The gap (C2).** `specs/basen/spec.md` Scenario "Encoding is injective" states the law as
      **`encode{X} v = encode{X} v'`** — equality of the two `Option (Sigma …)` *results*, i.e. the
      `Option`-equality form `encode v = encode v' → v = v'`. The Lean statement replaces that with
      *two hypotheses both `= some ⟨n,s⟩`*, which is a strictly **different** statement:

      * it **misses the `none = none` branch** — `encode v = none = encode v'` is a hypothesis of the
        spec law that the Lean theorem simply cannot be applied to (no `some` witness exists);
      * the bridge from the spec form to the Lean form is **`encode` is total** (`encode v ≠ none`),
        which is **never proved** — grep finds no `encodeB64_ne_none`/`isSome`, no
        `encodeHex_ne_none`. It *is* true (`#eval` shows `(encodeB64 v).isSome = true` for `[]`,
        `[0x66]`, `[0x66,0x6F,0x6F]`, `replicate 100`), so the intended law holds — but the shipped
        theorem is not it, and the docstring's "a partial bijection" (Base64.lean:2535) relies on the
        unproved totality.

      **Fix (pick one, keep spec and code in agreement):**
      1. *Prove totality and restate.* Add `theorem encodeB64_ne_none (v : List UInt8) :
         encodeB64 v ≠ none` (mirror base32 + the five fixed-width `encode{X}_ne_none`), then restate
         `encodeB64_injective : encodeB64 v = encodeB64 v' → v = v'` — split the `Option` equality:
         `some/some` case → existing proof; `none/none` case → `totality v` refutes it; mixed →
         contradictory. Do the same for `encodeB32` and `Base{2,4,8,10,16}`.
      2. *Keep the both-succeed theorem but make the spec honest.* Amend the Scenario to
         "... both `= some ⟨n, s⟩`" **and** state `encode{X}_ne_none` alongside it, so the
         weakening is explicit rather than silent.
      Do **not** leave the spec sentence as-is with a differently-shaped theorem underneath it.

      **Acceptance:** `#print axioms` still `[propext, Quot.sound]`; the Lean statement, quoted next to
      the spec sentence, is *literally* the spec's form (or the spec is amended to match); a
      `#check`/doc-test shows the `none = none` case is covered.)_

## 5. Bench lane + gate

- [x] 5.1 `Bench.lean`: rewire to the uniform surface (CLOSED by 6.1) — roundtrip `example`s,
      canonical vectors (`Zg==`/`Zm8=`/`Zm9v`, `MY======`/`MZXW6YTB`), rejection
      `example`s (`Zg==AAAA`/`MY======AAAAAAAA`), converse + overflow vectors, all
      through `Codec.decodeFull`/`Codec.encode` (and `decodeFullB64`/`decodeFullB32`),
      never a bespoke fn and never a facade.
      _(**Status: the rewiring landed, but the canonical vectors prove nothing — not done.**
      The good half (`../lean-basen` `44c0edf`): every reference to the deleted
      `decodeB64Strict`/`encodeB64Strict`/`decodeB32Strict`/`encodeB32Strict` triples is gone, and the
      bench now names a base's own value throughout (roundtrips `Base{X}.roundtrip`,
      `decodeFullB64_roundtrip`/`decodeFullB32_roundtrip`; rejection flagships
      `decodeFullB64_reject_ZgAAAA`/`decodeFullB32_reject_MYAAAA`; converse
      `decodeFullB64_conv`/`decodeFullB32_conv`; injectivity; `Base8/10.rejects_overflow`).
      `lake build bench` green, zero warnings.

      **The gap (C1): the "canonical vectors" are tautologies.** `Bench.lean:101-118` contains two
      `example`s of the form

      ```lean
      example (n : Nat) (s : Bytes n) (he : Base64.encodeB64 foobar = some ⟨n, s⟩) :
          ∃ blocks m₁ m₂ blkBytes tailBytes,
            Codec.encodeRepeat b64BlockElem blocks = some ⟨m₁, blkBytes⟩ ∧
            Base64.encodeB64Tail (…(b64OfBytes foobar)).2 = some ⟨m₂, tailBytes⟩ ∧
            List.ofFn s = List.ofFn blkBytes ++ List.ofFn tailBytes := by
        obtain ⟨blocks, m₁, m₂, blkBytes, tailBytes, hblk, htail, hlen, _, _⟩ :=
          Base64.encodeB64_canonical foobar he       -- NOTE: the final `_, _`
        exact ⟨blocks, m₁, m₂, blkBytes, tailBytes, hblk, htail, hlen⟩
      ```

      `encodeB64_canonical` (Base64.lean:2230) returns **five** conjuncts; the `_, _` in the `obtain`
      **drops conjuncts 4 and 5**, which are the only two that say anything about the RFC:

      * 4 — `∀ b ∈ List.ofFn blkBytes, b64Valid b.toNat = true` (blocks are alphabet-only), and
      * 5 — the pad-arity disjunction `List.ofFn tailBytes = [] ∨ [c₀,c₁,=,=] ∨ [c₀,c₁,c₂,=]`.

      So the `example` re-states the decomposition of *whatever* `encodeB64` happened to emit and
      verifies **nothing** about the bytes: a buggy encoder (lowercase output, or wrong pad count)
      would still satisfy it. Worse, there is **no `example` anywhere** asserting the real output —
      `encodeB64 foobar = some ⟨8, "Zm9vYmFy"⟩` never appears. The only concrete base64/base32 strings
      in the bench are `b64BlockUnapply`/`b32BlockUnapply` `rfl`s at `Bench.lean:44-56`, which test the
      *block* function, never the whole-input `encodeB64`/`encodeB32`.

      **Fix.**
      1. Delete the two ∃-repacking `example`s.
      2. Add concrete whole-input value asserts for every RFC §10 vector, e.g.
         `example : Base64.encodeB64 f = some ⟨4, fun i : Fin 4 => [0x5A, 0x67, 0x3D, 0x3D][i]⟩ := rfl`
         (the repo's `Bytes n := Fin n → UInt8` function-literal idiom, as in the existing `zgAAAA`/
         `zgEqEq` vectors; use `decide`/a `List.ofFn` equality if `rfl` does not fire), for
         `f/fo/foo` → `Zg==`/`Zm8=`/`Zm9v`,
         `foob/fooba/foobar` → `Zm9vYg==`/`Zm9vYmE=`/`Zm9vYmFy`; base32
         `f/fo/foo/foob/fooba` → `MY======`/`MZXQ====`/`MZXW6===`/`MZXW6YQ=`/`MZXW6YTB`.
      3. If the existential decomposition is still wanted, keep it **with all five conjuncts** (drop
         the `_, _`) so the alphabet-only and pad-arity facts are actually exercised.
      4. Also assert the *pad-count* per tail length (base64 1→2, 2→1; base32 1→6, 2→4, 3→3, 4→1) —
         the spec's "Padding is terminal and arity-correct" scenario.

      **Acceptance (the point of the task):** a deliberately broken encoder — e.g. one emitting
      lowercase, or `Zg=` instead of `Zg==` — must **fail** `lake build bench`. Today it would not.
      Keep `#print axioms`-clean and zero warnings.)_

- [x] 5.2 `lake build` and `lake build bench` green, zero `sorry`/warnings;
      `#print axioms` = `[propext, Quot.sound]` (or `[propext]`) for the new laws;
      `nix flake check` green (checks.lean + checks.formatting).
      _(**DONE.** `lake build` (18 jobs) and `lake build bench` (43 jobs) green, zero `sorry`/warnings.
      `#print axioms` = `[propext, Quot.sound]` for every new law (`decodeFullB64_conv`/`encodeB64_injective`/
      `decodeFullB32_conv`/`encodeB32_injective`/`encodeB64_canonical`/`encodeB32_canonical`/the roundtrips/
      the rejection flagships) and every per-base `roundtrip`. `nix flake check` green: both
      `checks.aarch64-darwin.lean` and `checks.aarch64-darwin.formatting` ✅.)_
- [x] 5.3 Commit + push; update `openspec/changes/lean-basen/` (its §4.1 "no
      roundtrip dispatch" note → "each base is its own `Codec` value decoded/encoded
      by `Codec.decode`/`Codec.encode`; no facade").
      _(**DONE.** `../lean-basen` §4.1 entry rewritten to "each base is its own `Codec` value decoded/encoded
      by `Codec.decode`/`Codec.encode`; no facade, no `Base` inductive, no dispatcher", and
      `openspec validate lean-basen` is green. Commits pushed: `../lean-basen` `9babcab` (base64 converse +
      injectivity), `6d7ba52` (base32 mirror + warning fixes), `44c0edf` (bench rewire).)_

## 6. Post-review hardening (independent hyper-critical review, `../lean-basen/REVIEW-basen-rfc-conformance.md`)

> **Context.** An independent adversarial review of commits `9babcab`/`6d7ba52`/`44c0edf`
> found **zero axiom leaks** (every new law verified `[propext, Quot.sound]`-only, two
> `[propext]`-only, no `sorry`/`Classical.choice`/`native_decide`/`by_contra`) and **no
> unsound proof** — the proofs are valid _for the statements they state_. The failures are
> in **statement fidelity and honesty**: three CRITICAL (bench tautology, injectivity weaker
> than the spec, synced main spec still asserting the withdrawn "unrepresentable"/"no
> per-format function" claims), four HIGH (D7 header lies about `head?`/`filterMap`; a
> self-labelled-non-goal bench vector; `relB32Block_all_size3` proves length 5; duplicated
> Common-eligible helpers), and the MEDIUM finding that "unique canonical inverse"/"total
> characterization" (the proposal's headline) is _not_ proved — only converse + injectivity +
> named rejection vectors. These tasks close the review. Nothing here is a soundness bug.

> **Verification recipe (run from `../lean-basen`; no tooling is on the host PATH).**
>
> ```
> nix develop --command lake build        # the library: zero sorry / zero warnings
> nix develop --command lake build bench  # the bench lane (task 5.1/6.1 lives here)
> ```
>
> Axiom gate — write `/tmp/chk.lean` importing `BaseN` and, for **every** new law,
> `#print axioms BaseN.Base64.decodeFullB64_conv` … then
> `nix develop --command lake env lean /tmp/chk.lean`. Expected today (all verified at
> `44c0edf`): every law `[propext, Quot.sound]`, with `b64Split_blocks_tail` /
> `b32Split_blocks_tail` even `[propext]`-only. **A `Classical.choice` in the output is a
> regression** — the usual culprits are `simp at h` on a list-length contradiction, and
> `omega`/`decide` in a dependent context (see the `lean` skill entries dated 2026-10-25).
> `nix flake check` (checks.lean + checks.formatting) is a _long_ build — launch it
> detached (`nohup nix flake check > /tmp/fc.log 2>&1 &`) and poll the log with short
> calls; never foreground it (AGENTS.md "Long builds" rule).
> `openspec validate basen-rfc-conformance-theorems` (from `../lean-codec`) after any
> spec-delta edit, and again after any §6.6/§6.11 change.

- [x] 6.1 **Bench canonical vectors are tautologies (CRITICAL C1).** The two canonical
      `example`s in `Bench.lean` unpack `encodeB64_canonical`'s ∃-hypothesis and repack only
      conjuncts 1–3, **dropping conjuncts 4–5** (alphabet-only + exact pad-arity) — the only
      RFC content. No `example` anywhere asserts the _actual_ encoder output
      (`encodeB64 foobar = some ⟨8, "Zm9vYmFy"⟩`); the only concrete base32/64 strings are
      block-level `b64BlockUnapply`/`b32BlockUnapply` `rfl` checks, which never exercise
      `encodeB64`/`encodeB32`. So a buggy whole-input encoder would still pass. **Fix:** add
      concrete whole-input value asserts per vector (`f/fo/foo/foob/fooba/foobar` →
      `Zg==`/`Zm8=`/`Zm9v`/`Zm9vYg==`/`Zm9vYmE=`/`Zm9vYmFy`; base32 → `MY======`/…/`MZXW6YTB`)
      as `example : encodeB64 v = some ⟨k, <literal Bytes k>⟩` (prove by `rfl`/`decide`, or a
      `List.ofFn` equality); delete the ∃-repackings. **Acceptance:** a deliberately-wrong
      encoder (lowercase, or wrong pad count) must fail the bench.

- [ ] 6.2 **Injectivity stated weaker than the spec (CRITICAL C2) — NEXT, planned below.** Spec
      (`specs/basen/spec.md`, Scenario "Encoding is injective"): `encode v = encode v' → v = v'`
      (Option equality). `encodeB64_injective`/`encodeB32_injective` and the five fixed-width
      `encode_injective` all assume **both** sides `= some ⟨n,s⟩`, so they miss the
      `none = none` branch and silently rely on an unproved totality fact (no `encode…_ne_none`
      exists). **Fix:** prove `encode{X}_ne_none`/`isSome` (totality — it _is_ total, per
      `#eval`) and restate injectivity as the spec's `Option`-equality form; **or** if keeping
      the both-succeed form, amend the spec Scenario to say so explicitly _and_ state the
      totality lemma beside it. Do not leave the spec sentence mismatched.

- [ ] 6.3 **"Unique canonical inverse" / total characterization is not proved (MEDIUM M3).**
      The requirement is titled "Decode is the unique canonical inverse"; the delivered laws
      are roundtrip + converse + injectivity (three separate statements). They yield "unique"
      only with `decode s = some v ↔ ∃ v', encode v' = some ⟨n, s⟩` (decode succeeds _iff_ `s`
      is in `encode`'s image), which is **not** stated. **Fix:** add
      `decodeFullB64_char : decodeFullB64 s = some v ↔ ∃ v', encodeB64 v' = some ⟨n, s⟩ ∧ v = v'`
      (and the B32 mirror), `[propext, Quot.sound]`-only. This is what the proposal's
      "decode succeeds exactly on the RFC-valid inputs" actually means, and it subsumes 6.4.

- [ ] 6.4 **Rejection is a finite vector set, not the general law (MEDIUM M4).** The rejection
      theorems are named instances (`reject_ZgAAAA`, `reject_MYAAAA`, `reject_invalid_char`,
      `reject_pad_first`, `reject_bad_length`, `reject_overflow`). The proposal promises the
      _general_ statement. **Fix:** prove, for **all** `s`: (a) any byte `b64Valid = false` ⇒
      `decodeFullB64 s = none` (generalize `reject_first_invalid` from index 0 to all indices);
      (b) a `=` at a non-terminal position ⇒ `none` (cover the `Zg==Zg==`/`MY======MY======`
      class explicitly — currently only implicit in the D8 `≤ 1` guard, no theorem states it);
      (c) `n % 4 ≠ 0` ⇒ `none` (and `n % 8 ≠ 0` for base32). Mirror; all `[propext, Quot.sound]`.

- [x] 6.5 **Design D7 header is false (HIGH H1).** `design.md:237` says the padded decoder is
      "**not** `head?`/`filterMap`", and `:276` "This removes the flattened `List UInt8`/`head?`/
      `filterMap` step" — but `Base64.lean:866`/`Base32.lean:1009` **are** exactly
      `List.head? ((decodeRepeat …).filterMap …)`. **Fix:** either perform the D7 rewrite
      (drop `head?`/`filterMap`; use the direct `Run.decodeFull` ▸ tail composition) or rewrite
      D7's header/body to state the shape is retained and guarded by the D8 `≤ 1` bound. The
      honest note currently buried in a task parenthetical must move into D7 itself.

- [ ] 6.6 **Synced main spec still asserts withdrawn claims (CRITICAL C3).**
      `../lean-codec/openspec/specs/basen/spec.md:24-31` still says the padded bases are composed
      "so illegal 'data after `=`' is **unrepresentable**" (the proposal explicitly **withdraws**
      this: "the earlier … 'unrepresentable' … claims were false … withdrawn") and still says
      "**no bespoke `encode`/`decode`"** (the code has `decodeFullB64`/`encodeB64`/
      `decodeFullB32`/`encodeB32`). **Fix (see 6.11 for the archive hazard):** edit the synced
      requirement to drop "unrepresentable" and to qualify "no bespoke per-format function" as
      "no per-format _decoder triple_; the whole-input base32/64 composition is exposed as
      `decodeFullB{32,64}`/`encodeB{32,64}`" — or make those `abbrev`s and document them as the
      composition D7/D8 promise.

- [x] 6.7 **`relB32Block_all_size3` proves length 5 (HIGH H3).** `relB64Block_all_size3` proves
      `b.length = 3`, the base32 twin proves `b.length = 5` — same name, different content.
      **Fix:** rename to `relB64Block_len3`/`relB32Block_len5` (or `…_all_len` with a comment).

- [x] 6.8 **Duplicated Common-eligible helpers (HIGH H4 / tech-debt).** Three lemma pairs are
      structurally identical and re-derived per base: `relB{64,32}Block_all_size3` (same
      induction), `b{64,32}Split_blocks_tail` (same split-back, differing only in block size
      3/5 and tail bound 2/4), `encodeB{64,32}Tail_of_rel` (same functionality-pins-bytes shape).
      `../lean-basen/AGENTS.md` requires reusing `BaseN.Common`. **Fix:** hoist a generic
      `relRepeat_all_len {elem} {len} (h : ∀ x {m} s, Rel elem x s → x.length = len)`, a
      size-parameterized `split_blocks_tail (k : Nat)` over the per-base `split`'s defining
      equations, and a `encodeTail_of_rel` parameterized by the tail element; or at minimum add a
      docstring per base documenting the mirror and why the `split`/tail-shape stays per-base.

- [x] 6.9 **Axiom gate is manual, not automated (MEDIUM M1).** `[propext, Quot.sound]`-only was
      verified by hand this session (and a `Classical.choice` leak was already caught once — see
      the 4.3 note). AGENTS' "`#print axioms Codec.roundtrip` is the check" is not what runs here.
      **Fix:** add an `Axioms.lean` (or a `#print axioms` block wired into `lake build`) covering
      **every** new law for all seven bases, so a future `simp`/`omega` regression that picks up
      `Classical.choice` fails the build.

- [x] 6.10 **`rejects_lowercase` is a passing vector labelled a non-goal (HIGH H2 / LOW L6, N2).**
      `Bench.lean:181` is a **passing** `example` whose own comment says "not a passing vector",
      contradicting `proposal.md` ("recorded as a non-goal, **not** a passing vector"); and its
      comment says "lowercase `6f`" while the byte is `0x66` (`'f'`) and the theorem is arity-1.
      This positively enshrines an RFC §8 divergence ("a decoder MUST accept both cases") that no
      spec mentions. **Fix:** either delete the `example` and record the §8 divergence as an
      explicit spec non-goal requirement, or keep it and add the spec requirement + fix the
      comment; also add the interesting vector (`decodeFull … 2 "6f" = none`) if the two-char
      lowercase form is meant.

- [ ] 6.11 **Archive hazard: overlapping MODIFIED block (openspec integrity, E).** The
      `lean-basen` change **MODIFIES** "The `basen` bases are `Codec` values" and so would the
      6.6 fix — the AGENTS-documented "two changes each MODIFY the same requirement ⇒ archive
      silently drops one version" trap. **Fix:** apply the 6.6 edit to the **synced** spec once
      (coordinate the two changes / archive `lean-basen` first), and re-run
      `openspec validate basen-rfc-conformance-theorems` + `openspec validate lean-basen` before
      archiving; carry every existing scenario in the MODIFIED block.

- [x] 6.12 **Proof-quality cleanups (LOW L1/L2, NIT).** (a) `encodeB64Tail_of_rel`'s 4-branch
      `rcases x with _ | ⟨a,t⟩; cases t with …` cascade is overkill — `hxlen : x.length = 1 ∨
x.length = 2` is already in scope; replace with a 3-line length-dichotomy (`match x, hxlen`
      or `cases x <;> cases hxlen <;> first | rfl | omega`). (b) `dsimp only []` is a no-op —
      remove. (c) `simp only [Suffix.empty, Nat.sub_zero] at st hrelt` + `subst hst_eq` are brittle
      — prefer `cases`/explicit `cast (Nat.sub_zero …)` and a comment that the `- 0` index is what
      is being normalised. (d) `encodeB64_injective`'s docstring "partial bijection" overstates —
      it proves injectivity only (totality unproved, see 6.2).

### 6.2 — implementation plan (settled; execute in the next session)

**Decision taken: prove totality and restate injectivity as the spec's
`Option`-equality law.** The spec Scenario "Encoding is injective" says
`encode{X} v = encode{X} v' → v = v'`. Rather than weaken the spec to match the
shipped both-succeed theorems, prove the stronger law — `encode` genuinely _is_
total for all seven bases, so the spec sentence is achievable as written.

**Why it is provable (the key fact, verified this session).** For the padded
bases the only `none` branches are in `encodeB64Tail`/`encodeB32Tail`, whose
`_ => none` arms are _unreachable from a split_: `b64Split` only ever produces
tails of length 0–2 and `b32Split` 0–4, which are exactly the arms that
`Codec.encode b64TailElem`/`b32TailElem` handle (both are total on their
1/2- and 1–4-byte domains by `Rel_b64TailElem_size`/`Rel_b32TailElem_size` +
`encode_ne_none`). For the five fixed-width bases `encode{X} = encodeRepeat
{x}Elem`, and `encodeRepeat` is total when the element encoder is
(`encodeRepeat_ne_none` at `Codec/Sound.lean:719`, already proved and in use in
`Common.encodeRepeat_of_rel`).

**The change set (11 theorems + 7 restatements + 1 bench update):**

1. **Totality lemmas** (new, `[propext, Quot.sound]`-only each):
   - `Base{2,4,8,10,16}.encode{X}_ne_none : encode{X} v ≠ none` — immediate from
     `encodeRepeat_ne_none` _if_ the element relation always has a witness; if
     not, prove directly by `encodeRepeat` case analysis (no `Rel` needed).
   - `Base64.encodeB64_ne_none` / `Base32.encodeB32_ne_none` — the real work:
     unfold `encodeB64`/`encodeB32` → `encodeB64'` → the two components. Needs a
     **tail-length bound lemma** first:
     `b64Split_tail_len : (b64Split bs).2.length ≤ 2` (and base32 `≤ 4`),
     proved by `b64Split.induct` — the `_ => none` arm is then excluded by
     `omega`. Then the block run is total by `encodeRepeat_ne_none` and the tail
     by the bound + `encode_ne_none`.
2. **Restate the seven injectivity theorems** as the spec's form:
   `encode{X} v = encode{X} v' → v = v'`, disposing of the three `Option` cases:
   `some/some` → existing both-succeed proof; `none/none` → refuted by
   `encode{X}_ne_none v`; `some/none` / `none/some` → contradiction on one side.
   (A small `Option`-case helper per file keeps this 4 lines each.)
3. **Bench** (`Bench.lean`): the three injectivity `example`s currently pass
   `h h'` to the old signature — restate them in the new form.
4. **`Axioms.lean`**: add the seven `encode{X}_ne_none` laws (and the two
   tail-length bounds) to the gate. The gate pins exact text, so it will fail
   until they are added — that is the intended behaviour.
5. **Docstrings**: `encodeB64_injective`/`encodeB32_injective` lose the
   "not yet the spec's law / task 6.2" caveat added in `f5e65fa`, and may once
   again say "bijection" — this time it is earned.

**Acceptance:** the Lean statement of each injectivity law, read aloud next to
the spec's Scenario line, is _literally the same proposition_; the `none = none`
branch is covered by a `#check`-visible totality hypothesis; `lake build`
(24+ jobs), `lake build bench`, zero warnings, `Axioms` green.

**Risk / watch-items:**

- The base32 tail bound is `≤ 4` and its `encodeB32Tail` has four `some` arms;
  mirror base64 exactly rather than generalising (see task 6.8's note on why
  these stay per-base).
- `Classical.choice` is the usual accident: prefer explicit `omega`/`cases` over
  `simp at` on length contradictions (this leaked once already, per the 4.3 note).
- `b64Split.induct` needs the `case1..case4` naming; base32 has `case1..case6`.
  If `simp [b64Split]` does not close a base case, use `rfl`.

## 6.5 — Remaining order after 6.2 (the tracked queue)

Everything below is **tracked, not yet started**. Do them in this order; the
rationale is that each one unblocks or de-risks the next.

| #   | Task                                                                                                                                                                                          | Nature                                                                                                                              | Depends on                         |
| --- | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ----------------------------------------------------------------------------------------------------------------------------------- | ---------------------------------- |
| 1   | **6.3** (M3) — the "unique canonical inverse" iff: `decodeFullB{64,32} s = some v ↔ ∃ v', encodeB{v} v' = some ⟨n,s⟩ ∧ v = v'`                                                                | new theorem; after 6.2 the `→` half is `decodeFullB64_conv` and the `←` half is `decodeFullB64_roundtrip`, so it is mostly assembly | 6.2                                |
| 2   | **6.4** (M4) — generalise rejection from named vectors to the law: (a) any invalid alphabet byte at **any** index, (b) a `=` at a non-terminal position, (c) `n % 4 ≠ 0` (base32 `n % 8 ≠ 0`) | new theorems; (c) is the only genuinely hard one — it needs the arity argument lifted off the named vectors                         | 6.3 (shares the image/iff framing) |
| 3   | **6.6** (C3) — synced `lean-codec/openspec/specs/basen/spec.md:24-31` still asserts the **withdrawn** "illegal data after `=` is unrepresentable" and "no bespoke per-format function"        | spec edit                                                                                                                           | **6.11 first**                     |
| 4   | **6.11** (E) — the archive hazard: `lean-basen` change MODIFIES "The `basen` bases are `Codec` values", and the 6.6 fix would modify it again                                                 | process                                                                                                                             | coordinate; see below              |
| 5   | **4.4** — closes automatically once 6.2 lands (it is the same theorem); re-verify then flip                                                                                                   | bookkeeping                                                                                                                         | 6.2                                |

**6.11 must be resolved before 6.6, not after.** Both changes MODIFY the same
requirement block, and OpenSpec's archive takes one version silently (see
AGENTS.md "Openspec workflow"). The safe sequence is: apply the 6.6 wording to
the **synced** spec once, in whichever change syncs first, and carry every
existing scenario of that requirement into the MODIFIED block of whichever
change edits it second — then `openspec validate` **both** changes.

## 7. Follow-on change (out of scope for `basen-rfc-conformance-theorems`)

> Recorded so the scope split is explicit; create as its own change
> (`basen-rfc-total-characterization`) rather than absorbing into this one.

- [ ] 7.1 The general "decode succeeds iff `s ∈ image encode`" iff for all seven bases (the full
      consequence of 6.3 + 6.4; may simply be the 6.3 law promoted per base).
- [ ] 7.2 Either legitimately prove a type-level `B64`/`B32` that cannot represent trailing data
      (currently `B64`/`B32` is a bijective relabeling of `List UInt8`, so "unrepresentable" is
      false by construction), or keep the withdrawal and update the main spec (6.6).
- [ ] 7.3 Base16 case-insensitive decoder (RFC §8 "MUST accept both cases") — currently a non-goal;
      if pursued it breaks `Unambiguous` (per design) and needs a documented relaxation.
