# Changelog

All notable changes to this project are documented in this file.

The format follows [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Added

- `Codec.ByteSlice.byteSlice_spec`: the `byteSlice` trust seam's Lean law
  (`byteSlice a i = ByteArray.mk (a.data.extract i.toNat a.data.size)`, `rfl`).
  `byteSlice` was the one Layer-2 seam with a body and prose but no theorem fixing
  it, while `blitBytes`/`findByte` each had a `*_spec` — so the C's contract ("the
  C matches the Lean body") had no machine-checkable referent for it.
  `commitRemainder_spec` now derives from it rather than re-deriving the body.
  Every seam law now states its own axiom footprint, which is **not** uniform:
  `byteSlice_spec`/`blitBytes_spec`/`commitRemainder_spec` report no axioms,
  `findByte_spec` reports `[propext]` (its `Array.findIdx?` goes through
  `DecidableEq UInt8`).
- `Codec.Sound.unambiguous_byte` / `functional_byte` and
  `Codec.decodeArray_functional_byte` / `decodeArray_unambiguous_byte`:
  `Unambiguous`/`Functional` established for a concrete codec, at both the `Rel`
  and `decodeArray` levels. Both predicates had only ever been _hypotheses_, so a
  typo in either definition could not surface; the instances are verified
  load-bearing by mutating `Unambiguous` to quantify over two independent byte
  strings, which makes the proposition refutable.

- `Codec.Normal`: the information-free-variation layer. `Normal S norm` (the
  quotient of a concrete syntax by an information-free variation, reified as the
  fixed points of a total idempotent `norm`), `Normalizer S norm` (carrying
  idempotence in the type rather than as a per-call proof argument), `fill` (the
  canonical representative), and `decodeNormal` (the normalising decoder — `norm`
  composed **outside** a strict `Iso`, explicitly not an `Iso` and having no
  inverse). Laws: `fill_fixed` (`norm ∘ fill = id` on the quotient, no axioms),
  `fill_surj` (faithfulness of the fixed-point reification), `fill_inj` (two
  spellings share a class iff they normalise equally), `decodeNormal_of_fixed`, and
  `decodeNormal_encode` (with the per-codec obligation that the encoder emits a
  normal form). `Iso.law` is untouched — the quotient lives in the object, so RFC
  4648 §8 case-insensitivity becomes possible without weakening the inverse law.
  Length-preserving normalizers only; README `[D4]` sharpened accordingly.
- `Codec.Normal`'s first downstream consumer: `../lean-basen` `BaseN/Base16.lean`
  now provides RFC 4648 §8 case-insensitive decoding — a length-preserving ASCII
  case fold (`foldByte`/`foldList`/`foldByteBytes`) applied **outside** the strict
  `Iso`, folded **up** so the canonical uppercase encoding is a fixed point
  (`hexBlockIsoF : Iso UInt8 (Normal (List UInt8) foldList)`, `decodeHexFold`,
  `decodeHexFold_lowercase_eq`). Confirms the layer's design: `Iso.law` was not
  touched, and only decoding widens.
- `Codec.Combinators` chain-combinator decode→encode and injectivity companions
  (`encodeChainl1_ne_none`/`encodeChainr1_ne_none`,
  `encodeChainl1_of_decode`/`encodeChainr1_of_decode`,
  `encodeChainl1_injective_of_unambiguous`/`encodeChainr1_injective_of_unambiguous`),
  mirroring the primitives, stated over the new relation-level
  `relFunctional`/`relUnambiguous` predicates (see `Codec.Sound`).
- `Codec.Sound`: `relFunctional`/`relUnambiguous` (the relation-level forms of
  `Functional`/`Unambiguous`) and `encodeRepeat_ne_none` (`relRepeat`-level
  encoder completeness).
- `Bytes` (`abbrev Bytes (n : Nat) : Type := Fin n → UInt8`) as the named
  **length-indexed** proof substrate — one byte-string type for both the spec and
  its scalar-read run-model, with no second `List`/`Array`/`ByteArray` carrier for
  the laws (see README `[D1]` and "Representations").
- A `bench` `lean_exe` (`Bench.lean`, `root := `Bench`) and the
`default.nix#bench`/`flake.nix` `bench` package. It is a plain executable —
Lean's ordinary C backend compiles it — that additionally links the Layer-2
seam object (`Codec/ByteSlice.c`, via `moreLinkObjs`). It is **not** a
  C-extraction step; there is none in the lakefile.

- `Iso.ofTotal f g hgf hfg`: **a total bijection is an `Iso`**, with the inverse
  law discharged from the two round-trip equations. The `Iso` fields are partial and
  its `law` is an `↔` over both directions — right for the theory, but a concrete
  leaf codec (a fixed-width integer, a base-N element) needs no partiality, only a
  pair of mutually inverse total functions. Without this the only way to express one
  was to fill three fields and close the `↔` by hand. It deliberately does not
  express a _partial_ leaf; for those the `Iso` structure remains the tool, which is
  the `[D4]` lesson (capture, don't discard), so the two forms are complementary.
- `Codec.seqConsumesByte` / `Codec.isoConsumesByte`: `ConsumesByte` (the
  productivity witness every whole-buffer decoder takes as a parameter) **derived**
  for `seq` and `iso`. It had been supplied only for leaves (`byte`, `satisfy`) and
  for `alt`, so the shape every composed codec takes had no witness at all — the
  `lean-basen` repo hand-proves `ConsumesByte` per block, which is the cost this
  removes. `seqConsumesByte` reuses `decode_seq_mem`, which is why it lives in
  `Codec/Sound` rather than beside `altConsumesByte` in `Codec/Decode` (no cycle
  would allow the latter).
- `Codec.decodeWholeOne` / `Codec.decodeWholeOneBytes`: **decode a whole buffer as
  exactly one value**, with `decodeWholeOne_eq` tying it to `decodeFull`. The
  existing wired surfaces answer "how many values does this buffer hold"
  (`Option (List α)`), which is the wrong question for a single-value codec, and
  there was no wired entry point for the single-value case at all: `decodeOne`
  threads a cursor but is the committed-choice decoder, unproven against the
  specification and unwired, while `decodeFull` is the repetition form. Defined as
  the projection of the wired surface (`decodeWhole` at a singleton) so every law
  about `decodeWhole` reads off without a second decoder whose agreement would need
  establishing. A buffer holding two values returns `none` rather than taking a
  prefix — that is the documented `decodeFullArray` head-projection defect, not a
  behaviour to repeat.
- `Codec/CRef.c` + `Bench.lean`'s `benchCReference`: a **hand-written C reference
  parser**, bench-only. Every ratio in this package was previously relative to its
  own pure-Lean cursor floor; `AGENTS.md` records that a `memcpy` ratio is a
  category error for a per-element codec and that the honest reference is a C
  parser. It is **not** Layer 2 and not a trust seam: no `@[extern]` in `Codec/`,
  nothing proven depends on it, it is excluded from the `#print axioms` gate by
  construction, and it is linked into `bench` only. It decodes one value per byte
  (the same job `decodeWhole Codec.byte` does, including the `n`-element value
  array) and is value-checked against `decodeWhole` before it prints.

### Changed

- Wrapped the denotation (`Rel`/`relRepeat`/`Productive`/`single`) in
  `namespace Codec`, so they live at `Codec.*` uniformly beside `Codec.decode`/
  `Codec.encode`/`Codec.roundtrip` (the `Codec` _type_ is unchanged — a type and
  a same-named namespace coexist).
- `Codec.Iso`: deleted the dead `app`/`unapp` wrappers and the redundant `comp`
  (kept `trans` + `≫`); inlined `foldlApply`/`foldrApply'` into `foldl`/`foldr`'s
  `apply` field, removing the ad-hoc `'` prime.
- `Codec.Codec`: restored `Rel_seq`/`Rel_empty` for a complete, constructor-ordered
  `Rel_iso`–`Rel_byte` lemma set.

## [0.1.0] — initial release

### Added

- `Codec.Iso` — partial isomorphisms with the inverse law as a _field_, plus the
  category structure, the product bifunctor, the structural isos (`nil`/`cons`/
  `unit`/`commute`/`associate`/`element`/`subset`/`inverse`/`optionSome`), and the
  well-founded `foldl`/`foldr` folded isos.
- `Codec.Codec` — the `Codec` description AST (`iso`/`seq`/`alt`/`empty`/`pure`/
  `byte`) and the denotational relation `Rel`.
- `Codec.Decode` — the nondeterministic (backtracking) decoder, plus
  `decodeRepeat`/`ConsumesByte` for productive repetition.
- `Codec.Encode` — the partial encoder, plus the total `encodeRepeat`.
- `Codec.Sound` — the unconditional laws (`encode_rel`, `decode_spec`, `bidir`,
  `decode_encode`, `roundtrip`, `productive_iff_consumesByte`,
  `decodeRepeat_spec`, `encodeRepeat_rel`) and the decode→encode companions
  (`Unambiguous`/`Functional`/`encode_ne_none`/`encode_of_decode`/
  `encode_injective_of_unambiguous`).
- `Codec.Combinators` — the derived combinators (`seqRight`/`seqLeft`/`between`,
  `optional`/`maybe`/`choice`, `count`/`manyUpTo`) and the semantic repetition
  split re-derived as `relRepeat`/`decodeRepeat`/`encodeRepeat` triples
  (`relSepBy`/`decodeSepBy`/`encodeSepBy`, `relChainl1`/`relChainr1` and their
  `decode*`/`encode*` forms).

### Changed

- Restored the paper's **backtracking-union** `|` (the committed-choice `|` and
  its `NonNull`/`PrefixDisjoint`/`Disjoint` machinery were removed), making the
  laws unconditional.
- Removed the `partial def many` (its `Rel` was irreducibly opaque); unbounded
  repetition now lives as `relRepeat`/`decodeRepeat`/`encodeRepeat`.

### Notes

- Zero `sorry` / zero warnings across all modules.
- The axiom footprint of every law is `[propext, Quot.sound]` (and `[propext]`
  only for `relRepeat_induction`/`encodeRepeat_ne_none`); never `Classical.choice`.
- Dual licensing: AGPL-3.0-or-later, or a commercial license from the author
  (see `LICENSE.md`).
