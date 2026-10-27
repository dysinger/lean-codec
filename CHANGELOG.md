# Changelog

All notable changes to this project are documented in this file.

The format follows [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Added

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
- `Codec.Buffer`: the packed, `ByteArray`-backed transport surface — `Buffer`
  (newtype over `ByteArray`), `toBytes`/`ofBytes` (routed through
  `ByteArray.data`, the reducible `Array`), and the transported interpreters
  `decodeBuffer`/`encodeBuffer` with the bar-transferred laws
  (`decodeBuffer_eq`/`encodeBuffer_eq`/`decodeBuffer_spec`/`roundtripBuffer`).
- `Bytes` (`abbrev Bytes (n : Nat) : Type := Fin n → UInt8`) as the named
  **length-indexed** proof substrate — one byte-string type for both the spec and
  its scalar-read run-model, with no second `List`/`Array`/`ByteArray` carrier for
  the laws (see README `[D1]` and "Representations").
- A `bench` `lean_exe` (`Bench.lean`) and the `default.nix#bench`/`flake.nix`
  `bench` package: extracts the `decode`/`encodeRepeat`/`decodeRepeat`/`Buffer`
  transport hot path to C and links it against the Lean runtime (`§10.5`).

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
