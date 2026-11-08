# Changelog

All notable changes to this project are documented in this file.

The format follows [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Fixed (corrections, not features — `codec-audit-round-nine`)

- **A withdrawn performance figure.** `README.md`'s `decodeFullFastRoot` cold cell
  read `77 ns/step`. The lane that would produce it (`benchDecodeFullFast`) value- and
  bridge-checks the decoder and **prints no timing at all**, by design: every in-process
  attempt gave an impossible number (`0 ns/op`, then `41 ns/op`), so the lane was
  reduced to a check. The `77` traces to
  `openspec/changes/archive/2026-11-01-codec-review-remediation/tasks.md:2407` — an A/B
  **control** column at `n = 65536` measured in **`ns/byte`**, on **2026-11-01**, i.e. a
  different date, `n` and unit borrowed into an `ns/step` column of a two-run table
  captioned "from the same two-run session". The cell is now `see note`, with the
  provenance recorded. This is the citation form of the subtraction this repository
  already forbids, and the same defect one row above (`49 ns/step`, round eight).
- **Two docstring footprint claims the gate contradicted.** `blitBytes_spec` and
  `commitRemainder_spec` each stated the two-axiom footprint; `#print axioms` measures
  **no axioms** for both. Corrected to the measurement, with the gate's `#guard_msgs`
  named as the authority in both docstrings.
- **A standards misquote, in three places rather than two.** RFC 4648 §8 does not
  require a Base16 decoder to accept lowercase; it **permits** it. `Codec/Normal.lean`
  said "requires" twice (once inside quotation marks, as the standard's text) and
  `Bench.lean` carried the same wording a third time — a site no reviewer flagged.
  All three corrected; the standard's own sentence is now quoted in the module header.
- **`decodeNormal`'s loss attributed to the wrong function.** It said it has no inverse
  "because `norm` is many-to-one". The loss is `fill`'s identification of every spelling
  in one class (now citing `fill_inj`); `norm` many-to-one is what makes the quotient
  exist, and such a map is injective _on_ the quotient. The same constancy-vs-quotient
  distinction `README [D4]` spends forty lines on, reproduced two files away.
- **The bench's burst lane could not detect a fold it existed to detect.** `benchBurst`
  ended with `if sink == 0 then throw`, and the sink was a **constant `7`** on every
  multi-call row: `sinkOfList` is `a*31+b` from seed `7`, `31a+1 mod 256` has period 16,
  and each row measured a 512-byte window of an all-`1` buffer. The guard passed while
  the loop was invariant. The shared buffer now has a non-uniform tail
  (`i % 251`), and `benchBurst` **asserts non-invariance** (`eraseDups ≥ 2`) plus a
  not-all-zero test, names the offending row in its error, and runs the probe outside
  the timed window. `arrayRead`'s invariant sink was a separate `measure` defect (it
  read indices `0..39` of a buffer that varied only at index 0) and is fixed in
  `measure`.
- **`benchCReference` could silently skip both timed lanes.** `| none, none => return ()`
  exits `benchCReference` rather than continuing the loop, so one `none` from the C
  skipped the comparison _and_ both lanes while the process still exited 0. Every
  disagreement now throws, the cross-check set gains `n = 0` and `n = 1` (the C's two
  real branches), and the count is asserted and printed (`6 of 6 inputs agree`).
- **`Codec/CRef.c`'s comment described a `none` arm the code does not contain.**
  Replaced with the fact: the function is total, `n = 0` decodes to `some #[]`, and a
  `none` arm would disagree with `decodeWhole` on exactly the input the cross-check now
  covers.
- **`Codec.findFrom.induct` promoted to the gated set.** It measured `[propext]` — the
  only allowlisted name with a non-zero footprint — which falsified the allowlist
  group's stated property ("not a law ⇒ free of axioms"). It is pinned like any law, and
  `Codec.findFrom`'s coverage is now an asserted number: six gated theorems name it that
  are not its own recursion principle.

### Added

- **The footprint arm now audits its own vocabulary.** It recognised
  `` `[propext, Quot.sound]`-only `` and not the bare spelling, so a docstring stating a
  two-axiom footprint without the suffix was not checked, not skipped and not out of
  scope — it **did not exist** as a claim site. Measured with an independent, markup-only
  predicate: 155 `thmInfo` docstrings contain a backticked axiom-list literal, 137 were
  recognised, **18 were blind** (six of them because the literal is wrapped across a
  newline, which no vocabulary width could match). The vocabulary gained the bare forms,
  every new label got an arm, and the arm now asserts
  **`recognised + blind + exempt = mentioningLiteral`** with `blind = 0` — the
  denominator/decomposition rule applied to the matcher itself. Mutation-tested: dropping
  a spelling fails the build naming the docstrings it was reading.
- **`checks.bench`**: the benchmark binary is now built **and run** in the flake checks,
  failing on a non-zero exit and on a missing value-check line. Its runtime checks were
  reachable from nothing before, so a broken C reference or an invariant burst row could
  not fail CI. `lean_exe bench` also carries `-DwarningAsError` now (an exe root is a
  separate root; the library's flag did not reach it).
- **`Axioms.lean` arms for four escape routes**: an `authored`-exemption validity arm
  (which measured the exemption to be **dead code** — `Codec.Nat.eq_irrel` matches no
  suffix pattern, so the classifier never dropped it), a **footprint report for every
  allowlisted theorem** (`82 = 39 + 24 + 19`, with `Classical.choice` asserted zero), a
  **global** constant-kind census (all 12 axioms in the process asserted by name), and a
  recursion-principle coverage accounting.
- **`README [S5]`: the `relRepeat` departure**, which was a _choice_ and was undocumented
  — the `nil` branch is `n = 0`, not the paper's `True`, because the substrate's length
  lives in the type. That is what makes `relRepeat_induction` an induction on the list,
  and a porter who copies the paper's form cannot close the `[]` case.

- `Codec.ByteSlice.byteSlice_spec`: the `byteSlice` trust seam's Lean law
  (`byteSlice a i = ByteArray.mk (a.data.extract i.toNat a.data.size)`, `rfl`).
  `byteSlice` was the one Layer-2 seam with a body and prose but no theorem fixing
  it, while `blitBytes`/`findByte` each had a `*_spec` — so the C's contract ("the
  C matches the Lean body") had no machine-checkable referent for it.
  `commitRemainder_spec` now derives from it rather than re-deriving the body.
  Every seam law now states its own axiom footprint, which is **not** uniform:
  `byteSlice_spec`/`blitBytes_spec`/`commitRemainder_spec` report no axioms,
  `findByte_spec` reports `[propext]` (its **`findFrom`** scan reads `a[k]?`, so the
  bound is propositional and no `DecidableEq UInt8` decision is consulted; the
  _earlier_ `Array.findIdx?` body is what went through `DecidableEq UInt8` and reached
  `Classical.choice` — a re-read of this entry before the rewrite attributed the clean
  footprint to the body that had already been replaced, `codec-audit-round-eight`
  S-3).
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
