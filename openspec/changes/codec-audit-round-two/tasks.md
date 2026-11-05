# Tasks

## 1. Axiom gate: a complete partition, not a name filter (C1)

- [ ] 1.1 In `Axioms.lean`, add `generatedAuxAllowlist : Array Name` and list, by
      name with a recorded reason, every declaration the gate currently drops.
      `Codec.Nat.eq_irrel` (`Codec/Codec.lean:389`) is **not** one of them — it is
      an authored theorem (its docstring explains the proof-irrelevance role it
      plays) and it moves to the gated set. `Iso.MeasureDecreases.dec`,
      `Iso.MeasureDecreasesR.dec`, `Iso.Unfold.dec` stay allowlisted with the
      reason "Prop-valued structure field, part of the type a caller supplies",
      and `Codec.findFrom.induct` with "the recursion principle of a `def`"
- [ ] 1.2 Add a build-time `run_cmd` that asserts, over every public `thmInfo` in
      `Codec`/`Iso`, membership in **exactly one** of `gatedNames` or
      `generatedAuxAllowlist`; a name in neither fails the build printing the
      name, and a name in both also fails. This is the path the existing
      `exclusions` check never covered
- [ ] 1.3 Correct the `isGeneratedAux` docstring: its claim that "none is a law a
      human wrote" is false for the three `.dec` projections and was false for
      `Nat.eq_irrel`. Restate the heuristic as a _default classifier whose
      decisions are audited by 1.2_, not as an authority
- [ ] 1.4 Regenerate `Axioms.lean`; `Codec.Nat.eq_irrel` gains its
      `#guard_msgs` block. Record the new totals in the header
- [ ] 1.5 Verify load-bearing: add a theorem whose name ends in `eq_irrel` to
      `Codec/` and confirm `lake build` fails naming it (neither gated nor
      allowlisted); restore
- [ ] 1.6 `nix develop --command lake build` — zero `sorry`, zero warnings, gate
      green

## 2. Congruence honesty: record what composes, and what provably does not (C3)

- [ ] 2.1 Record the measured `Unambiguous`/`seq` counterexample beside the
      `Unambiguous` definition in `Codec/Sound.lean`: with
      `bIso : Iso UInt8 Bool` (`apply a = if a = 0 then some true else none`),
      `bt := iso bIso byte`, `bo := alt bt (pure false)`,
      `whole := seq bo (pure ())`, the one-byte input `#[0]` yields
      `[((true, ()), 1), ((false, ()), 0)]` — two distinct values. State that
      `Unambiguous d₁ → Unambiguous d₂ → Unambiguous (seq d₁ d₂)` is therefore
      false, and that the obligation is not congruence but satisfiability
- [ ] 2.2 Decide `RelAligned`'s status under `seq` **by attempting the proof**, not
      by assumption. If it composes, state and prove it; if it does not, produce
      the refutation in the same shape as 2.1. Record which outcome was obtained
      in the module docstring. (The design pre-authorizes either outcome; a
      refutation is a successful result, not a blocker)
- [ ] 2.3 Record the same counterexample in `Codec/DecodeOne.lean` beside
      `decodeArray_unique`, noting that `RelAligned` is exactly the hypothesis
      that kills it (`bo` is not `RelAligned`) and that
      `Functional ∧ RelAligned` is the pair that closes
- [ ] 2.4 State plainly, at the `_byte` suppliers in `Codec/Sound.lean`, that they
      establish **satisfiability** and not **inheritance**: every
      uniqueness-gated law (`encode_of_decode`,
      `encode_injective_of_unambiguous`, `decodeArray_unique`,
      `decodeFull_spec`) is leaf-only in this tree
- [ ] 2.5 Correct `Codec/Sound.lean:138-141`: "every `Codec` constructor now has a
      `ConsumesByte` witness" is false — `pure` is a constructor and is refuted
      by `not_productive_pure`. Restate as every _consuming_ constructor, naming
      the refutation so the omission becomes information (D6)

## 3. Coverage: the right-fold witness, and a docstring that overclaims its role

- [ ] 3.1 Add `counterMeasureDecreasesR`, the `MeasureDecreasesR` mirror of
      `counterMeasureDecreases`. Note the type trap recorded in design D4:
      `Iso.inverse counterIso : Iso Bool (Bool × Unit)`, not
      `Iso (Unit × Bool) Bool`; go through `Iso.commute` or state the `Iso`
      explicitly. Record which construction was used
- [ ] 3.2 Confirm the new witness is `[propext, Quot.sound]`-only and that §1's
      partition gates it automatically
- [ ] 3.3 Correct `Codec/DecodeOne.lean`'s presentation of
      `decodeArray_functional_count` and `decodeArray_unambiguous_value` as "the
      hypothesis that makes the committed `decodeOne` complete":
      `decodeArray_unique` proves the composition directly and uses neither, so
      the docstrings advertise a role they do not fill. State what they actually
      establish, and that they are not a route to `decodeOne`'s completeness
- [ ] 3.4 State in `Codec/DecodeOne.lean` that `decodeOne`'s completeness remains
      **open** (the `seq` first-result commitment), so the module does not read as
      having closed it

## 4. `lean-basen`: close the base32 §3.5 gap and its false docstring (C2)

- [ ] 4.1 `nix flake update codec` + `lake update codec` **only if** a consumed
      statement changed; confirm no `decodeFull`/`decodeRepeat` statement moved
      and record whether the pin was bumped
- [ ] 4.2 Prove `b32Tail2_pad_bits`, `b32Tail3_pad_bits`, `b32Tail4_pad_bits` in
      `BaseN/Base32.lean`, mirroring `b64Tail1_pad_bits`/`b64Tail2_pad_bits`:
      2-byte tail's last character is `(v1 % 2) * 16` (4 spare bits), 3-byte's is
      `(v2 % 16) * 2` (3), 4-byte's is `(v3 % 4) * 8` (3)
- [ ] 4.3 Prove the three whole-input rejections, mirroring
      `decodeFullB32_reject_MZ`: `decodeFullB32_reject_MZTR` (`"MZTR===="`),
      `_MZTGN` (`"MZTGN==="`), `_MZTGMZR` (`"MZTGMZR="`). Each is the canonical
      encoding of `[0x66,…]` with one spare bit set
- [ ] 4.4 Replace `Base32.lean:2653-2655` with the true statement: the 1-, 2-,
      3- and 4-byte tails each carry spare bits (3, 4, 3, 3); only the 5-byte full
      block has none; and name the theorems that cover each shape
- [ ] 4.5 Add the three non-canonical vectors and their canonical counterparts to
      `BaseN/Bench.lean` so the behaviour is value-checked, not merely asserted
- [ ] 4.6 Preferred if cheap: prove the general
      `b32Tail_canonical_of_rel` (any accepted tail is one the encoder writes),
      which subsumes 4.2–4.3. If it costs more than the vectors, keep 4.2–4.3 and
      record the general form in `tasks.md` as the intended upgrade — do not
      silently drop it
- [ ] 4.7 Regenerate `BaseN/Axioms.lean` so the new theorems are gated; confirm
      0 missing, 0 duplicates
- [ ] 4.8 `../lean-basen` gates: `lake build`, `lake build bench`,
      `nix build '.#bench'` (detached; it runs the vectors)

## 5. `README.md`: three load-bearing corrections, then the smaller ones

- [ ] 5.1 `[S3]`: `Codec.takeWhile` **does not exist** (`#check` → unknown
      identifier); the triple is `relTakeWhile`/`decodeTakeWhile`/
      `encodeTakeWhile`. Fix the name and complete the inventory with the `Codec`
      values `[S3]` omits: `count`, `manyUpTo`, `optional`, `maybe`, `choice`,
      `seqRight`, `seqLeft`, `between` (`Codec/Combinators.lean`), noting which
      are bounded (hence genuine `Codec` values) — `[S6]` relies on `optional`
      without having introduced it
- [ ] 5.2 `[D2]`: refile under **Departures**. Its own body ("exposes the relation
      rather than only its fully-consuming slice") is an observable-semantics
      change, contradicting `README.md:50-52`'s definition of a strengthening.
      Also correct the premise: the paper has **two** values —
      `parse :: Parser α → … → [α]` and `data Rel α = Rel [(α, String)]` — so
      `codec` replaced an `[α]`-interpreter rather than extending a `Rel`, and the
      link to `parse` is a theorem (`decode_spec` filtered at `Suffix.empty`)
- [ ] 5.3 `[D3]`: scope the claim to `Rel`/`decode`/`encode`, and note that core
      also ships a committed-choice decoder (`Codec.decodeOne`, `alt` = `orElse`)
      that is sound but not complete. Add the multiplicity point:
      `decode (d | d) s` returns its result **twice** (list concatenation) while
      `Rel (d | d)` is idempotent `∨` — "agree by construction" means same graph,
      not same data
- [ ] 5.4 `[D7]`: `chainl1` needs a fifth obligation — `Iso.foldl`'s `apply`
      returns `none` on a non-terminal seed (`Codec/Iso.lean:661-668`), so the
      seed must be terminal. `[S4]` already states this restriction; `[D7]` omits
      it, so the two anchors currently disagree on the fold's obligations
- [ ] 5.5 `[D4]`: `Codec/Normal.lean`'s own header records that `[D4]`'s earlier
      diagnosis was "right in conclusion but incomplete"; cite that. Also state at
      the point of use that capture-verbatim is **length-preserving only**
      (`norm : Bytes n → Bytes n`), so it cannot collapse a whitespace run — the
      one thing `ignore` existed for — rather than leaving that to a later
      parenthesis
- [ ] 5.6 `[D1]`: the runtime "scalar indexed load" claim is an IR claim no
      theorem states, and sits beside the repo's own "the cursor is `Nat` and
      lowers to a boxed bignum" note (`Codec/ByteSlice.lean`). Distinguish the
      two instead of offering two unlabelled lowering claims
- [ ] 5.7 `decodeWhole`'s signature as written
      (`Codec α → ConsumesByte d → Array UInt8 → …`) is not a type, because `d` is
      passed before its witness; correct to
      `(d : Codec α) → d.ConsumesByte → …`. Same for `decodeWholeBytes`
- [ ] 5.8 `[S1]`: the composition is `≫` (`Codec/Iso.lean:134`), not the paper's
      `◦`; the two have opposite reading order, which matters for a porter. Also
      complete the iso list with the unconditional `id`, `trans`, `ofTotal`,
      `nil`, `cons`, `optionSome`
- [ ] 5.9 `[S2]`: only `Syntax → Codec` is a pure rename. `print → encode` changes
      the **argument** from a method-selected `Printer α` to an explicit
      description value — that is `[D6]`'s typeclass-to-value move, not cosmetics
- [ ] 5.10 `[D4]` paper micro-quotation: the paper's "not a strict partial
      isomorphism" sentence is about `ignore` alone, not about
      `skipSpace`/`optSpace`; and `skipSpace` re-emits the **empty** list. Quote
      and attribute correctly
- [ ] 5.11 `[D5]`: drop the unfalsifiable "could not use such a condition even if
      offered it"; the checkable statement is that `Codec.alt` carries no premise
      at all, so a prefix condition could only narrow a law that holds for free
- [ ] 5.12 `[D2]`/`[S3]`/`[S6]` inventory: add `Codec/Normal.lean`
      (`Normal`/`Normalizer`/`fill`/`decodeNormal`) to the core inventory — it is
      a public module with its own gated laws that no anchor lists
- [ ] 5.13 Re-read the whole README against the audit's list and confirm no other
      contradicting claims remain; the README's own rule is that an internal
      inconsistency between two statements is a legitimate defect

## 6. Gates

- [ ] 6.1 `nix develop --command lake build` — zero `sorry`, zero warnings, gate
      green
- [ ] 6.2 `nix develop --command lake build bench` — bench still compiles and links
- [ ] 6.3 `nix develop --command openspec validate --all`
- [ ] 6.4 `nix flake check` (detached with `nohup`, never foregrounded)
- [ ] 6.5 `../lean-basen`: `lake build`, `lake build bench`, `nix build '.#bench'`
- [ ] 6.6 Commit per task family (gate / congruence / coverage / basen / README),
      individual files only, printing `git diff --cached --name-only` before each
