# Tasks — `codec-audit-round-four`

**Issue ledger: 37 numbered findings** (`R5-01` … `R5-37`), from the round-five
audit. Every one is listed below with its location, its evidence, and the fix. Nothing
is dropped, including the 17 nitpicks — a nitpick left in the code is how the next
round's MUST-FIX starts.

**Two numbering systems, and they are off by one — this is not a typo.**
`codec-audit-round-four` is the **change** name (the fourth audit _change_); its
findings come from the **fifth review round** (rounds one to three produced
`codec-audit-remediation`, `-round-two`, `-round-three`; the fourth review fed
`-round-three` as a follow-up, so this review is the fifth). Hence the change is
`round-four` and the ids are `R5-nn`. When this archives it will be
`<date>-codec-audit-round-four`, and the _next_ review's findings will be `R6-nn` in a
change called `round-five`.

Evidence base: `/tmp/r5-a-vacuity.md` (910 lines), `/tmp/r5-b-departures.md` (1658
lines), `/tmp/r5-c-cross.md` (521 lines), merged ledger `/tmp/r5-SYNTHESIS.md`.
Main-agent verification probes: `/tmp/verify/*.lean`.

**`/tmp` does not survive a reboot.** Every proof this ledger depends on is therefore
**inlined below** rather than left as a path — if a `/tmp` reference is missing, the
task still has its content. The reports are cited for provenance only; no task requires
reading them. If `/tmp/r5a/p2.lean` is gone, §1.2's two terms are still fully specified
there in prose.

**Verification status of the findings.** Every MUST and SHOULD item was independently
re-derived by the main agent before being written here (marked ✔). One item is
**predicted, not run** (§6.3) and says so.

## Severity key

- **MUST** — a false claim, a broken gate, or a stale dependency. Six findings.
- **SHOULD** — an over-claim that steers a reader wrong, or an absent law that was
  advertised. Fourteen findings.
- **NITPICK** — a wording error, a dead lemma, a mis-citation. Seventeen findings.

## Issue ledger (the index — every id appears in exactly one section below)

| id    | sev     | repo  | location                                               | one-line                                                                                    |
| ----- | ------- | ----- | ------------------------------------------------------ | ------------------------------------------------------------------------------------------- |
| R5-01 | MUST    | codec | `Codec/Sound.lean` `LengthDet`/`RelAligned` docstrings | `LengthDet → RelAligned` recorded OPEN; **refuted**, ✔reproduced                            |
| R5-02 | MUST    | codec | `AGENTS.md`, archived ledger                           | same false "open" claim in two prose sites                                                  |
| R5-03 | SHOULD  | codec | `Codec/Packed.lean`                                    | two `rfl` identity unfolds satisfy the def proxy; header says "has a stated law"            |
| R5-04 | SHOULD  | codec | `Codec/Packed.lean`                                    | `decodeWholeBytes`'s advertised law absent; ✔**fix proved**                                 |
| R5-05 | SHOULD  | codec | `Codec/Sound.lean`                                     | `huniq_not_derivable` does not state the claim cited for it; ✔**fix proved**                |
| R5-06 | SHOULD  | codec | `Codec/Sound.lean`                                     | `RelAligned` "third family" framing; they are incomparable                                  |
| R5-07 | NITPICK | codec | `Codec/Codec.lean`                                     | `min_rotate` dead + false dependency claim                                                  |
| R5-08 | NITPICK | codec | `Codec/Combinators.lean`                               | `Rel_manyUpTo` redundant `∃ k`                                                              |
| R5-09 | NITPICK | codec | `Codec/Combinators.lean`                               | `Rel_seqLeft` has no docstring                                                              |
| R5-10 | NITPICK | codec | `Axioms.lean`                                          | defs table "has a stated law" over-reads                                                    |
| R5-11 | MUST    | codec | `README.md` `[D4]`                                     | "Lossless capture" title advertises a length-preserving answer to a length-changing problem |
| R5-12 | MUST    | codec | `README.md` `[S1]`                                     | "the full unconditional-iso list" omits `foldl`/`foldr`                                     |
| R5-13 | SHOULD  | codec | `Codec/Sound.lean`                                     | `decodeRepeat_mem_iff`'s "only step relation" reason is false; ✔general form proved         |
| R5-14 | SHOULD  | codec | `Codec/Packed.lean`                                    | `length_filterMap_le` calls `packedCands` a `filterMap`; it is a `map`; zero callers        |
| R5-15 | SHOULD  | codec | `Codec/DecodeOne.lean`                                 | "sound only when" contradicts unconditional `decodeOne_mem`                                 |
| R5-16 | SHOULD  | codec | `Codec/Sound.lean`                                     | "Satisfied by `byte` (`relUnambiguous` at `Bytes 1`)" — lemma does not exist                |
| R5-17 | SHOULD  | codec | `README.md` `[S2]`                                     | `print` misdescribed as a typeclass method                                                  |
| R5-18 | SHOULD  | codec | `README.md` `[S3]`                                     | "none has an in-tree caller" false for `isoConsumesByte`; ✔verified                         |
| R5-19 | SHOULD  | codec | `README.md` `[S3]`                                     | "complete `Codec`-value inventory" has a row with zero `Codec` values                       |
| R5-20 | NITPICK | codec | `Codec/Combinators.lean`                               | "only `relTakeWhile_cast` is new" — the fourth law's proof is new too                       |
| R5-21 | NITPICK | codec | `Codec/Iso.lean`                                       | still uses the phrase `README [D7]` disowns                                                 |
| R5-22 | NITPICK | codec | `Codec/Codec.lean`                                     | "typeclass reading would prevent the types" — false                                         |
| R5-23 | NITPICK | codec | `README.md` `[D2]`                                     | "the paper has two values" — three, counting `print`                                        |
| R5-24 | NITPICK | codec | `README.md` `[D4]`                                     | capture-verbatim "over a `subset p byte` step" — it is `Codec.satisfy p`                    |
| R5-25 | NITPICK | codec | `README.md` module table                               | `Normal.fixed`/`Normalizer.idem` are projections, not laws                                  |
| R5-26 | NITPICK | codec | `README.md` `[S4]`                                     | "fresh derivations" vs `Iso.lean`'s "factored once"                                         |
| R5-27 | NITPICK | codec | `README.md`                                            | `Nat`-cursor lowering cited to the wrong file                                               |
| R5-28 | NITPICK | codec | `README.md` `[D8]`                                     | `satisfy` reason does not explain why `subset` was converted                                |
| R5-29 | NITPICK | codec | `README.md` `[S1]`                                     | "no hypothesis" while `element`/`subset` take class args                                    |
| R5-30 | NITPICK | codec | `Codec/Normal.lean`                                    | "decidable idempotent `norm`" — no `Decidable` field exists                                 |
| R5-31 | SHOULD  | basen | `Bench.lean`                                           | lane does not pin whole-string encoder values or padded-base decodes                        |
| R5-32 | SHOULD  | basen | `BaseN/Base16.lean`                                    | even-arity lowercase witness has no positive counterpart theorem                            |
| R5-33 | MUST    | basen | `flake.lock`                                           | codec pin 27 commits stale; ✔verified                                                       |
| R5-34 | SHOULD  | basen | `Axioms.lean`                                          | prose says 440/437/483, reality 441/438/484; ✔verified                                      |
| R5-35 | NITPICK | basen | `Axioms.lean` log line                                 | "438 + 46 = 447 of 484" is arithmetically false                                             |
| R5-36 | MUST    | basen | `Axioms.lean`                                          | missing the definition-coverage check; 8 dead `*Run` values; ✔verified                      |
| R5-37 | NITPICK | codec | `Codec/CRef.c`                                         | bench-only C parser sits inside `Codec/`                                                    |

---

## 1. The one false mathematical claim (R5-01, R5-02)

Highest priority: this is a _mathematical_ error, not a wording one, and it survived
three archive rounds because every gate checks theorems and this was a claim about the
_absence_ of one.

- [ ] 1.1 Land `lengthDet_relUnambAlignedWitness` and
      `lengthDet_not_implies_relAligned` in `Codec/Sound.lean`. **R5-01.** ✔Verified
      `[propext]`-only by the main agent (`/tmp/verify/m1.lean`). The witness
      `relUnambAlignedWitness` is already in the tree; the theorem is ~20 lines of
      `match` on the two length indices. Statement of the second:
      `¬ (∀ {α} (R : α → {m : Nat} → Bytes m → Prop), LengthDet R → RelAligned R)`.
- [ ] 1.2 Land the **strong form** with productivity added as a second hypothesis, so a
      reader cannot attribute the failure to productivity's absence. **R5-01**, design
      §D1. Needs two more terms, both transcribed verbatim from the auditor's probe
      `/tmp/r5a/p2.lean` (still on disk; do not re-derive):
      `prod_relUnambAlignedWitness : ∀ a {m} (t : Bytes m), relUnambAlignedWitness a t →
m ≠ 0` (a `match` on `m`, four arms), and
      `lengthDet_not_implies_relAligned_productive :
¬ (∀ {α} (R), LengthDet R → (∀ a {m} (t : Bytes m), R a t → m ≠ 0) → RelAligned R)`,
      closed by `relUnambiguous_not_implies_relAligned` applied to the two witnesses.
      Method that works: copy `p2.lean`'s bodies — they are `match`-on-`m` throughout;
      a `match` on `t` as well as `m` fails to refine the hypothesis (see 1.3's note).
- [ ] 1.3 Land `relAligned_not_implies_lengthDet` (the other direction), completing the
      four-way diagram. **Corrected**: the auditor's report _names_ this theorem but its
      probe files do **not** contain it — the name appears only in prose. It is therefore
      **not** verified from the audit; the main agent proved it and the working proof is
      `/tmp/verify/i3.lean` (`[propext, Quot.sound]`-only). Transcribe:
      `alignedNotLengthDetWitness a := (m=1 -> a = true) | (m=2 -> a = true) | False`
      (one value at **two** lengths — `RelAligned` holds because no second value relates
      at all, so the conclusion `a = b` is discharged from `a = true`; `LengthDet` fails
      at `true`/1 vs `true`/2), then
      `relAligned_not_implies_lengthDet : ¬ (∀ {α} (R), RelAligned R → LengthDet R)`.
      **Proof note (cost me one failed attempt):** in `aligned_alignedNotLengthDetWitness`
      match on `m₁`/`t₁`/`h₁` and then on `m₂`/`t₂`/`h₂` — matching only on `m₂` leaves
      `h₂` unrefined and the `m=1 × m=2` arm cannot close. The `m₁=2, m₂=1` arm is
      `exact absurd hle (by omega)`.
- [ ] 1.4 Replace `def LengthDet`'s "**open**: it may or may not hold, and no theorem
      settles it either way" paragraph (and the parenthetical about the earlier
      `DecidableEq` story) with the refutation. **The "diagram" is a markdown table in
      the docstring with exactly these six rows** — copy it from design §D1; each row
      names a theorem that exists after §1.1–§1.3 or in the tree already:
      `LengthConst → LengthDet` (`lengthDet_of_lengthConst`) ·
      `RelAligned → relUnambiguous` (`relUnambiguous_of_relAligned`) ·
      `relUnambiguous ↛ RelAligned` (`relUnambiguous_not_implies_relAligned`) ·
      `relUnambiguous ↛ LengthDet` (`lengthDet_not_implied_by_unamb`) ·
      `LengthDet ↛ RelAligned` (`lengthDet_not_implies_relAligned`) ·
      `RelAligned ↛ LengthDet` (`relAligned_not_implies_lengthDet`). **R5-01.**
      Put the table in `LengthDet`'s docstring; `RelAligned`'s (1.5) cross-references it
      rather than repeating all six rows.
- [ ] 1.5 Replace `def RelAligned`'s "**`LengthDet` is a third, separate family** …
      plausible but unproved here … recorded as open" paragraph with: (a) the measured
      incomparability, cross-referencing 1.4's table; (b) why the pair is _jointly_
      load-bearing in `relRepeat_cons_eq` — `hld` is used exactly once, at
      `have hmm : m = m' := hld a a' hRa (hxy ▸ hRa')`, i.e. **after** `hal` has already
      identified `a₀ = b₀`, to conclude the two step-lengths agree. So neither hypothesis
      can be dropped. (**R5-06**; reviewer A's S4.)

- [ ] 1.6 Delete `AGENTS.md`'s clause "and `LengthDet → RelAligned` (neither proved nor
      refuted)" from the "three items open in code" list, and fix the "Three items"
      count that depends on it. **R5-02.**
- [ ] 1.7 Annotate the archived round-three ledger's `:77` entry — **do not rewrite
      it**. A ledger records what was believed then; rewrite and the fact that it was
      wrong for three rounds disappears. Add a one-line dated note pointing at the
      refutation. **R5-02.**

## 2. Advertised laws that are absent (R5-04, R5-13)

Both fixes are already proved by the main agent; this section is transcription plus
docstring repair.

- [ ] 2.1 Add three lemmas to `Codec/Packed.lean`, next to `decodeWholeBytes_eq`. The
      names below are the ones the verified proof uses; keep them (they are descriptive
      and the `_apply`/`_eq` convention matches `bdrop_*`/`prepend_*`):
      `arrayToBytes_bytesToArray_apply` (pointwise, `Array.getElem_toList` +
      `List.getElem_ofFn`), `arrayToBytes_bytesToArray` (the `cast`-form transport),
      `decodeWholeBytes_spec`. The short proof above `decodeWholeBytes_spec`
      (`spec_aux`, taking `k`, `hk : k = n`, `a`, `ha` abstract) is a **local helper** —
      make it a `private theorem` or fold it into the main proof; it is not public
      surface and needs no gate entry. **R5-04.** ✔Proved (`/tmp/verify/s2z.lean`),
      `[propext, Quot.sound]`-only. **Three traps recorded in design §D3 and all three
      fired:** the docstring's "`rfl` by `funext`/`Fin.ext`" is wrong (needs
      `Array.getElem_toList` + `List.getElem_ofFn`; `Array.getElem_mk` and
      `Array.getElem_eq_getElem_toList` do **not** exist in 4.35.0); a `simpa` on the
      dependent `Fin` bound **leaks `Classical.choice`** (write
      `Nat.lt_of_lt_of_eq i.isLt (bytesToArray_size s)`); and the final dependent rewrite
      cannot be `rw`/`subst`/`generalize`.
- [ ] 2.2 Correct `decodeWholeBytes_eq`'s docstring: it claims the right side "is
      `decodeFull d h n` applied to the readback — i.e. the law a caller who started
      from `Bytes n` would state", and it is not. Point at `decodeWholeBytes_spec` once
      2.1 lands, and replace the false "`rfl`" claim with the two bridge lemmas.
      **R5-04.**
- [ ] 2.3 Add `decodeRepeat_mem_iff_general` to `Codec/Sound.lean`. **R5-13.**
      ✔Proved by both the auditor and the main agent (`/tmp/verify/b3.lean`),
      `[propext, Quot.sound]`-only, and it is a character-for-character rename of the
      specialised proof.
- [ ] 2.4 Rewrite `decodeRepeat_mem_iff`'s docstring. It says the specialisation is
      forced because `Codec.byte` is "the only step relation whose `∃ s₀` collapses for
      free" — **false**: `prepend_empty_self`'s statement mentions no step relation at
      all, so the collapse is uniform. State that the specialisation is a convenience
      kept because it is the instance `huniq_byte` needs, and name the general form.
      **R5-13.**

## 3. The `huniq` claim is carried by the wrong theorem (R5-05)

- [ ] 3.1 Add the `∃ R` form as a **new name `huniq_not_derivable_full`** — do **not**
      restate the existing `huniq_not_derivable`: `Axioms.lean` pins the existing one by
      name, and a rename would invalidate the archived ledgers' references. ✔Proved
      (`/tmp/verify/s3.lean`), `[propext, Quot.sound]`-only, by packaging the three
      existing `uniqCounterexample_*` lemmas:
      `∃ (R : Bool → {m : Nat} → Bytes m → Prop), relUnambiguous R ∧
 (∀ a {m} (t : Bytes m), R a t → m ≠ 0) ∧
 ¬ (∀ (xs ys : List Bool) (n : Nat) (s : Bytes n),
     relRepeat R xs n s → relRepeat R ys n s → xs = ys)`.
      Keep the existing `n = 2` version as the small witness. **R5-05.**
- [ ] 3.2 Point the section header's "machine-checked below as `huniq_not_derivable`" at
      the strengthened name. The existing theorem never mentions `relUnambiguous` or
      productivity, so a reader who runs `#print axioms` on it learns only "two lists
      here differ" — the prose attributes strictly more than the name supports.
      **R5-05.**

## 4. `README.md` — the declared departures (R5-11, R5-12, R5-17, R5-18, R5-19, R5-23, R5-24, R5-25, R5-26, R5-27, R5-28, R5-29)

The substantive one is R5-11; the rest are one-clause corrections. `PAPER.md` is the
authority for every quote.

- [ ] 4.1 **`[D4]` title + opener.** Rewrite "**[D4] Lossless capture** — a destructive
      constructor such as the paper's `ignore` is _impossible_ under strict
      isomorphism" so the anchor states at the top that both shipped mechanisms are
      **length-preserving** (`norm : Bytes n → Bytes n`; `relTakeWhile` relates a run of
      length `n`) and that the paper's actual use case — collapsing an arbitrary-length
      blank run, a `Bytes m → Bytes n` map with `m ≠ n` — is **not reproduced** by
      core. Keep the correct 40-lines-later caveat; stop making it carry the whole
      disclosure. **R5-11**, design §D4. Do **not** build the carrier.
- [ ] 4.2 **`[S1]` "the full unconditional-iso list".** Add the one clause that
      `Iso.foldl`/`Iso.foldr` are _deliberately_ excluded (their law holds only on the
      terminal-seed domain — anchor (ii) already says so), so the list is not called
      "full" while omitting the only two `Iso`-valued `def`s in the file. **R5-12**;
      ✔verified by grepping `^def` in `Codec/Iso.lean`.
- [ ] 4.3 **`[S2]` `print → encode`.** Replace "a method selected by the value's
      `Printer α` instance" with the paper's actual form: `print :: Printer α → α →
Maybe String` takes an explicit _pretty-printer implementation_ value. The
      conclusion ("largest porting cost") survives; the justification does not — what
      differs is _what the argument is_ (`[D6]`'s typeclass-to-value move), not whether
      one is passed. **R5-17.**
- [ ] 4.4 **`[S3]` "none has an in-tree caller".** `isoConsumesByte` **is** called, at
      `Codec/Combinators.lean:403` inside `countSuccConsumesByte`; ✔verified by grep.
      `Iso.ofTotal` and `decodeWholeOne` are genuinely caller-free. Rewrite to
      distinguish the three. **R5-18.**
- [ ] 4.5 **`[S3]` "complete core `Codec`-value inventory".** The `Normal` row
      (`fill`, `decodeNormal`) contains **zero** `Codec` values. Either drop the row
      (the table is otherwise exactly the 15 `Codec`-valued definitions — verified) or
      retitle to "core values a porter must reproduce" with a `kind` column. **R5-19.**
- [ ] 4.6 **`[D2]` "the paper has two values, not one".** Scope it: the paper has two
      _decoder-side_ values; `print` is a third interpreter. **R5-23.**
- [ ] 4.7 **`[D4]` "realized by repetition over a `subset p byte` step".** The step is
      `Codec.satisfy p` (`Combinators.lean:1276`); no code composes `subset` with
      `byte`. **R5-24.**
- [ ] 4.8 **Module-inventory table.** `Normal.fixed` / `Normalizer.idem` are listed as
      "gated laws" but are **structure projections** — the same category error
      README:394–402 itself applies to `Iso.law`. Annotate. **R5-25.**
- [ ] 4.9 **`[S4]` "fresh well-founded derivations".** `Iso.lean:375–383` says the
      recursion is "factored once"; `foldr` reuses `unfoldBy`. The distinct thing is
      the step _type_ and the measure witness. Reword. **R5-26.**
- [ ] 4.10 **`Nat`-cursor lowering citation.** Cited to `Codec/ByteSlice.lean`; it
      primarily lives at `Codec/Packed.lean:15–30`. Fix the citation. **R5-27.**
- [ ] 4.11 **`[D8]` `satisfy`.** The "`UInt8` totality" reason does not explain why
      `subset` _was_ converted to `DecidablePred`; and `satisfy` has no paper
      counterpart, so it sits oddly under a paper-combinator anchor. Reword and scope.
      **R5-28.**
- [ ] 4.12 **`[S1]` "unconditionally … no hypothesis".** `Iso.element`/`Iso.subset`
      take `[DecidableEq α]`/`[DecidablePred p]` — instance hypotheses. Qualify.
      **R5-29.**

## 5. Necessity claims in `Codec/` docstrings (R5-03, R5-06, R5-10, R5-14, R5-15, R5-16, R5-20, R5-21, R5-22, R5-30)

Five of these are self-contradictions inside one file. Each is cheap; each steered a
reader.

- [ ] 5.1 **`length_filterMap_le` (R5-14).** Its docstring calls `packedCands` "a
      `filterMap`"; `Packed.lean:599–610` shows a `map` and `:579` **bolds** "Built by
      `map`, not `filterMap`, and that is a measured 2.6×". The lemma has **zero
      callers** and `packedCands`'s bound comes from `length_map`. **Delete the
      lemma** (design §D8) rather than repair prose no reader consumes.
- [ ] 5.2 **`DecodeOne.lean:19` (R5-15).** "sound only when unambiguous/functional"
      contradicts `decodeOne_mem` seven lines later and the theorem itself (no
      hypothesis, `[propext, Quot.sound]`). Change "sound only when" → "equal to
      `decodeArray` only when", and say soundness is unconditional.
- [ ] 5.3 **`RelAligned`'s "Satisfied by `byte` (`relUnambiguous` at `Bytes 1`)"
      (R5-16).** No such lemma exists — the supplier is `relAligned_byte` — and the
      at-one-length justification is the length/unambiguity confusion the _next_
      docstring retracts. Rewrite to cite `relAligned_byte` and the prefix argument.
- [ ] 5.4 **`min_rotate` (R5-07).** Dead: `grep` outside `Axioms.lean` returns only its
      own definition, and `btake_btake` is plain `rfl` and never mentions it. Its
      docstring claims the `#print axioms` pins "confirm it for the laws that cite
      this" — nothing cites it. **Delete** the lemma and both `Axioms.lean` entries
      (`gatedNames` + the `#print axioms` block), then regenerate. `omega` supplies it
      in place if ever needed.
- [ ] 5.5 **`Combinators.lean:1269` (R5-20).** "Only `relTakeWhile_cast` is new" —
      `encodeTakeWhile_of_decode` is a new ~15-line proof, not an inherited term. One
      clause.
- [ ] 5.6 **`Iso.lean:846–853` (R5-21).** Still uses "chain-isolated in both
      directions", the phrase `README [D7]` says "was invented in an earlier draft" and
      disowns. Replace with the measure/terminal-seed obligation that _is_ the reason.
- [ ] 5.7 **`Codec.lean:30–33` (R5-22).** "The typeclass reading would prevent the two
      interpreters from having [those] types" is false — a typeclass parameter _is_
      `Type → Type`. The real reason (given correctly at README:697–700) is that a
      typeclass gives no finite case list to induct over.
- [ ] 5.8 **`Normal.lean:41–49` (R5-30).** "for a **decidable** idempotent `norm`" —
      `Normalizer` carries no `Decidable` field. Either add the field or state the
      sentence as describing an intended instantiation.
- [ ] 5.9 **`Rel_seqLeft` docstring (R5-09).** Its twin has a long docstring that
      explicitly warns the proof recipe does **not** transfer between the two halves;
      `Rel_seqLeft` has none. Add two lines.
- [ ] 5.10 **`Rel_manyUpTo` (R5-08).** This is a NITPICK, not an optional task — every
      box in this ledger is ticked or the change does not archive, and an "optional" box
      is the one that gets skipped silently. Do the cheap version: leave the statement
      alone (the `∃ k` form is _correct_ and shows the bound's provenance via
      `count k p`) and add **one sentence** to its docstring saying so. Only add the
      `∃`-free corollary as a real theorem if a caller wants it — do not invent a
      consumer. **R5-08.**
- [ ] 5.11 **`Axioms.lean` defs table (R5-03, R5-10).** Change "has a stated law, by the
      proxy" to "named by a gated theorem's type — the proxy's whole measurement (a
      mention, not a strength claim)", and name the two vacuous cases
      (`decodeArrayFast_eq`, `decodeWholeOneBytes_eq` — `rfl` unfolds whose docstrings
      already admit it). Count stays 111. Design §D2.

## 6. `basen` — gate parity and the stale pin (R5-33, R5-36, R5-32, R5-31)

- [ ] 6.1 **Bump the pin.** `nix flake lock --update-input codec` (targeted — never all
      inputs), then `lake update codec`. **R5-33.** ✔Verified stale: pin
      `eb1d77af838f26b89a6bb6ccc1ad81063a0d4fd3`, HEAD
      `e1d8d124ea928f35cdef98533b40b036ca20293f`, 27 commits, ancestor confirmed. The
      27 commits add law families and _withdraw a prose claim_ (`99526b4`); none changes
      a type `basen` imports.
- [ ] 6.2 **Delete the eight dead `*Run` values.** `bitRun`, `quartetRun`, `octRun`,
      `digRun`, `b32Run`, `b64Run`, `b32TailRun`, `b64TailRun` — each occurs **exactly
      once** in the tree (its own `def`); ✔verified. Keep `hexRun` (5 occurrences,
      genuinely used by base16's fold proofs). **R5-36**, design §D5. Also check
      `decodeBit`-style orphans: `decodeBit` has 2 hits (def + docstring) and
      `roundtrip` calls `decodeFull …` directly.
- [ ] 6.3 **Port the definition-coverage check** into `basen/Axioms.lean`: `publicDefs`,
      `mentionedByGated`, `isDerivedDefName`, `definitionSurfaceAllowlist` and the
      `run_cmd`, mirroring `codec/Axioms.lean`. Widen the namespace predicate to
      `BaseN` (codec's checks `Codec`/`Iso`; basen's must check `BaseN` only — `Codec.*`
      names are the dependency's and stay outside). **R5-36.**

      **The outcome is open on purpose, and here is how to handle it, so the session does
      not stall.** The auditor's "28 substantive defs" came from a `/tmp` mirror
      (`/tmp/probe-basen/ProbeDefs.lean`) with 38 machinery names filtered by hand, not
      from the ported check; expect a *different* set. Procedure: (a) run the ported
      check and let it print the silent set; (b) for each name, classify into exactly one
      of four groups and write the reason in place —
      `Iso`-law-as-field (`*BlockIso`, `*TailIso`, `Run.decode/encode/rel` projections),
      `Type`-level alias, internal witness, or **lawless-and-dead**; (c) **dead ones get
      deleted** (§6.2 already removes the eight `*Run` values — check whether each
      remaining candidate is dead by `grep -c` before allowlisting it, because
      allowlisting dead API is the failure mode §1.8 exists to prevent); (d) anything
      with a live consumer but no law gets a law or an allowlist reason. If the ported
      check names **zero** defs because §6.2 already removed them all, that is a pass,
      not a failure — record it and move on. Do not tune `isDerivedDefName` to shrink
      the list; that is the dumping ground the allowlist's reasons exist to avoid.

- [ ] 6.4 **Correct the prose counts and gate the paragraph.** `Axioms.lean:32–40` says
      `440 pins / 437 / 483`; reality is `441 / 438 / 484` (✔verified by grep:
      438 `BaseN` pins + 3 `Codec` pins = 441; `484 = 438 + 46`). Same at
      `:1655–1656`. Then extend `headerNumbers` to compute so many constants that the
      paragraph cannot rot — design §D7. **R5-34.**
- [ ] 6.5 **Fix the log line's arithmetic.** `"438 pinned + 46 allowlisted = 447 of
484"` — `447` is the _kept_ side of `partitionInto` (`484 − 37 suffix-dropped`),
      not `438 + 46`. The checks are correct; the message conflates two sets in one
      equation. **R5-35.**
- [ ] 6.6 **Even-arity lowercase witness needs its positive counterpart.** Add
      `decodes_6F : decodeFull hexElem hexConsumesByte 2 (…) = some [0x6F]` so
      `rejects_lowercase_even_arity` can cite it as the explicit "only difference is
      case" contrast instead of relying on an unstated premise. **R5-32.**
- [ ] 6.7 **Bench lane: pin the values it only implies.** Add concrete `example`
      value-checks for **base16 whole-string** `encodeHex foobar = "666F6F626172"`,
      **base2/4/8/10 whole-string** encoder outputs, and **plain decode-to-bytes** for
      the padded bases (`decodeFullB64` / `decodeFullB32` on canonical strings).
      **R5-31.** The values are known-correct (audit F0 cross-checked every RFC 4648
      vector), so this is a **regression guard, not a bug fix** — the lane currently
      checks only block-level outputs and `↔` forms, which a preservation-of-relation
      regression would survive.

## 7. `codec` gates (R5-37, plus housekeeping)

- [ ] 7.1 Regenerate `Axioms.lean` after §1–§5 (`scripts/gen-axioms.lean`), and move
      the header tables **and** the `expected*` constants together. **Do not predict the
      delta — the run prints it.** The four gate lines give
      `N public theorems partitioned, G gated and A allowlisted` and
      `header numbers verified (N = G + A; defs …)`; the generator also rewrites the
      footprint distribution between its `BEGIN/END GENERATED distribution` markers, so
      that table needs no hand edit. Then update **by hand** the two header tables and
      the six `expected*` constants in `headerNumbers` to match, and re-run until green.
      Sanity anchors from the current tree (**not** a target): 400/327/73 theorems,
      140/111/29 defs. The only planned removals are `min_rotate` (−1 gated) and
      `length_filterMap_le` (−1 gated).
- [ ] 7.2 **`CRef.c` placement (R5-37).** Nitpick, but the rule's letter matters: the
      file's own header concedes it "parses bytes and is therefore deliberately outside
      `Codec/`'s design rule". It is bench-only, not `@[extern]`, not in the gate.
      Decide and record: either move it to `bench/CRef.c`, or keep it and add one
      sentence to `AGENTS.md` saying the `Codec/` **directory** holds one bench-only
      file that is not part of the library. Do not delete — it is the C reference the
      perf claims are measured against.
- [x] 7.3 Update `openspec/lean-notes.md` with the two new lessons: (a) **a dependent
      `Fin`/`Array` bound reached by `simpa` leaks `Classical.choice`** — state the
      bound explicitly instead; (b) **a dependent rewrite under `decode d h (size) ∘
cast` cannot be `rw`/`subst`/`generalize`** — carry `hk : k = n` and
      `ha : a = cast …` as hypotheses and `subst` twice.

      **DONE in the authoring session** (`722a69f`, 2026-11-06), together with the
      `AGENTS.md` traps (`d0fb9db`) and the global skill (`lean-skills` `6cf4b05`).
      Ticked so it is not re-done; the entries are dated and headed
      "(**round-five audit**)".

- [x] 7.4 Add the class-level lesson to `openspec/lean-notes.md`: _a "necessity" claim
      about why code was written a particular way has no gate — grep it before believing
      it._ Five of this round's findings (R5-13, R5-14, R5-15, R5-16, R5-18) were that
      shape.

      **DONE in the authoring session** (same commit, entry 3).

## 8. Recorded, deliberately NOT fixed here

- [ ] 8.1 **The length-changing carrier for `[D4]`.** Would be
      `Iso (Bytes m) (Bytes n)` or a `List`-shaped normalizer, with its own
      `Productive`/`ConsumesByte`/shrink-witness obligations. A design change, not a
      prose fix; needs an owner decision because it changes what `[S3]`/`[S4]` may ship.
      Design §D4.
- [ ] 8.2 **`relRepeat_induction` has zero callers.** The principle's _existence_ is
      the least-fixpoint property, so the claim is accurate whether or not anything
      uses it. Recorded as a known state; no action.
- [ ] 8.3 **README throughput figures were not re-measured** by the audit, and
      `AGENTS.md` forbids quoting a figure without running its lane in the same
      session. Not touched. If they are ever quoted, re-run `benchBurst`/`benchRatio`
      first.
- [ ] 8.4 **`basen`'s `native_decide` ×3** remain bench-only with no law depending on
      them (✔confirmed: `Bench.lean` is a `lean_exe`, no library module imports it, and
      they are `example`s outside `publicTheorems`). Unchanged, still tracked open.

## 9. Gates (run all three repos; they are different flakes)

- [ ] 9.1 `codec`: `lake build` (zero `sorry`, four gate lines, all counts moved in
      lockstep), `lake build bench`, `openspec validate --all`,
      `nix flake check` (detached with `nohup`, never foregrounded — and **`nix fmt`
      first**, or `checks.formatting` fails on the uncommitted ledger).
- [ ] 9.2 `basen`: `lake build`, `lake build bench`, `nix build '.#bench'` (its
      `installPhase` **runs** the executable, so the vectors are value-checked).
- [ ] 9.3 `template`: `nix flake check`, `nix build .#native .#cli`.
- [ ] 9.4 Commit per task family, individual files only, printing
      `git diff --cached --name-only` before each. The pre-commit hook runs `nix fmt`
      and rejects a reformatted staged file; re-add and commit again.
- [ ] 9.5 Verify every new law's footprint by hand:
      `printf 'import Codec\n#print axioms Codec.<n>\n' > /tmp/c.lean` →
      expect `[propext, Quot.sound]` or cleaner. `Classical.choice` is a defect.

---

## Appendix A — the proofs, inlined (do not depend on `/tmp`)

These are the four proof bodies §1–§3 transcribe. They are `lake env lean`-verified in the
authoring session; the axiom footprint of each is noted. Copy them, then correct the
docstrings around them. **They are written in an `open Codec` / `namespace Codec` block
as standalone files** — landing them means moving each inside `Codec/Sound.lean`'s or
`Codec/Packed.lean`'s existing `namespace Codec`, and dropping the `#print axioms` lines
(`scripts/gen-axioms.lean` generates the gated equivalents).

### A.1 — §1.1, §1.2, §1.3 (`Codec/Sound.lean`) — `[propext]` / `[propext, Quot.sound]`

```lean
-- §1.1
theorem lengthDet_relUnambAlignedWitness : LengthDet relUnambAlignedWitness := by
  intro a m₁ m₂ t₁ t₂ h₁ h₂
  match m₁, t₁, h₁ with
  | 1, _, h₁ =>
      match m₂, t₂, h₂ with
      | 1, _, _ => rfl
      | 2, _, h₂ => exact absurd (h₁.symm.trans h₂) (by decide)
      | 0, _, h₂ => exact absurd h₂ (by simp [relUnambAlignedWitness])
      | _+3, _, h₂ => exact absurd h₂ (by simp [relUnambAlignedWitness])
  | 2, _, h₁ =>
      match m₂, t₂, h₂ with
      | 1, _, h₂ => exact absurd (h₁.symm.trans h₂) (by decide)
      | 2, _, _ => rfl
      | 0, _, h₂ => exact absurd h₂ (by simp [relUnambAlignedWitness])
      | _+3, _, h₂ => exact absurd h₂ (by simp [relUnambAlignedWitness])
  | 0, _, h₁ => exact absurd h₁ (by simp [relUnambAlignedWitness])
  | _+3, _, h₁ => exact absurd h₁ (by simp [relUnambAlignedWitness])

theorem lengthDet_not_implies_relAligned :
    ¬ (∀ {α : Type} (R : α → {m : Nat} → Bytes m → Prop), LengthDet R → RelAligned R) :=
  fun h => relUnambiguous_not_implies_relAligned
    (h relUnambAlignedWitness lengthDet_relUnambAlignedWitness)

-- §1.2
theorem prod_relUnambAlignedWitness :
    ∀ a {m : Nat} (t : Bytes m), relUnambAlignedWitness a t → m ≠ 0 := by
  intro a m t h
  match m, t, h with
  | 0, _, h => exact absurd h (by simp [relUnambAlignedWitness])
  | 1, _, _ => decide
  | 2, _, _ => decide
  | _+3, _, h => exact absurd h (by simp [relUnambAlignedWitness])

theorem lengthDet_not_implies_relAligned_productive :
    ¬ (∀ {α : Type} (R : α → {m : Nat} → Bytes m → Prop),
        LengthDet R → (∀ a {m : Nat} (t : Bytes m), R a t → m ≠ 0) → RelAligned R) := by
  intro h
  exact relUnambiguous_not_implies_relAligned
    (h relUnambAlignedWitness lengthDet_relUnambAlignedWitness prod_relUnambAlignedWitness)

-- §1.3
def alignedNotLengthDetWitness (a : Bool) : {m : Nat} → Bytes m → Prop
  | 1, _ => a = true
  | 2, _ => a = true
  | _, _ => False

theorem aligned_alignedNotLengthDetWitness : RelAligned alignedNotLengthDetWitness := by
  intro a b m₁ m₂ t₁ t₂ hle h₁ h₂ _
  match m₁, t₁, h₁ with
  | 1, _, h₁ => match m₂, t₂, h₂ with
    | 1, _, h₂ => exact h₁.trans h₂.symm
    | 2, _, h₂ => exact h₁.trans (h₂ ▸ rfl)
    | 0, _, h₂ => exact absurd h₂ (by simp [alignedNotLengthDetWitness])
    | _+3, _, h₂ => exact absurd h₂ (by simp [alignedNotLengthDetWitness])
  | 2, _, h₁ => match m₂, t₂, h₂ with
    | 1, _, _ => exact absurd hle (by omega)
    | 2, _, h₂ => exact h₁.trans h₂.symm
    | 0, _, h₂ => exact absurd h₂ (by simp [alignedNotLengthDetWitness])
    | _+3, _, h₂ => exact absurd h₂ (by simp [alignedNotLengthDetWitness])
  | 0, _, h₁ => exact absurd h₁ (by simp [alignedNotLengthDetWitness])
  | _+3, _, h₁ => exact absurd h₁ (by simp [alignedNotLengthDetWitness])

theorem not_lengthDet_alignedNotLengthDetWitness : ¬ LengthDet alignedNotLengthDetWitness := by
  intro h
  have h1 : alignedNotLengthDetWitness true (m := 1) (fun _ => (0x41 : UInt8)) := rfl
  have h2 : alignedNotLengthDetWitness true (m := 2) (fun _ => (0x41 : UInt8)) := rfl
  have := h (a := true) (fun _ : Fin 1 => (0x41 : UInt8)) (fun _ : Fin 2 => (0x41 : UInt8)) h1 h2
  omega

theorem relAligned_not_implies_lengthDet :
    ¬ (∀ {α : Type} (R : α → {m : Nat} → Bytes m → Prop), RelAligned R → LengthDet R) :=
  fun h => not_lengthDet_alignedNotLengthDetWitness (h alignedNotLengthDetWitness
    aligned_alignedNotLengthDetWitness)
```

Measured: `lengthDet_relUnambAlignedWitness` and `lengthDet_not_implies_relAligned`
`[propext]`; `aligned_alignedNotLengthDetWitness` and `relAligned_not_implies_lengthDet`
`[propext, Quot.sound]`.

### A.2 — §2.1 (`Codec/Packed.lean`) — `[propext, Quot.sound]`

```lean
theorem arrayToBytes_bytesToArray_apply {n : Nat} (s : Bytes n)
    (i : Fin (bytesToArray s).size) :
    arrayToBytes (bytesToArray s) i
      = s ⟨i.val, Nat.lt_of_lt_of_eq i.isLt (bytesToArray_size s)⟩ := by
  have hiL : i.val < (List.ofFn s).length := by
    rw [List.length_ofFn]; exact Nat.lt_of_lt_of_eq i.isLt (bytesToArray_size s)
  show (Array.mk (List.ofFn s))[i.val] = s _
  rw [← Array.getElem_toList]
  exact List.getElem_ofFn (f := s) (i := i.val) (h := hiL)

theorem arrayToBytes_bytesToArray {n : Nat} (s : Bytes n) :
    arrayToBytes (bytesToArray s)
      = cast (congrArg Bytes (bytesToArray_size s).symm) s := by
  funext i
  rw [cast_bytes_val_symm (e := (bytesToArray_size s)) (f := s) (i := i)]
  exact arrayToBytes_bytesToArray_apply s i

-- local helper; make private or fold in
private theorem decodeWholeBytes_spec_aux {α : Type} (d : Codec α) (h : ConsumesByte d)
    {n : Nat} (s : Bytes n) (k : Nat) (hk : k = n)
    (a : Bytes k) (ha : a = cast (congrArg Bytes hk.symm) s) :
    d.decodeFull h k a = d.decodeFull h n s := by
  subst hk; subst ha; rfl

theorem decodeWholeBytes_spec {α : Type} (d : Codec α) (h : ConsumesByte d) {n : Nat}
    (s : Bytes n) : decodeWholeBytes d h s = decodeFull d h n s := by
  unfold decodeWholeBytes
  rw [decodeWhole_eq]
  exact decodeWholeBytes_spec_aux d h s _ (bytesToArray_size s) _ (arrayToBytes_bytesToArray s)
```

### A.3 — §3.1 (`Codec/Sound.lean`) — `[propext, Quot.sound]`

```lean
theorem huniq_not_derivable_full :
    ∃ (R : Bool → {m : Nat} → Bytes m → Prop),
      relUnambiguous R ∧ (∀ a {m : Nat} (t : Bytes m), R a t → m ≠ 0) ∧
      ¬ (∀ (xs ys : List Bool) (n : Nat) (s : Bytes n),
          relRepeat R xs n s → relRepeat R ys n s → xs = ys) := by
  refine ⟨uniqCounterexampleRel, uniqCounterexample_unambiguous,
    uniqCounterexample_productive, ?_⟩
  intro h
  have := h [true] [false, false] 2 (fun _ => 0) uniqCounterexample_single uniqCounterexample_pair
  exact absurd this (by simp)
```

### A.4 — §2.3 (`Codec/Sound.lean`) — `[propext, Quot.sound]`

```lean
theorem decodeRepeat_mem_iff_general {α : Type} (p : Codec α) (h : ConsumesByte p)
    {n : Nat} (s : Bytes n) (xs : List α) :
    (xs, Suffix.empty n) ∈ decodeRepeat p h n s ↔ relRepeat (Rel p) xs n s := by
  rw [decodeRepeat_spec p h]
  constructor
  · rintro ⟨s₀, hs, hrel⟩
    have hpre : (Suffix.empty n).prepend s₀ = s := hs.symm
    rw [prepend_empty_self] at hpre
    subst hpre
    exact hrel
  · intro hrel
    exact ⟨s, (prepend_empty_self n s).symm, hrel⟩
```

---

## Archive ordering

`codec-audit-round-three` archived 2026-11-06, so this change's MODIFIED blocks are
authored against the **post-sync** text. Before archiving:

1. Re-run the live-vs-delta scenario diff for all four modified requirements. Expected:
   `codec/review-remediation` "ordering or implication claim" 2 → 4;
   `codec/law-coverage` "declared free theorem" 1 → 3;
   `codec/axiom-gate` "partition extends to public definitions" 3 → 4;
   `basen` "conformance laws are gated" 3 → 6. **Nothing may be dropped.** These are
   additive-only deltas; if the diff shows a drop, the delta was authored from the
   wrong base.
2. `openspec validate --all` after the archive; confirm it stays 10/10.
3. No new capability is created by this change — all four are MODIFIED-existing.

## Known OPEN work that is NOT a task number

These are open in code and must not be re-discovered as bugs, nor ticked as done:

- `basen`'s general arity rejection for the five fixed-width bases (needs a
  `decodeFull`-length lemma); `rejects_single_char` is an honest single-point witness.
- `huniq` for unequal-length `alt` is not derivable in general
  (`Codec.huniq_not_derivable`) — a hypothesis by design.
- `[D4]`'s missing length-changing carrier (§8.1).
- `basen`'s three `native_decide` bench uses (§8.4).
