# Tasks

> **Surface (read first):** this change is **additive**. No existing declaration
> changes shape: `Iso`, `Codec`, `decode`, `encode`, `Rel`, `Unambiguous`,
> `Functional` and every proved law stay exactly as they are. The change is one new
> module (`Codec/Normal.lean`), its re-export from `Codec.lean`, a README `[D4]`
> sharpening, and the axiom gate additions.
>
> **Scope:** **length-preserving** normalizers only (`Bytes n → Bytes n`). Case
> folding is in scope. Whitespace-run collapsing is **not** — it is length-changing
> and needs a different carrier (design D6). Do not attempt `skipSpace` here.
>
> The shape is **already verified to compile and gate clean** in a `/tmp` probe
> against the built library (under the earlier working name `Formatted`): the
> quotient type, `fill`, the fixed-point witness, `drop ∘ fill = id` **by `rfl`**,
> an `Iso UInt8 (Formatted UInt8 drop)` with its `law` field proved, a
> `norm`-outside-the-`Iso` decode wrapper, and its functionality lemma — `#print
axioms` = **no axioms** for `drop ∘ fill = id`, `[propext]` for the `Iso` and the
> wrapper, zero `sorry`, zero `Classical.choice`. Task 0.1 re-runs the probe under
> the new names as the acceptance check.
>
> **Review provenance:** an adversarial review found four defects in the first
> draft of this plan — the missing wrapper law (3.1), the idempotence-as-argument
> mistake (1.2), the mislocated `Unambiguous` (3.2), and the false whitespace claim
> (removed from scope). The tasks below are the corrected versions; do not
> reintroduce the originals.

## 0. Verify the shape under the final names

- [x] 0.1 Re-run the probe against the built library with the names `Normal` /
      `normalize` / `fill` and confirm: zero warnings; `drop ∘ fill = id` reports
      **no axioms**; `fill_surj` reports **no axioms**; the `Iso α (Normal S nz)` and
      the `decodeNormal` wrapper report `[propext]` only. If anything regresses, stop
      and revise `design.md` D1/D2 before touching `Codec/`.

  Target shape:

  ```lean
  structure Normal (S : Type) (norm : S → S) where
    raw   : S
    fixed : norm raw = raw

  structure Normalizer (S : Type) where
    norm : S → S
    idem : ∀ x, norm (norm x) = norm x

  def fill (nz : Normalizer S) (s : S) : Normal S nz.norm :=
    ⟨nz.norm s, nz.idem s⟩

  @[simp] theorem fill_raw (nz : Normalizer S) (s : S) : (fill nz s).raw = nz.norm s := rfl
  @[ext] theorem Normal.ext {f g : Normal S norm} (h : f.raw = g.raw) : f = g

  /-- `norm ∘ fill = id` on the quotient — the fixed-point witness, not a law. -/
  theorem fill_fixed (nz : Normalizer S) (s : S) : nz.norm (fill nz s).raw = (fill nz s).raw
  ```

## 1. The `Normal` quotient and its `Normalizer` in core

- [x] 1.1 Add `Codec/Normal.lean`: `Normal`, `Normal.ext`, `Normalizer`
      (`norm` + `idem`), `fill`, `fill_raw`, `fill_fixed`. Docstring each declaration
      in place: cite README `[D4]`, the paper's §3.1 "modulo equivalence classes"
      remark, and **why the quotient is a subtype of fixed points rather than Lean's
      `Quotient`** (design D1: reducibility, `simp`/`rfl`, no `Quot.sound` in the gate).
- [x] 1.2 Carry the laws in `Normalizer` — **not** as a `fill` argument (design D2).
      If any signature tempts you to take `∀ x, norm (norm x) = norm x` as a parameter,
      that is the defect the review caught; stop and re-read D2.
- [x] 1.3 State and record that this is **two** laws, honestly: `Iso.law` on the
      arrow (untouched) and `Normalizer.idem` on the normalizer (new, in a structure).
      There is no third; nothing is weakened. The change's docs SHALL NOT say "no second
      law".

## 2. The facts the layer owes

- [x] 2.1 `fill_surj (nz) (f : Normal S nz.norm) : fill nz f.raw = f` — design D7.
      This is what makes "the fixed-point subtype faithfully reifies the quotient" a
      lemma rather than an assertion. Expected **no axioms**.
- [x] 2.2 `fill_inj : fill nz s = fill nz t ↔ nz.norm s = nz.norm t` — the lemma
      that makes "two spellings, one quotient element" usable downstream.
- [x] 2.3 Length-preservation is **not** in `Normalizer` (it is only true when
      `S = Bytes n`). Record it as a per-instantiation obligation in the docstring, with
      the one-line reason: `Bytes n := Fin n → UInt8`, so a `Bytes n → Bytes n` map
      cannot change the count (design D6).

## 3. The decode-only wrapper and its law

- [x] 3.1 Add the wrapper as a **named, documented, non-`Iso`** function (design
      D3): `decodeNormal (i : Iso α (Normal S nz.norm)) (nz : Normalizer S) (s : S) :
Option α := i.unapply (fill nz s)`. Docstring SHALL say: _not_ an `Iso`; has no
      inverse (`norm` is many-to-one); accepts input the `Iso` rejects; is the lossy
      half of the layer.
- [x] 3.2 Prove **the wrapper's real law** (design D3) — the theorem the first draft
      omitted and the reason the layer is useful:

  > `hfix : nz.norm s = s → i.unapply (fill nz s) = i.unapply ⟨s, hfix⟩`

  and, at the whole-codec level, state the usable form with its **precondition
  spelled out**: if the wrapped codec's encoder emits a normal form
  (`norm (encode x) = encode x`), then `decodeNormal (encode x) = some x`. The
  precondition is an obligation, **not** a free fact — do not state the roundtrip
  without it.

- [x] 3.3 **Do not** claim an `Unambiguous`-preservation theorem (design D4).
      `Unambiguous` is defined over `Codec α` (`Sound.lean:621`) and this layer is at the
      `Iso`, so there is nothing to prove — the wrapper introduces no alternatives
      because `norm` is a function. Record that as a _clarification of domain_ in the
      module docstring, not as a theorem. (The first draft listed it as a theorem; that
      was a tautology misdescribed.)

## 4. Gate and docs

- [x] 4.1 `lake build` green: zero `sorry`, zero warnings. `#print axioms`:
      `fill_fixed`/`fill_surj`/`fill_inj` = **no axioms** or `[propext]`; the wrapper
      and its law `[propext]` (or `[propext, Quot.sound]`) — **never**
      `Classical.choice`.
- [x] 4.2 `lake build bench` green (this change adds no format; add an `example`
      only if the bench already has a suitable site).
- [x] 4.3 Amend README `[D4]` (design D8). Keep the conclusion (no `ignore`; the law
      holds unconditionally) and replace the false generalisation. Use the **corrected
      wording**: `ignore :: α → Iso α ()` is an `Iso` _value_, so it cannot be a lossy
      `Iso`; what models formatting loss is the normalising decoder with the normalizer
      **outside** an `Iso`. Do **not** write "`ignore` is the `drop` half" (review point
      9). Also record the layman reason: formatting is not semantic, so an AST must not
      carry it.
- [x] 4.4 `CHANGELOG.md` entry (one bullet: the normal-form layer, length-preserving
      case variation only).
- [x] 4.5 `openspec validate --all` green; commit each file individually
      (`Codec/Normal.lean`, `Codec.lean`, `README.md`, `CHANGELOG.md`, the `openspec/`
      artifacts), with `nix fmt` clean before each commit.

## 5. Downstream follow-up — **out of scope here, recorded so it is not lost**

> **START HERE (next session).** Summary also lives in `AGENTS.md` §Current state.
> this change, and the `lean-codec` half is complete and pushed. Two findings below
> were verified in `/tmp` probes — they are facts, not plans; do not rediscover them.
>
> **Finding 1 — the fold direction must be UP.** The canonical hex alphabet is
> uppercase, so the encoder's output must be a **fixed point** of `norm`; that is
> exactly `decodeNormal_encode`'s `hfix` obligation. Therefore `norm` folds
> `a`–`f` (97..102) **up** to `A`–`F` (65..70), _not_ down. Folding down makes the
> encoder's output a non-fixed point and the normalising decoder fails on its own
> encoder's output. Verified: `foldByte_idem` holds, and `A`, `F`, `9` are fixed
> points while `a`→`A`, `f`→`F`.
>
> **Finding 2 — the blocker is semantic, not `List.ofFn` plumbing.** `hexBlockApply`
> accepts **uppercase only**, so an `Iso` into normal forms with
> `unapply f := hexBlockApply f.raw` is wrong: a class whose representative is
> lowercase will not apply. The correct `unapply` **folds first**:
> `unapply f := hexBlockApply (foldList f.raw)`. The `Iso` law then needs the
> commutation lemma `hexBlockApply (foldList cs) = hexBlockApply cs` for a 2-element
> digit list.
>
> **The lemma that defeated three attempts, and its correct shape.**
> `hexToNibble (foldByte b).toNat = hexToNibble b.toNat` is **false as a single
> equation** (in the non-lowercase branch it would demand
> `hexToNibble b.toNat = b.toNat`, false for a non-digit). It must be stated as a
> **three-way case split** — digit `48..57` (fixpoint, `hexToNibble` equal), upper
> `65..70` (fixpoint, equal), lower `97..102` (folds to `b.toNat - 32`, nibble equal
> by `hexToNibble_*`). Do the case split _first_; do not try to unify it.
>
> **Lemma inventory already proved in probes** (re-prove in-tree, they are short):
> `foldByte_idem`; `foldByte_fixed (b) (¬(97 ≤ b.toNat ∧ b.toNat ≤ 102))`;
> `nibbleToHex_not_lower (n) (n ≤ 15)`; `hexDigit_fixed (n) (n ≤ 15)` —
> `foldByte (toByte (nibbleToHex n)) = toByte (nibbleToHex n)` (needs
> `toByte_nibbleToHex`, which is `private` in `Base16.lean` — inline the
> `UInt8.toNat_ofNat'` + `Nat.mod_eq_of_lt` bridge as the probe did);
> `hexCanon_fixed (b) : (hexCanon b).map foldByte = hexCanon b` (needs
> `b.toNat < 256` from `UInt8.toNat_lt b` for `omega`).
>
> **Do not** use `git checkout --` to reset a stuck file (`AGENTS.md` forbids it; it
> was tried once this session and was only harmless by luck). Stub the one failing
> theorem and iterate in `/tmp` against the built library.
>
> **Order:** (1) the three-way `hexToNibble`/`foldByte` lemma; (2)
> `hexBlockApply_fold`; (3) `hexElemF` + law; (4) `decodeHexFold` + the §8 both-cases
> theorem; (5) discharge `hfix` (uppercase output is a fold fixed point — Finding 1);
> (6) the ledger edits in §5.1 below.

- [x] 5.1 `../lean-basen`: RFC 4648 §8 Base16 case-insensitivity as `norm = ASCII
fold` **upward** over the existing uppercase `hexBlockIso`, plus the
      encoder-emits-uppercase obligation (D3's hypothesis) and the both-cases
      theorem. **DONE** — this closed `basen-rfc-conformance-theorems` task 7.3.

      **The six planned steps were carried out, and two had to be corrected
      because their stated mathematics was wrong.** Both corrections are verified,
      not conjectures:

      1. **The three-way lemma could not be one equation.** Confirmed: it is split
         into `hexToNibble_foldByte_true` / `_false` (plus `_value`, the `if`-form
         the `Iso` law consumes) and `hexNibbleValid_foldByte` for validity.
      2. **The commutation lemma is one-directional, not an identity.** This note
         said the `Iso` law needs `hexBlockApply (foldList cs) = hexBlockApply cs`.
         **That equality is false.** `['6','f']` is rejected by the strict
         `hexBlockApply` yet folds to the accepted `['6','F']` — `#eval`-verified
         as `none` vs `some 0x6F` — which is exactly the §8 widening the layer
         exists to produce, so no identity can hold. The law needs the
         **preservation** form
         `hexBlockApply cs = some b → hexBlockApply (foldList cs) = some b`
         (landed as `hexBlockApply_foldList`), together with
         `hexBlockApply_foldList_ne` recording the refutation of the plan's
         equality. `hexBlockIsoF_law` then closes with that plus `fill_surj`.

      **Landed in `../lean-basen` `BaseN/Base16.lean`** (commits `bddc8f8`,
      `31c4250`, `ec62371`): `foldByte`/`foldList`/`foldByteBytes` + idempotence,
      `hexChar`, `hexNibbleValid_foldByte`, the three-way split,
      `hexBlockApply_foldList` + `_ne`, `hexBlockIsoF` + `hexBlockIsoF_law`,
      `decodeHexBlockFold`, `decodeHexFold`, `foldList_hexBlockUnapply` (the `hfix`
      discharge), `decodeHexFold_lowercase_eq`, `decodeHexFold_of_fixed`. Six new
      `#guard_msgs` in `Axioms.lean`, seven new bench `example`s. `lake build` and
      `lake build bench` green, zero `sorry`, every law `[propext,
      Quot.sound]`-only.

      **The `Classical.choice` trap, in its new disguise.** The first pass leaked
      `Classical.choice` through *every* new law — not from a dependent `cases`, but
      from `decide_eq_true (by omega)` on a **disjunction** goal: `omega` closes a
      disjunction by case analysis, which drags in classical logic. Build the
      disjunct explicitly (`decide_eq_true (Or.inl ⟨_, _⟩)`). A second, independent
      leak was a `match` on a `Bool` **in the goal**; splitting the lemma into
      `_true`/`_false` removed it.

      Also done: spec delta, `proposal.md`, `design.md` D6 and task 3.3 amended in
      `basen-rfc-conformance-theorems`; `rejects_lowercase`'s false `Unambiguous`
      rationale withdrawn in-tree; the module docstring corrected.

## Explicitly not doing

- **Whitespace collapsing** (`skipSpace`/`optSpace`/`sepSpace`, paper §6.3). It is
  length-changing, so it is not a `Bytes n → Bytes n` normalizer. It needs a
  different carrier, and the single-substrate rule (`Bytes n := Fin n → UInt8`) is
  not reopened here. Recorded in design D6 as a deliberate boundary. The earlier
  draft's `lean-text` follow-up task said otherwise and was **wrong**; it is not
  carried forward.
