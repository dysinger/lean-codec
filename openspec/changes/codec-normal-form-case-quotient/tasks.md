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
- [ ] 4.5 `openspec validate --all` green; commit each file individually
      (`Codec/Normal.lean`, `Codec.lean`, `README.md`, `CHANGELOG.md`, the `openspec/`
      artifacts), with `nix fmt` clean before each commit.

## 5. Downstream follow-up — **out of scope here, recorded so it is not lost**

- [ ] 5.1 `../lean-basen`: RFC 4648 §8 Base16 case-insensitivity as `norm = ASCII
fold` over the existing uppercase `hexBlockIso`, plus the encoder-emits-uppercase
      obligation (D3's hypothesis, already a proved canonicality law there) and the
      both-cases theorem. This **closes `basen-rfc-conformance-theorems` task 7.3** and
      replaces that task's false `Unambiguous` rationale. It also requires fixing that
      change's spec clause which currently _requires_ lowercase rejection, and removing
      `lowercase` from task 3.3's rejection family.

## Explicitly not doing

- **Whitespace collapsing** (`skipSpace`/`optSpace`/`sepSpace`, paper §6.3). It is
  length-changing, so it is not a `Bytes n → Bytes n` normalizer. It needs a
  different carrier, and the single-substrate rule (`Bytes n := Fin n → UInt8`) is
  not reopened here. Recorded in design D6 as a deliberate boundary. The earlier
  draft's `lean-text` follow-up task said otherwise and was **wrong**; it is not
  carried forward.
