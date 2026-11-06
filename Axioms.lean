/- Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later -/

import Codec
import Lean.Elab.Command

/-!
# Axiom gate (`lake build`-enforced)

Every public law of this package must be provable from Lean's kernel plus **only**
`propext` and `Quot.sound` — never `Classical.choice`, never `sorryAx`, never
`native_decide`. That discipline is a standing invariant of the whole `codec`
ecosystem (see `AGENTS.md`), and `-DwarningAsError` in `lakefile.lean` already makes
the `sorry` half a build error. `../lean-basen` has carried the axiom half since its
own audit; this file closes the asymmetry by giving the *dependency* the same gate.

Each `#guard_msgs` below pins the *exact* diagnostic text of `#print axioms`, so an
axiom that appears **or disappears** changes the message and trips the guard. A
`Classical.choice` regression therefore cannot land silently.

## How the theorem set is enumerated (not hand-listed)

The generated region at the bottom of this file is **derived from the compiled
environment**, so it covers whatever `Codec` exports rather than what a maintainer
remembered to list. The generator walks `Environment.constants`, keeps every
constant in the `Codec` or `Iso` namespace whose `ConstantInfo` is `thmInfo` (a
theorem, not a `def`), and drops two kinds of non-authorial name:

* unsafe constants and private / internal-detail names — not public surface;
* **compiler-generated auxiliaries**, recognised by their last component:
  `eq_def`, `inj`, `injEq`, `sizeOf_spec`, `congr_simp`, `dec`, `eq_irrel`,
  `induct`.

## The coverage check is a *partition*, not a filter

The suffix rule above is a **default classifier, not an authority**. It was one in
fact until `codec-audit-round-two`: `Codec.Nat.eq_irrel` — an authored theorem with
a docstring explaining the proof-irrelevance role it plays — ends in `eq_irrel` and
was silently dropped from the gate, and the three `MeasureDecreases*.dec` /
`Unfold.dec` structure-field projections were dropped for the same last-name reason.
A name-based mechanism can always un-gate a law a human wrote, so a green build said
nothing about them.

The hole is closed structurally: `generatedAuxAllowlist` (below) lists **by name,
with a reason**, every declaration the suffix rule drops, and two build-time checks
run on every `lake build`:

* `partition` — every public theorem is in `gatedNames` **xor**
  `generatedAuxAllowlist`; a name in neither fails the build printing the name (an
  un-gated law), and a name in both also fails (a self-contradiction).
* `gateCoverage` — `gatedNames` agrees with the environment, so a rename or a stale
  entry is a build failure too.

Forgetting to maintain the allowlist is therefore a **build failure** rather than a
silent hole, which is the strongest property a name-based gate can have. It is *not*
"sound by construction": the allowlist is still a list a maintainer maintains. What
changed is that its lapses are loud.

Regenerate with:

```
nix develop --command lake env lean scripts/gen-axioms.lean
```

## The definition-coverage check, and what it is NOT

The two checks above partition the **theorems**. A public `def` is in neither side —
the gate's universe is `thmInfo`, so a definition is not "un-gated", it is *outside
the partition*. That is why `btake`, `maybe`, `manyUpTo`, `seqRight`, `seqLeft` and
`between` shipped with zero theorems while every gate was green.

The third check closes that: every public `def` must be mentioned by the **type** of
some gated theorem, or be in `definitionSurfaceAllowlist` with its reason in place.

**Read that as a MENTION PROXY, never as a strength guarantee.** "Does this `def`
have a law?" is not decidable; "does any gated theorem's type mention this constant"
is. The property the check actually has is the narrow one:

> no public definition can be covered by **silence**.

A `def` some theorem mentions has at least been reasoned about; a `def` no theorem
mentions has no stated law. It can be satisfied **vacuously** — a theorem whose
statement mentions the name trivially passes — and it says nothing about whether the
resulting law is strong, useful, or true of the intended semantics. It is the same
escalating-proxy discipline the footprint gate already uses (that one proxies "is
this a law" by "is this a `thmInfo`"), and it exists because silence was the actual
failure mode. **It is not soundness.**

## Current state

**400** public theorems are covered, by a partition with no third route:

| side | count | what it is |
| --- | --- | --- |
| gated (`gatedNames`) | **327** | footprint pinned by `#print axioms` |
| allowlisted (`generatedAuxAllowlist`) | **73** | not a law; reason recorded in place |
| un-gated and unlisted | **0** | a build failure, by construction |

Gated footprint distribution — **generated** from the same `collectAxioms` results the
`#guard_msgs` blocks pin (`scripts/gen-axioms.lean`; task §1.9), not transcribed:

-- BEGIN GENERATED distribution

| footprint | count |
| --- | --- |
| `[propext, Quot.sound]` | 210 |
| `[propext]` | 79 |
| `[Quot.sound]` | 4 |
| axiom-free | 34 |
| anything else | 0 |
| **total** | **327** |

`[propext, Classical.choice, Quot.sound]` rows: **0** — every gated law is
inside the discipline.
-- END GENERATED distribution

Definitions, by the third check:

| side | count | what it is |
| --- | --- | --- |
| public `def`s (after dropping compiler machinery) | **140** | the universe |
| mentioned by a gated theorem's type | **111** | has a stated law, by the proxy |
| `definitionSurfaceAllowlist` | **29** | no law; reason recorded in place |
| silent | **0** | a build failure, by construction |

**The theorem/definition counts are asserted, and the footprint table is
generated** — two mechanisms, because they have different failure modes.

* The *counts* are asserted by `headerNumbers` at the end of this file: a stale table
  is a build failure. That is not decoration — this table said `364 / 292` and
  `197 / 61 / 4 / 30` after the gated set had already reached `382 / 310` and
  `201 / 74 / 4 / 31`, because `partition`/`gateCoverage` compare set *membership* and
  never read the prose.
* The *footprint distribution* is now **generated** by `scripts/gen-axioms.lean`
  (`codec-audit-round-three` §1.9), counting the `collectAxioms` name lists rather than
  parsing renderered prose. It keys on names, so the audit's own failure mode — a
  parser truncating at the `?` in `Codec.attach_getElem?_corr` — cannot recur (design
  D1). On the regeneration that introduced it the generated table **equalled the
  hand-written one** (`209 / 78 / 4 / 34 = 325`), which is D1's "the table is correct
  today" re-confirmed by the compiler rather than by re-reading it.

`Codec.Nat.eq_irrel` is one of the axiom-free 34, and it is in the gated set only
since `codec-audit-round-two`: the suffix classifier had been dropping it as an
`eq_irrel`-shaped auxiliary, which is what motivated the partition.

`Classical.choice` appears in **no** law. The one law that used to carry it —
`Codec.findByte_spec`, which reached classical logic through `Array.findIdx?`'s
`DecidableEq UInt8` — was rewritten onto a constructive `Nat`-recursion
(`Codec.findFrom`) and now reports `[propext]`. The gate's first run recorded that
leak as an explicit exclusion (`codec-audit-remediation` task 1.3); task 2 removed
the leak and the exclusion with it. **The excluded set is empty.**
-/

namespace CodecAxioms

open Lean Elab Command

/-- Default classifier for non-authorial theorem names: the ones the compiler emits
for every structure or `def`.

**This is a heuristic, not an authority.** Its claim used to be "none is a law a
human wrote", and that was false: `Codec.Nat.eq_irrel` is an authored, docstringed
theorem that this rule dropped, and the three `MeasureDecreases*.dec` / `Unfold.dec`
projections are structure fields a human wrote. Every decision this classifier makes
is audited by `CodecAxioms.partition` below, which requires each dropped name to
appear in `generatedAuxAllowlist` with a reason — so a wrong decision here is a
build failure, not a silent gap. Never read this rule as "therefore not a law".

`induct` is the `@[elab_as_elim]` principle Lean derives for a recursive `def` from
its `termination_by` / structural recursion (here `findFrom.induct`); it is a proof
of the recursion, not a law. -/
def isGeneratedAux (n : Name) : Bool := Id.run do
  -- Authored laws that carry a generated-looking suffix. `Codec.Nat.eq_irrel` is a
  -- law (see its docstring) that the bare suffix rule used to drop; the partition
  -- check below means this list cannot hide anything, only name it.
  let authored : Array Name := #[`Codec.Nat.eq_irrel]
  if authored.contains n then return false
  let s := n.components.getLast!.toString
  return s == "eq_def" || s == "inj" || s == "injEq" || s == "sizeOf_spec" ||
    s == "congr_simp" || s == "dec" || s == "induct"

/-- Every public theorem candidate in the `Codec`/`Iso` namespaces, **before** any
name-based declination. This is the universe `gatedNames` and
`generatedAuxAllowlist` must partition.

The unsafe / private / internal-detail filter is *not* a declination: those are not
public surface at all (`@[implemented_by]` helpers, `_private` proofs), so they are
outside the universe rather than dropped from it. The allowlist only ever describes
names a reader could cite. -/
def publicTheorems (env : Environment) : Array Name := Id.run do
  let mut thms : Array Name := #[]
  for (name, ci) in env.constants.toList do
    if (`Codec).isPrefixOf name || (`Iso).isPrefixOf name then
      match ci with
      | .thmInfo _ =>
        if ci.isUnsafe || isPrivateName name || name.isInternalDetail then
          pure ()
        else
          thms := thms.push name
      | _ => pure ()
  return thms.qsort (fun a b => Name.toString a < Name.toString b)

/-- The membership decisions of `isGeneratedAux`, per name — the candidate set split
into the two sets the partition requires. Used by both build-time checks; kept here so
the split and the assertion that it *is* a partition live together. -/
def partitionInto (env : Environment) : Array Name × Array Name := Id.run do
  let mut dropped : Array Name := #[]
  let mut kept : Array Name := #[]
  for n in publicTheorems env do
    if isGeneratedAux n then dropped := dropped.push n else kept := kept.push n
  return (kept, dropped)

/-- The kept side of the classifier: the universe minus the names `isGeneratedAux`
drops — the set the `gatedNames` mirror of the environment is built from. Named
because the generator script mirrors *it*, and because "what the classifier keeps" and
"what `generatedAuxAllowlist` declares" are the two halves the `partition` check
compares. -/
def gatedTheorems (env : Environment) : Array Name := partitionInto env |>.1

/-! ## The definition-coverage check

The axiom gate's universe is `thmInfo` constants only, so a public `def` sits in
**neither** side of the partition above — it is not "un-gated", it is *outside the
partition*. That is why `btake`, `maybe`, `manyUpTo`, `seqRight`, `seqLeft` and
`between` shipped with zero theorems while every gate was green.

**The check is a MENTION proxy, and must be read as one.** "Does this `def` have a
law?" is not decidable — provability is not a property you can grepping for. What *is*
decidable is whether any gated theorem's **type** mentions the constant. The property
this check has is therefore exactly:

> no public definition can be covered by **silence**.

A `def` some theorem mentions has at least been reasoned about; a `def` no theorem
mentions has no stated law. It can still be satisfied *vacuously* — a theorem whose
statement mentions the name trivially would pass — and it is **not** a soundness
claim, not a strength requirement, and not "every `def` has a law worth having". It
closes the failure mode that is actually present (silence) and is stated as a proxy,
never as a guarantee. This is the same escalating-proxy discipline the footprint gate
already uses (it proxies "is this a law" by "is this a `thmInfo`").

The same last-name classifier as `isGeneratedAux` decides which `def`s are *not*
surface: an inductive's derived companions (`recOn`, `casesOn`, `noConfusion`,
`ctorIdx`, `ctorElim`, `brecOn`, `below`, `rec`) are machinery Lean emits, not
definitions anyone wrote. Everything else is either mentioned by a gated theorem or
listed in `definitionSurfaceAllowlist` **with its reason in place**. -/

/-- Default classifier for `def` names that are **not** authorial surface: the
companions Lean emits for every inductive and structure. Same status as
`isGeneratedAux` — a heuristic, audited by the check below, never an authority. -/
def isDerivedDefName (n : Name) : Bool := Id.run do
  let last := n.components.getLast!.toString
  return last == "casesOn" || last == "recOn" || last == "rec" || last == "elim" ||
    last == "noConfusion" || last == "noConfusionType" || last == "ctorIdx" ||
    last == "ctorElim" || last == "ctorElimType" || last == "below" ||
    last == "brecOn" || last == "brecOn.go" || last == "mk" || last == "prod" ||
    last == "sizeOf" || last == "sizeOf_spec" ||
    -- Notation aliases: a token bound to an existing declaration, so the *declaration*
    -- is what has (or lacks) a law, not the token. `Iso.«term_≫_»` is `Infixr "≫" =>
    -- Iso.trans`, whose law is `Iso.trans`'s own `law` field.
    last == "«term_≫_»"

/-- Every public `def` in the `Codec`/`Iso` namespaces, **after** dropping compiler
machinery and non-public names. This is the universe `definitionSurfaceAllowlist`
and "mentioned by a gated theorem" must partition. -/
def publicDefs (env : Environment) : Array Name := Id.run do
  let mut ds : Array Name := #[]
  for (name, ci) in env.constants.toList do
    if (`Codec).isPrefixOf name || (`Iso).isPrefixOf name then
      match ci with
      | .defnInfo _ =>
        if ci.isUnsafe || isPrivateName name || name.isInternalDetail ||
            isDerivedDefName name then
          pure ()
        else
          ds := ds.push name
      | _ => pure ()
  return ds.qsort (fun a b => Name.toString a < Name.toString b)

/-- The names mentioned by at least one gated theorem's **type**. The other half of
the definition-coverage partition; the mention proxy's whole measurement. -/
def mentionedByGated (env : Environment) : Std.HashSet Name := Id.run do
  let mut s : Std.HashSet Name := {}
  for t in gatedTheorems env do
    match env.find? t with
    | some (.thmInfo ti) =>
      for c in ti.type.getUsedConstants do
        s := s.insert c
    | _ => pure ()
  return s

/-- Public `def`s with **no** law naming them, listed by name with the reason the
absence is deliberate.

Each entry is one of three shapes, and the reason is in place at the entry:

* an `Iso` combinator whose correctness is the `law` **structure field**, proved at its
own definition site (so the kernel checks it at construction) and therefore stated by
no separate theorem — the mention proxy cannot see a field proof;
* a `Type`-level alias (`candsAt`/`candsRoot`/`retypeCands`) whose whole content is a
list-cast that is definitionally the identity;
* an internal witness or instance (`uniqSeqBt`, `instDecidableEqBytes`, …) that exists
to make another proof go through, not to be a codec a caller uses.

Keep the reason next to the entry: a bare name here would be the dumping ground this
list exists to avoid. -/
def definitionSurfaceAllowlist : Array Name := #[
  -- **`Iso` combinators: correctness is the `law` structure field**, proved at the
  -- definition site (`law := by …`), so the kernel checks it at construction and no
  -- separate theorem names it. The mention proxy cannot see a field proof.
  `Iso.associate,
  `Iso.commute,
  `Iso.element,
  `Iso.id,
  `Iso.inverse,
  `Iso.ofTotal,
  `Iso.optionSome,
  `Iso.subset,
  `Iso.trans,
  `Iso.unit,
  -- `Iso.foldl`/`Iso.foldr`/`Iso.nil` are `Iso` structures too: their `law` field is
  -- proved at the definition site (the fold/unfold bijection on terminal seeds; the
  -- `Unit`↔`[]` bijection).
  `Iso.foldl,
  `Iso.foldr,
  `Iso.nil,

  -- **`Iso` fold plumbing** (`foldApply`/`foldUnapply`/`foldrApply`/`foldrUnapply`):
  -- the `Option`-returning halves the `Unfold` structure is built from. What they are
  -- *for* is proved about `Unfold`/`foldl`/`foldr` (`Iso.unfoldBy_eq`,
  -- `Iso.foldRec_append`, `Iso.unfoldBy_sound`), not about these part-functions.
  `Iso.foldApply,
  `Iso.foldUnapply,
  `Iso.foldrApply,
  `Iso.foldrUnapply,
  `Iso.MeasureDecreases.toUnfold,
  `Iso.MeasureDecreasesR.toUnfold,

  -- **`Type`-level aliases**: the whole content is a `List.cast` that is
  -- definitionally the identity. There is no law to state (see `retypeCands`'s
  -- docstring: "`List.cast` is definitionally the identity here; it exists only to
  -- name the type").
  `Codec.candsAt,
  `Codec.candsRoot,
  `Codec.retypeCands,

  -- **Internal witnesses** built to make one specific proof go through, not codecs.
  -- `uniqSeq*` are the `Unambiguous`-counterexample description values (their
  -- witnesses `uniqSeqBt_*` are gated laws); the recons halves are the `foldl`/`foldr`
  -- step functions those proofs supply.
  `Codec.uniqSeqBt,
  `Codec.uniqSeqIso,
  `Codec.uniqSeqUnitIso,
  `Iso.reconsLeft,
  `Iso.reconsRight,

  -- **Computed instances**: `DecidableEq`/`Inhabited` for `Bytes n`, used by `decide`
  -- and by `Option`/`Array` plumbing. Instances, not surface a caller writes against.
  `Codec.instDecidableEqBytes,
  `Codec.instInhabited,
]

/-- Declarations knowingly excluded from the `[propext, Quot.sound]`-only discipline,
by name. Each must also appear in the "Explicit exclusion" section at the end of
this file, with its measured footprint and the reason. An exclusion is a decision on
the record — never a silent omission, and never described in prose as clean.

**Currently empty.** The single law that needed an exclusion — `Codec.findByte_spec`
— was made clean rather than excluded (`codec-audit-remediation` design D2, option
B), so there is no entry. The mechanism is kept because the exclusion list is what
makes an exclusion *visible* in the diff; deleting it would make the next one a
silent addition to `isGeneratedAux` instead. -/
def exclusions : Array Name := #[]

/-- The other half of the gate's partition: every public theorem the suffix rule drops
without footprint-checking, listed **by name with the reason it is not a law**.

This is the audit's finding made structural. The suffix rule is a heuristic that can
drop an authored law — it did drop `Codec.Nat.eq_irrel` — so it cannot be the last
word. This list is the last word: `CodecAxioms.partition` (below) requires every name
here to *actually* be dropped by `isGeneratedAux` (so the list cannot smuggle a law
out of the gate), requires every dropped public theorem to appear here (so nothing
falls between the two sets), and requires the list to be disjoint from `gatedNames`.

Why each entry is not a law. Four groups, each with its own reason in place:

* **`inj`, `injEq`, `sizeOf_spec`, `congr_simp`, `eq_def`** — compiler auxiliaries:
  the constructor injectivity equation, its `Bool` form, the derived `SizeOf`
  equation, the `@[congr]` lemma for recursor arguments, and the compiled-body
  equation of a `def`. Each restates its own definition; none says anything about
  which bytes a codec accepts.
* **`Iso.MeasureDecreases.dec`, `Iso.MeasureDecreasesR.dec`, `Iso.Unfold.dec`** — a
  **`Prop`-valued structure field**: part of the *type a caller supplies*, not a
  theorem proved about it. `MeasureDecreases.dec` is the well-foundedness hypothesis
  of `foldl`, `MeasureDecreasesR.dec` the mirror for `foldr`, and `Unfold.dec` the
  same obligation on the factored recursion. The `@[projection]` theorems Lean derives
  from them report whatever the caller gave — they assert nothing. Note that the
  *satisfiability* of these obligations **is** a law, and is gated:
  `counterMeasureDecreases` / `counterMeasureDecreasesR`.
* **`Codec.findFrom.induct`** — **the recursion principle of a `def`**, generated by
  Lean from `findFrom`'s structural recursion. A proof that the recursion terminates,
  not a statement about the codec.

`Codec.Nat.eq_irrel` is deliberately **not** here. It is an authored theorem — its
docstring explains the proof-irrelevance role it plays in closing the laws without
`Classical.choice` — so it belongs in the gated set even though its name matches the
`eq_irrel` pattern. The classifier no longer drops it either (`isGeneratedAux` names
it as an authored exception), which is why it is absent from the group above. That is
the shape of every future correction: a law the heuristic misclassifies moves into
the gated set, and the allowlist keeps only what is genuinely not a law. -/
def generatedAuxAllowlist : Array Name := #[
  -- **`Prop`-valued structure fields**: part of the type a caller supplies, not a
  -- theorem proved about it. Their satisfiability *is* a law, and is gated
  -- (`counterMeasureDecreases`, `counterMeasureDecreasesR`).
  `Iso.MeasureDecreases.dec,
  `Iso.MeasureDecreasesR.dec,
  `Iso.Unfold.dec,

  -- **The recursion principle of a `def`** (`findFrom`'s structural recursion).
  `Codec.findFrom.induct,

-- **`inj` — the injectivity equation of a constructor.** Lean emits it for every
-- inductive constructor and structure `mk`: two applications are equal iff their
-- fields are, which the constructor's own typing already gives. It states nothing
-- about which bytes a codec accepts.
  `Codec.Normal.mk.inj,
  `Codec.Suffix.mk.inj,
  `Codec.alt.inj,
  `Codec.iso.inj,
  `Codec.pure.inj,
  `Codec.satisfy.inj,
  `Codec.seq.inj,
  `Iso.Unfold.mk.inj,
  `Iso.mk.inj,

-- **`injEq` — the `Bool`-valued form of the same equation**, the shape `simp`
-- consumes. An auxiliary of `inj`, not an independent statement.
  `Codec.Normal.mk.injEq,
  `Codec.Suffix.mk.injEq,
  `Codec.alt.injEq,
  `Codec.iso.injEq,
  `Codec.pure.injEq,
  `Codec.satisfy.injEq,
  `Codec.seq.injEq,
  `Iso.Unfold.mk.injEq,
  `Iso.mk.injEq,

-- **`sizeOf_spec` — the defining equation of the derived `SizeOf` instance.**
-- Part of Lean's termination machinery; about the size of a description value, not
-- about a codec's behaviour.
  `Codec.Normal.mk.sizeOf_spec,
  `Codec.Suffix.mk.sizeOf_spec,
  `Codec.alt.sizeOf_spec,
  `Codec.byte.sizeOf_spec,
  `Codec.empty.sizeOf_spec,
  `Codec.iso.sizeOf_spec,
  `Codec.pure.sizeOf_spec,
  `Codec.satisfy.sizeOf_spec,
  `Codec.seq.sizeOf_spec,
  `Iso.Unfold.mk.sizeOf_spec,
  `Iso.mk.sizeOf_spec,

-- **`congr_simp` — the `@[congr]` lemma `congr_simp` derives** so that `simp` can
-- rewrite under a recursion's argument (well-founded or `partial` definitions).
-- `simp` plumbing, nothing more.
  `Codec.Normal.mk.congr_simp,
  `Codec.Suffix.mk.congr_simp,
  `Codec.decodeFull.congr_simp,
  `Codec.decodeFullArrayFast.congr_simp,
  `Codec.decodeFullArraySearch.congr_simp,
  `Codec.decodeFullFastSearch.congr_simp,
  `Codec.decodeFullStep.congr_simp,
  `Codec.decodeFullStepPacked.congr_simp,
  `Codec.decodeRepeat.congr_simp,
  `Codec.fill.congr_simp,
  `Codec.shiftedOfFn.congr_simp,
  `Codec.splice.congr_simp,
  `Iso.MeasureDecreasesR.toUnfold.congr_simp,
  `Iso.foldl.congr_simp,
  `Iso.foldr.congr_simp,
  `Iso.mk.congr_simp,

-- **`eq_def` — the compiled-body equation of a `def`** (`f x = body`). It unfolds a
-- definition the source already states; nobody cites it as an authority, and it is
-- regenerated automatically whenever the body changes.
  `Codec.Rel.eq_def,
  `Codec.choice.eq_def,
  `Codec.count.eq_def,
  `Codec.decode.eq_def,
  `Codec.decodeArray.eq_def,
  `Codec.decodeFast.eq_def,
  `Codec.decodeFullArrayFast.eq_def,
  `Codec.decodeFullArraySearch.eq_def,
  `Codec.decodeFullFast.eq_def,
  `Codec.decodeFullFastSearch.eq_def,
  `Codec.decodeFullStep.eq_def,
  `Codec.decodeFullStepPacked.eq_def,
  `Codec.decodeOne.eq_def,
  `Codec.encode.eq_def,
  `Codec.encodeArray.eq_def,
  `Codec.encodeArrayFold.eq_def,
  `Codec.encodeRepeat.eq_def,
  `Codec.encodeWholeRepeatAcc.eq_def,
  `Codec.fastEncodeRepeatAcc.eq_def,
  `Codec.findFrom.eq_def,
  `Codec.pushBytesFrom.eq_def,
  `Codec.relRepeat.eq_def,
  `Codec.relSepBy.eq_def,
  `Iso.foldRec.eq_def,
]

-- BEGIN GENERATED gatedNames
/-- The names this file actually pins a `#guard_msgs` block for. GENERATED — written
in lockstep with the body, so it is a record of what is gated rather than a second
list to maintain by hand. -/
def gatedNames : List Lean.Name := [
  `Codec.Bytes.ext
  ,`Codec.Bytes.ext_iff
  ,`Codec.CandAligned_at
  ,`Codec.CandAligned_fst
  ,`Codec.CandAligned_tail
  ,`Codec.Fin.cast_val
  ,`Codec.Nat.eq_irrel
  ,`Codec.Normal.ext
  ,`Codec.Normal.ext_iff
  ,`Codec.Normal.fixed
  ,`Codec.Normalizer.idem
  ,`Codec.Rel_alt
  ,`Codec.Rel_between
  ,`Codec.Rel_byte
  ,`Codec.Rel_cast
  ,`Codec.Rel_cast_symm
  ,`Codec.Rel_choice
  ,`Codec.Rel_count_eq_relRepeat
  ,`Codec.Rel_count_succ
  ,`Codec.Rel_count_zero
  ,`Codec.Rel_empty
  ,`Codec.Rel_iso
  ,`Codec.Rel_manyUpTo
  ,`Codec.Rel_maybe_none
  ,`Codec.Rel_maybe_some
  ,`Codec.Rel_optional_none
  ,`Codec.Rel_optional_some
  ,`Codec.Rel_pure
  ,`Codec.Rel_satisfy
  ,`Codec.Rel_seq
  ,`Codec.Rel_seqLeft
  ,`Codec.Rel_seqRight
  ,`Codec.Suffix.consumed_id
  ,`Codec.Suffix.consumed_trans
  ,`Codec.Suffix.drop_zero
  ,`Codec.Suffix.eq_empty_of_remaining_zero
  ,`Codec.Suffix.ext
  ,`Codec.Suffix.hle
  ,`Codec.Suffix_cast_remaining
  ,`Codec.altConsumesByte
  ,`Codec.append_toArray_ofFn_concat
  ,`Codec.array_bridge
  ,`Codec.array_readback
  ,`Codec.attach_eq_cons
  ,`Codec.attach_getElem?_corr
  ,`Codec.attach_pair_eq
  ,`Codec.bdrop_add
  ,`Codec.bdrop_bdrop
  ,`Codec.bdrop_consumedAbs_eq
  ,`Codec.bdrop_drop_eq_bytes
  ,`Codec.bdrop_prepend
  ,`Codec.bdrop_prepend_splice
  ,`Codec.bdrop_prepend_splice_eq_splice
  ,`Codec.bdrop_prepend_splice_len
  ,`Codec.bdrop_prepend_splice_snd_len
  ,`Codec.bdrop_seg
  ,`Codec.bdrop_splice
  ,`Codec.bdrop_zero
  ,`Codec.bidir
  ,`Codec.blitBytes_spec
  ,`Codec.bpush_data
  ,`Codec.brecOn.eq
  ,`Codec.btake_agree
  ,`Codec.btake_apply
  ,`Codec.btake_btake
  ,`Codec.btake_zero
  ,`Codec.byteConsumesByte
  ,`Codec.byteSlice_spec
  ,`Codec.bytesToArray_size
  ,`Codec.cands_eq_nil_of_zero
  ,`Codec.cast_bytes_eq_single
  ,`Codec.cast_bytes_irrel
  ,`Codec.cast_bytes_val
  ,`Codec.cast_bytes_val'
  ,`Codec.cast_bytes_val_symm
  ,`Codec.cast_concat_eq_splice
  ,`Codec.cast_concat_splice_sub
  ,`Codec.cast_fin
  ,`Codec.cast_fin_symm
  ,`Codec.cast_fin_symm_val
  ,`Codec.cast_fin_val
  ,`Codec.cast_fun_apply
  ,`Codec.commitRemainder_spec
  ,`Codec.concat_assoc
  ,`Codec.concat_eq_splice
  ,`Codec.consume_lt
  ,`Codec.consumedAbs_cast_trans
  ,`Codec.consumedAbs_drop_one
  ,`Codec.consumedAbs_id
  ,`Codec.consumedAbs_remaining
  ,`Codec.countLength
  ,`Codec.countSuccConsumesByte
  ,`Codec.countToRelRepeat
  ,`Codec.count_succ
  ,`Codec.cursor_bridge
  ,`Codec.decodeArrayFast_eq
  ,`Codec.decodeArray_bounded
  ,`Codec.decodeArray_bounded_upper
  ,`Codec.decodeArray_consumes
  ,`Codec.decodeArray_eq
  ,`Codec.decodeArray_functional_byte
  ,`Codec.decodeArray_functional_count
  ,`Codec.decodeArray_getElem?_spec
  ,`Codec.decodeArray_unambiguous_byte
  ,`Codec.decodeArray_unambiguous_value
  ,`Codec.decodeArray_unique
  ,`Codec.decodeArray_unique_byte
  ,`Codec.decodeChainl1_spec
  ,`Codec.decodeChainr1_spec
  ,`Codec.decodeFast_eq
  ,`Codec.decodeFullArrayFast_succ
  ,`Codec.decodeFullArrayFast_zero
  ,`Codec.decodeFullArrayRoot_eq
  ,`Codec.decodeFullArraySearch_cons
  ,`Codec.decodeFullArraySearch_eq_stepPacked
  ,`Codec.decodeFullArraySearch_nil
  ,`Codec.decodeFullArray_spec
  ,`Codec.decodeFullFastRoot_eq
  ,`Codec.decodeFullFastSearch_eq
  ,`Codec.decodeFullFast_succ
  ,`Codec.decodeFullFast_zero
  ,`Codec.decodeFullStep_cons
  ,`Codec.decodeFullStep_ne_none
  ,`Codec.decodeFullStep_nil
  ,`Codec.decodeFullStep_none_of_forall_none
  ,`Codec.decodeFullStep_some
  ,`Codec.decodeFull_at_zero
  ,`Codec.decodeFull_cast
  ,`Codec.decodeFull_ne_none
  ,`Codec.decodeFull_reroot_cursor
  ,`Codec.decodeFull_some
  ,`Codec.decodeFull_spec
  ,`Codec.decodeFull_spec_byte
  ,`Codec.decodeFull_succ
  ,`Codec.decodeFull_zero
  ,`Codec.decodeNormal_encode
  ,`Codec.decodeNormal_of_fixed
  ,`Codec.decodeOne_mem
  ,`Codec.decodeRepeat_eq
  ,`Codec.decodeRepeat_mem_iff
  ,`Codec.decodeRepeat_spec
  ,`Codec.decodeSepBy_spec
  ,`Codec.decodeTakeWhile_spec
  ,`Codec.decodeWholeBytes_eq
  ,`Codec.decodeWholeBytes_size
  ,`Codec.decodeWholeOneBytes_eq
  ,`Codec.decodeWholeOne_eq
  ,`Codec.decodeWhole_eq
  ,`Codec.decode_cast
  ,`Codec.decode_congr_bdrop
  ,`Codec.decode_encode
  ,`Codec.decode_genuine_suffix
  ,`Codec.decode_genuine_suffix_pointwise
  ,`Codec.decode_seq_mem
  ,`Codec.decode_spec
  ,`Codec.drop_prepend
  ,`Codec.drop_trans_eq
  ,`Codec.drop_zero_eq_id
  ,`Codec.emptyBytes_unique
  ,`Codec.emptyConsumesByte
  ,`Codec.encodeArrayFold_toList
  ,`Codec.encodeArray_eq
  ,`Codec.encodeByteArrayBytes_eq
  ,`Codec.encodeChainl1_injective_of_unambiguous
  ,`Codec.encodeChainl1_ne_none
  ,`Codec.encodeChainl1_of_decode
  ,`Codec.encodeChainl1_rel
  ,`Codec.encodeChainr1_injective_of_unambiguous
  ,`Codec.encodeChainr1_ne_none
  ,`Codec.encodeChainr1_of_decode
  ,`Codec.encodeChainr1_rel
  ,`Codec.encodeRepeat_ne_none
  ,`Codec.encodeRepeat_rel
  ,`Codec.encodeSepBy_ne_none
  ,`Codec.encodeSepBy_of_decode
  ,`Codec.encodeSepBy_rel
  ,`Codec.encodeTakeWhile_ne_none
  ,`Codec.encodeTakeWhile_of_decode
  ,`Codec.encodeTakeWhile_rel
  ,`Codec.encodeWholeBytes_toList
  ,`Codec.encodeWholeRepeatAcc_eq_fold
  ,`Codec.encodeWholeRepeatAcc_toList
  ,`Codec.encodeWholeRepeat_eq
  ,`Codec.encodeWhole_eq
  ,`Codec.encode_injective_of_unambiguous
  ,`Codec.encode_ne_none
  ,`Codec.encode_of_decode
  ,`Codec.encode_rel
  ,`Codec.fastEncodeRepeatAcc_eq
  ,`Codec.fastEncodeRepeatAcc_full_size
  ,`Codec.fastEncodeRepeatAcc_full_toList
  ,`Codec.fastEncodeRepeat_eq
  ,`Codec.fill_fixed
  ,`Codec.fill_inj
  ,`Codec.fill_raw
  ,`Codec.fill_surj
  ,`Codec.filterMap_eq_map_of_forall
  ,`Codec.findByte_spec
  ,`Codec.findFrom_complete
  ,`Codec.findFrom_finds
  ,`Codec.findFrom_least
  ,`Codec.findFrom_min
  ,`Codec.findFrom_sound
  ,`Codec.foldl_push_append
  ,`Codec.foldl_push_data
  ,`Codec.functional_byte
  ,`Codec.huniq_byte
  ,`Codec.huniq_not_derivable
  ,`Codec.isoConsumesByte
  ,`Codec.lengthConst_byte
  ,`Codec.lengthDetWitness_unamb
  ,`Codec.lengthDet_byte
  ,`Codec.lengthDet_not_implied_by_unamb
  ,`Codec.lengthDet_of_lengthConst
  ,`Codec.length_filterMap_le
  ,`Codec.length_packedCands_le
  ,`Codec.lengths_eq_of_const
  ,`Codec.list_ofFn_getElem_clean
  ,`Codec.map_toList_eq_ofFn_none_iff
  ,`Codec.mem_decodeArray_iff
  ,`Codec.mem_map_range_iff
  ,`Codec.mem_packedCands
  ,`Codec.min_rotate
  ,`Codec.nil_append_size
  ,`Codec.nil_append_toList
  ,`Codec.not_productive_pure
  ,`Codec.ofFn_concat
  ,`Codec.ofFn_shifted
  ,`Codec.packedCand_iff
  ,`Codec.packedCand_of_mem
  ,`Codec.packedCands_aligned
  ,`Codec.packedCands_consumes
  ,`Codec.packedCands_eq_attach
  ,`Codec.packedCands_length_eq
  ,`Codec.packedCands_mem
  ,`Codec.prepend_apply
  ,`Codec.prepend_assoc
  ,`Codec.prepend_drop_of_prepend_splice
  ,`Codec.prepend_drop_single
  ,`Codec.prepend_empty
  ,`Codec.prepend_empty_apply
  ,`Codec.prepend_empty_eq
  ,`Codec.prepend_empty_self
  ,`Codec.prepend_eq_of_eq_splice
  ,`Codec.prepend_id
  ,`Codec.prepend_prefix_agree
  ,`Codec.prepend_prefix_eq
  ,`Codec.prepend_prefix_read
  ,`Codec.prepend_single_bdrop
  ,`Codec.productive_iff_consumesByte
  ,`Codec.pushBytesFrom_eq
  ,`Codec.pushBytes_eq
  ,`Codec.relAligned_byte
  ,`Codec.relChainl1_cast
  ,`Codec.relChainr1_cast
  ,`Codec.relRepeatToCount
  ,`Codec.relRepeat_cast
  ,`Codec.relRepeat_cons
  ,`Codec.relRepeat_cons_eq
  ,`Codec.relRepeat_induction
  ,`Codec.relRepeat_length_of_const
  ,`Codec.relRepeat_nil
  ,`Codec.relRepeat_prefix_inj
  ,`Codec.relRepeat_suffix_inj
  ,`Codec.relRepeat_unbounded_of_empty
  ,`Codec.relRepeat_unique_same_length
  ,`Codec.relSepBy_cast
  ,`Codec.relTakeWhile_cast
  ,`Codec.relUnambAlignedWitness_unamb
  ,`Codec.relUnambiguous_not_implies_relAligned
  ,`Codec.relUnambiguous_of_relAligned
  ,`Codec.rel_byte_cast
  ,`Codec.remaining_at_cursor
  ,`Codec.remaining_at_reroot
  ,`Codec.reroot_bytes_eq
  ,`Codec.reverse_cons_append
  ,`Codec.roundtrip
  ,`Codec.satisfyConsumesByte
  ,`Codec.search_nil_left
  ,`Codec.search_nil_right
  ,`Codec.seqConsumesByte
  ,`Codec.seqCountConsumesByte
  ,`Codec.spec_at_advance
  ,`Codec.splice_add
  ,`Codec.splice_apply
  ,`Codec.splice_cast_commute
  ,`Codec.splice_prefix_agree
  ,`Codec.splice_prefix_read
  ,`Codec.splice_splice_assoc
  ,`Codec.splice_splice_len
  ,`Codec.stepPacked_eq_step
  ,`Codec.step_bytes_pointwise
  ,`Codec.sub_sub_add
  ,`Codec.sub_sub_eq
  ,`Codec.sub_sub_sub
  ,`Codec.suffix_consumed_lt
  ,`Codec.unambiguous_byte
  ,`Codec.uniqCounterexample_pair
  ,`Codec.uniqCounterexample_productive
  ,`Codec.uniqCounterexample_single
  ,`Codec.uniqCounterexample_unambiguous
  ,`Codec.uniqSeqBo_false
  ,`Codec.uniqSeqBo_true
  ,`Codec.uniqSeqBo_unambiguous
  ,`Codec.uniqSeqD2_one
  ,`Codec.uniqSeqD2_unambiguous
  ,`Codec.uniqSeqD2_zero
  ,`Codec.uniqSeqWhole_false
  ,`Codec.uniqSeqWhole_true
  ,`Codec.uniqSeq_not_congruent
  ,`Codec.uniqSeq_not_relAligned
  ,`Codec.uniqSeq_unambiguous_not_congruent
  ,`Iso.apply_eq_some_of_unapply
  ,`Iso.bind_eq_some
  ,`Iso.counterMeasureDecreases
  ,`Iso.counterMeasureDecreasesR
  ,`Iso.dropLast_append_last
  ,`Iso.foldRec_append
  ,`Iso.ite_some_eq_some
  ,`Iso.law
  ,`Iso.map_fst_reverse_eq_some
  ,`Iso.map_swap_eq_none
  ,`Iso.map_swap_eq_some
  ,`Iso.unapply_eq_some_of_apply
  ,`Iso.unfoldBy_eq
  ,`Iso.unfoldBy_of_fold
  ,`Iso.unfoldBy_sound]
-- END GENERATED gatedNames

/-! **Coverage check**, run on every `lake build`. Fails when the set of public
theorems the environment exports differs from the set pinned in this file: a missing
name means a theorem landed un-gated, and a name with no theorem means a stale entry
(and, likely, a rename). Both are build failures, so the gate cannot rot into a
snapshot of a past tree. -/
run_cmd do
  let env ← getEnv
  let covered := Std.HashSet.ofList gatedNames
  let excluded := Std.HashSet.ofList CodecAxioms.exclusions.toList
  let actual := CodecAxioms.partitionInto env |>.1
  let mut unGated : Array Name := #[]
  let mut coveredSet : Std.HashSet Name := {}
  for n in actual do
    coveredSet := coveredSet.insert n
    if !covered.contains n && !excluded.contains n then unGated := unGated.push n
  let stale : Array Name := covered.toArray.filter fun n => !coveredSet.contains n
  if !unGated.isEmpty || !stale.isEmpty then
    let mut msg : MessageData := ""
    if !unGated.isEmpty then
      msg := msg ++ m!"theorems not pinned by this gate (regenerate `Axioms.lean`):\n" ++
        m!"{String.join (unGated.toList.map fun n => s!"  {Name.toString n}\n")}"
    if !stale.isEmpty then
      msg := msg ++ m!"pinned names with no matching theorem:\n" ++
        m!"{String.join (stale.toList.map fun n => s!"  {Name.toString n}\n")}"
    throwError msg
  logInfo m!"axiom gate: {actual.size} public theorems covered ({excluded.size} explicit exclusion(s))"

/-! **Partition check**, run on every `lake build`. The coverage check above only
compares `gatedNames` against the *kept* side of the classifier, so a theorem the
classifier drops is invisible to it — that is exactly how `Codec.Nat.eq_irrel` sat
un-gated. This second check closes that path: the gated set and
`generatedAuxAllowlist` must **partition** the public theorems, with no third route
out of the gate.

Four failures, each naming what is wrong:

* a public theorem in **neither** set — a law nothing footprint-checks;
* a name in **both** — the gate's own record contradicts itself;
* an allowlist entry the classifier does **not** drop — a typo or a stale name, or an
  attempt to un-gate a law by listing it, and both must fail;
* a name in both `exclusions` and the allowlist — an exclusion is a *measured
  footprint with a reason*, an allowlist entry is *not a law*, so they cannot
  describe the same declaration. -/
run_cmd do
  let env ← getEnv
  let gated := Std.HashSet.ofList gatedNames
  let allow := Std.HashSet.ofList CodecAxioms.generatedAuxAllowlist.toList
  let pub := CodecAxioms.publicTheorems env
  let noPath := pub.filter fun n => !gated.contains n && !allow.contains n
  let both := pub.filter fun n => gated.contains n && allow.contains n
  let notDropped := CodecAxioms.generatedAuxAllowlist.filter fun n =>
    !(CodecAxioms.isGeneratedAux n) || !pub.contains n
  let exclusionOverlap := CodecAxioms.exclusions.filter allow.contains
  if !noPath.isEmpty || !both.isEmpty || !notDropped.isEmpty ||
      !exclusionOverlap.isEmpty then
    let mut msg : MessageData := ""
    if !noPath.isEmpty then
      msg := msg ++ m!"public theorems in NEITHER the gated set nor the allowlist (un-gated: regenerate, or allowlist by name with a reason):\n" ++
        m!"{String.join (noPath.toList.map fun n => s!"  {Name.toString n}\n")}"
    if !both.isEmpty then
      msg := msg ++ m!"names in BOTH the gated set and the allowlist (the partition requires disjointness):\n" ++
        m!"{String.join (both.toList.map fun n => s!"  {Name.toString n}\n")}"
    if !notDropped.isEmpty then
      msg := msg ++ m!"allowlist entries the classifier does not drop (stale name, or a law cannot be allowlisted out of the gate):\n" ++
        m!"{String.join (notDropped.toList.map fun n => s!"  {Name.toString n}\n")}"
    if !exclusionOverlap.isEmpty then
      msg := msg ++ m!"names in both the exclusion list and the allowlist (an exclusion is a measured footprint; an allowlist entry is not a law):\n" ++
        m!"{String.join (exclusionOverlap.toList.map fun n => s!"  {Name.toString n}\n")}"
    throwError msg
  logInfo m!"axiom gate: {pub.size} public theorems partitioned, {gatedNames.length} gated and {CodecAxioms.generatedAuxAllowlist.size} allowlisted"

/-! **Definition-coverage check**, run on every `lake build`. The two checks above
partition the *theorems*; a public `def` is in neither side, because the gate's
universe is `thmInfo`. This check closes that hole: every public `def` must be
mentioned by the **type** of some gated theorem, or be in
`definitionSurfaceAllowlist` with its reason in place.

**This is a mention proxy, not a strength guarantee** (see the section above
`isDerivedDefName`). Its property is the narrow one it can actually have: *no public
definition can be covered by silence.* A `def` some theorem mentions has been
reasoned about; a `def` no theorem mentions has no stated law. It can be satisfied
vacuously by a theorem that mentions the name trivially, and it says nothing about
whether the resulting law is strong — only that the name is not absent from the proof
surface.

Three failures, each naming what is wrong:

* a public `def` in **neither** set — a definition with no law and no recorded reason;
* a name in **both** — the check's own record contradicts itself;
* an allowlist entry that is public, not machinery, **and** already mentioned — a
  stale entry, or an attempt to exempt a `def` that did get a law. Keep the list
  shrinking. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let defs := CodecAxioms.publicDefs env
  let allow := Std.HashSet.ofList CodecAxioms.definitionSurfaceAllowlist.toList
  let mentioned := CodecAxioms.mentionedByGated env
  let silent := defs.filter fun n => !mentioned.contains n && !allow.contains n
  let both := defs.filter fun n => mentioned.contains n && allow.contains n
  let stale := CodecAxioms.definitionSurfaceAllowlist.filter fun n =>
    !defs.contains n
  if !silent.isEmpty || !both.isEmpty || !stale.isEmpty then
    let mut msg : MessageData := ""
    if !silent.isEmpty then
      msg := msg ++ m!"public definitions with no law naming them (prove one, or allowlist with a reason):\n" ++
        m!"{String.join (silent.toList.map fun n => s!"  {Name.toString n}\n")}"
    if !both.isEmpty then
      msg := msg ++ m!"definitions that HAVE a gated law but are also allowlisted (drop the entry):\n" ++
        m!"{String.join (both.toList.map fun n => s!"  {Name.toString n}\n")}"
    if !stale.isEmpty then
      msg := msg ++ m!"allowlist entries that are not public definitions (stale name, or machinery):\n" ++
        m!"{String.join (stale.toList.map fun n => s!"  {Name.toString n}\n")}"
    throwError msg
  logInfo m!"axiom gate: {defs.size} public definitions covered, {defs.size - CodecAxioms.definitionSurfaceAllowlist.size} mentioned and {CodecAxioms.definitionSurfaceAllowlist.size} allowlisted (mention proxy)"

/-! **Header check**, run on every `lake build`. The "Current state" tables at the top
of this file are prose, and `partition`/`gateCoverage` compare set *membership* — so a
regeneration leaves them stale silently. It happened: the tables read
`364 / 292` and `197 / 61 / 4 / 30` while the tree was already at
`382 / 310` and `201 / 74 / 4 / 31`. This check makes the numbers **asserted**:
a mismatch fails the build naming both sides.

Keep these constants in lockstep with the tables above. `codec-audit-round-three`
§1.9 tracks replacing the constants with compiler-emitted output; until then this is
what keeps the transcription honest. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let pub := CodecAxioms.publicTheorems env
  let gated := gatedNames.length
  let allow := CodecAxioms.generatedAuxAllowlist.size
  -- Lockstep with "Current state" above.
  let expectedPub := 400
  let expectedGated := 327
  let expectedAllow := 73
  let expectedDefs := 140
  let expectedMentioned := 111
  let expectedDefAllow := 29
  let mut bad : Array String := #[]
  if pub.size != expectedPub then
    bad := bad.push s!"public theorems: table says {expectedPub}, environment has {pub.size}"
  if gated != expectedGated then
    bad := bad.push s!"gated: table says {expectedGated}, gatedNames has {gated}"
  if allow != expectedAllow then
    bad := bad.push s!"allowlisted: table says {expectedAllow}, generatedAuxAllowlist has {allow}"
  if gated + allow != pub.size then
    bad := bad.push s!"table does not add up: {gated} + {allow} != {pub.size}"
  let defs := CodecAxioms.publicDefs env
  let defAllow := CodecAxioms.definitionSurfaceAllowlist.size
  if defs.size != expectedDefs then
    bad := bad.push s!"public defs: table says {expectedDefs}, environment has {defs.size}"
  if defAllow != expectedDefAllow then
    bad := bad.push s!"definitions allowlisted: table says {expectedDefAllow}, list has {defAllow}"
  if defs.size - defAllow != expectedMentioned then
    bad := bad.push s!"definitions mentioned: table says {expectedMentioned}, environment implies {defs.size - defAllow}"
  if !bad.isEmpty then
    throwError m!"the \"Current state\" table is stale (update it and expected* here):\n{String.join (bad.toList.map fun s => s!"  {s}\n")}"
  logInfo m!"axiom gate: header numbers verified ({expectedPub} = {expectedGated} + {expectedAllow}; defs {expectedDefs} = {expectedMentioned} + {expectedDefAllow})"

end CodecAxioms

/-! ## Generated body

Everything between the `BEGIN GENERATED` and `END GENERATED` markers is rewritten by
`scripts/gen-axioms.lean`. Do not hand-edit: a hand edit is either overwritten on the
next regeneration or caught by `gateCoverage`, and neither outcome is useful. Add or
fix a law in `Codec/`, then regenerate. -/


/-! ## Explicit exclusion

**There are no exclusions.** Every gated law is inside the `[propext, Quot.sound]`
-only discipline; `CodecAxioms.exclusions` is empty and `gateCoverage` reports zero
exclusions on every build.

The history is worth keeping because it is the shape an exclusion must take. The
gate's first run found exactly one law outside the discipline:

`Codec.findByte_spec` — `[propext, Classical.choice, Quot.sound]`. `findByte`'s body
then scanned with `Array.findIdx?`, whose `DecidableEq UInt8` decision is
propositional rather than definitional and so reached classical logic. It was
recorded here **by name with its measured footprint and this reason**, and marked
*excluded*, never clean — the `codec/axiom-gate` rule. Task 2 of
`codec-audit-remediation` then removed the cause rather than living with it: the
scan is now the constructive `Nat`-recursion `Codec.findFrom`, and the law reports
`[propext]`. The exclusion entry was deleted in the same commit that made the
measurement clean, so the two can never disagree.

It was **not** a Layer-2 C-trust exclusion (the C is invisible to `#print axioms`
either way) — it was an avoidable decision-procedure leak in the Lean body, which is
why it was fixed instead of documented.
-/

-- BEGIN GENERATED body

/-- info: 'Codec.Bytes.ext' depends on axioms: [Quot.sound] -/
#guard_msgs in
#print axioms Codec.Bytes.ext
/-- info: 'Codec.Bytes.ext_iff' depends on axioms: [Quot.sound] -/
#guard_msgs in
#print axioms Codec.Bytes.ext_iff
/-- info: 'Codec.CandAligned_at' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.CandAligned_at
/-- info: 'Codec.CandAligned_fst' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.CandAligned_fst
/-- info: 'Codec.CandAligned_tail' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.CandAligned_tail
/-- info: 'Codec.Fin.cast_val' does not depend on any axioms -/
#guard_msgs in
#print axioms Codec.Fin.cast_val
/-- info: 'Codec.Nat.eq_irrel' does not depend on any axioms -/
#guard_msgs in
#print axioms Codec.Nat.eq_irrel
/-- info: 'Codec.Normal.ext' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.Normal.ext
/-- info: 'Codec.Normal.ext_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.Normal.ext_iff
/-- info: 'Codec.Normal.fixed' does not depend on any axioms -/
#guard_msgs in
#print axioms Codec.Normal.fixed
/-- info: 'Codec.Normalizer.idem' does not depend on any axioms -/
#guard_msgs in
#print axioms Codec.Normalizer.idem
/-- info: 'Codec.Rel_alt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.Rel_alt
/-- info: 'Codec.Rel_between' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.Rel_between
/-- info: 'Codec.Rel_byte' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.Rel_byte
/-- info: 'Codec.Rel_cast' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.Rel_cast
/-- info: 'Codec.Rel_cast_symm' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.Rel_cast_symm
/-- info: 'Codec.Rel_choice' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.Rel_choice
/-- info: 'Codec.Rel_count_eq_relRepeat' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.Rel_count_eq_relRepeat
/-- info: 'Codec.Rel_count_succ' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.Rel_count_succ
/-- info: 'Codec.Rel_count_zero' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.Rel_count_zero
/-- info: 'Codec.Rel_empty' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.Rel_empty
/-- info: 'Codec.Rel_iso' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.Rel_iso
/-- info: 'Codec.Rel_manyUpTo' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.Rel_manyUpTo
/-- info: 'Codec.Rel_maybe_none' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.Rel_maybe_none
/-- info: 'Codec.Rel_maybe_some' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.Rel_maybe_some
/-- info: 'Codec.Rel_optional_none' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.Rel_optional_none
/-- info: 'Codec.Rel_optional_some' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.Rel_optional_some
/-- info: 'Codec.Rel_pure' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.Rel_pure
/-- info: 'Codec.Rel_satisfy' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.Rel_satisfy
/-- info: 'Codec.Rel_seq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.Rel_seq
/-- info: 'Codec.Rel_seqLeft' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.Rel_seqLeft
/-- info: 'Codec.Rel_seqRight' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.Rel_seqRight
/-- info: 'Codec.Suffix.consumed_id' does not depend on any axioms -/
#guard_msgs in
#print axioms Codec.Suffix.consumed_id
/-- info: 'Codec.Suffix.consumed_trans' does not depend on any axioms -/
#guard_msgs in
#print axioms Codec.Suffix.consumed_trans
/-- info: 'Codec.Suffix.drop_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.Suffix.drop_zero
/-- info: 'Codec.Suffix.eq_empty_of_remaining_zero' depends on axioms: [Quot.sound] -/
#guard_msgs in
#print axioms Codec.Suffix.eq_empty_of_remaining_zero
/-- info: 'Codec.Suffix.ext' does not depend on any axioms -/
#guard_msgs in
#print axioms Codec.Suffix.ext
/-- info: 'Codec.Suffix.hle' does not depend on any axioms -/
#guard_msgs in
#print axioms Codec.Suffix.hle
/-- info: 'Codec.Suffix_cast_remaining' does not depend on any axioms -/
#guard_msgs in
#print axioms Codec.Suffix_cast_remaining
/-- info: 'Codec.altConsumesByte' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.altConsumesByte
/-- info: 'Codec.append_toArray_ofFn_concat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.append_toArray_ofFn_concat
/-- info: 'Codec.array_bridge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.array_bridge
/-- info: 'Codec.array_readback' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.array_readback
/-- info: 'Codec.attach_eq_cons' does not depend on any axioms -/
#guard_msgs in
#print axioms Codec.attach_eq_cons
/-- info: 'Codec.attach_getElem?_corr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.attach_getElem?_corr
/-- info: 'Codec.attach_pair_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.attach_pair_eq
/-- info: 'Codec.bdrop_add' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.bdrop_add
/-- info: 'Codec.bdrop_bdrop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.bdrop_bdrop
/-- info: 'Codec.bdrop_consumedAbs_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.bdrop_consumedAbs_eq
/-- info: 'Codec.bdrop_drop_eq_bytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.bdrop_drop_eq_bytes
/-- info: 'Codec.bdrop_prepend' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.bdrop_prepend
/-- info: 'Codec.bdrop_prepend_splice' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.bdrop_prepend_splice
/-- info: 'Codec.bdrop_prepend_splice_eq_splice' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.bdrop_prepend_splice_eq_splice
/-- info: 'Codec.bdrop_prepend_splice_len' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.bdrop_prepend_splice_len
/-- info: 'Codec.bdrop_prepend_splice_snd_len' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.bdrop_prepend_splice_snd_len
/-- info: 'Codec.bdrop_seg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.bdrop_seg
/-- info: 'Codec.bdrop_splice' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.bdrop_splice
/-- info: 'Codec.bdrop_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.bdrop_zero
/-- info: 'Codec.bidir' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.bidir
/-- info: 'Codec.blitBytes_spec' does not depend on any axioms -/
#guard_msgs in
#print axioms Codec.blitBytes_spec
/-- info: 'Codec.bpush_data' does not depend on any axioms -/
#guard_msgs in
#print axioms Codec.bpush_data
/-- info: 'Codec.brecOn.eq' does not depend on any axioms -/
#guard_msgs in
#print axioms Codec.brecOn.eq
/-- info: 'Codec.btake_agree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.btake_agree
/-- info: 'Codec.btake_apply' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.btake_apply
/-- info: 'Codec.btake_btake' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.btake_btake
/-- info: 'Codec.btake_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.btake_zero
/-- info: 'Codec.byteConsumesByte' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.byteConsumesByte
/-- info: 'Codec.byteSlice_spec' does not depend on any axioms -/
#guard_msgs in
#print axioms Codec.byteSlice_spec
/-- info: 'Codec.bytesToArray_size' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.bytesToArray_size
/-- info: 'Codec.cands_eq_nil_of_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.cands_eq_nil_of_zero
/-- info: 'Codec.cast_bytes_eq_single' does not depend on any axioms -/
#guard_msgs in
#print axioms Codec.cast_bytes_eq_single
/-- info: 'Codec.cast_bytes_irrel' does not depend on any axioms -/
#guard_msgs in
#print axioms Codec.cast_bytes_irrel
/-- info: 'Codec.cast_bytes_val' does not depend on any axioms -/
#guard_msgs in
#print axioms Codec.cast_bytes_val
/-- info: 'Codec.cast_bytes_val'' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.cast_bytes_val'
/-- info: 'Codec.cast_bytes_val_symm' does not depend on any axioms -/
#guard_msgs in
#print axioms Codec.cast_bytes_val_symm
/-- info: 'Codec.cast_concat_eq_splice' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.cast_concat_eq_splice
/-- info: 'Codec.cast_concat_splice_sub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.cast_concat_splice_sub
/-- info: 'Codec.cast_fin' does not depend on any axioms -/
#guard_msgs in
#print axioms Codec.cast_fin
/-- info: 'Codec.cast_fin_symm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.cast_fin_symm
/-- info: 'Codec.cast_fin_symm_val' does not depend on any axioms -/
#guard_msgs in
#print axioms Codec.cast_fin_symm_val
/-- info: 'Codec.cast_fin_val' does not depend on any axioms -/
#guard_msgs in
#print axioms Codec.cast_fin_val
/-- info: 'Codec.cast_fun_apply' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.cast_fun_apply
/-- info: 'Codec.commitRemainder_spec' does not depend on any axioms -/
#guard_msgs in
#print axioms Codec.commitRemainder_spec
/-- info: 'Codec.concat_assoc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.concat_assoc
/-- info: 'Codec.concat_eq_splice' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.concat_eq_splice
/-- info: 'Codec.consume_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.consume_lt
/-- info: 'Codec.consumedAbs_cast_trans' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.consumedAbs_cast_trans
/-- info: 'Codec.consumedAbs_drop_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.consumedAbs_drop_one
/-- info: 'Codec.consumedAbs_id' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.consumedAbs_id
/-- info: 'Codec.consumedAbs_remaining' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.consumedAbs_remaining
/-- info: 'Codec.countLength' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.countLength
/-- info: 'Codec.countSuccConsumesByte' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.countSuccConsumesByte
/-- info: 'Codec.countToRelRepeat' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.countToRelRepeat
/-- info: 'Codec.count_succ' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.count_succ
/-- info: 'Codec.cursor_bridge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.cursor_bridge
/-- info: 'Codec.decodeArrayFast_eq' does not depend on any axioms -/
#guard_msgs in
#print axioms Codec.decodeArrayFast_eq
/-- info: 'Codec.decodeArray_bounded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeArray_bounded
/-- info: 'Codec.decodeArray_bounded_upper' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeArray_bounded_upper
/-- info: 'Codec.decodeArray_consumes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeArray_consumes
/-- info: 'Codec.decodeArray_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeArray_eq
/-- info: 'Codec.decodeArray_functional_byte' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.decodeArray_functional_byte
/-- info: 'Codec.decodeArray_functional_count' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeArray_functional_count
/-- info: 'Codec.decodeArray_getElem?_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeArray_getElem?_spec
/-- info: 'Codec.decodeArray_unambiguous_byte' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.decodeArray_unambiguous_byte
/-- info: 'Codec.decodeArray_unambiguous_value' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeArray_unambiguous_value
/-- info: 'Codec.decodeArray_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeArray_unique
/-- info: 'Codec.decodeArray_unique_byte' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeArray_unique_byte
/-- info: 'Codec.decodeChainl1_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeChainl1_spec
/-- info: 'Codec.decodeChainr1_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeChainr1_spec
/-- info: 'Codec.decodeFast_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeFast_eq
/-- info: 'Codec.decodeFullArrayFast_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeFullArrayFast_succ
/-- info: 'Codec.decodeFullArrayFast_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeFullArrayFast_zero
/-- info: 'Codec.decodeFullArrayRoot_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeFullArrayRoot_eq
/-- info: 'Codec.decodeFullArraySearch_cons' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeFullArraySearch_cons
/-- info: 'Codec.decodeFullArraySearch_eq_stepPacked' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeFullArraySearch_eq_stepPacked
/-- info: 'Codec.decodeFullArraySearch_nil' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeFullArraySearch_nil
/-- info: 'Codec.decodeFullArray_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeFullArray_spec
/-- info: 'Codec.decodeFullFastRoot_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeFullFastRoot_eq
/-- info: 'Codec.decodeFullFastSearch_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeFullFastSearch_eq
/-- info: 'Codec.decodeFullFast_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeFullFast_succ
/-- info: 'Codec.decodeFullFast_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeFullFast_zero
/-- info: 'Codec.decodeFullStep_cons' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeFullStep_cons
/-- info: 'Codec.decodeFullStep_ne_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeFullStep_ne_none
/-- info: 'Codec.decodeFullStep_nil' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeFullStep_nil
/-- info: 'Codec.decodeFullStep_none_of_forall_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeFullStep_none_of_forall_none
/-- info: 'Codec.decodeFullStep_some' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeFullStep_some
/-- info: 'Codec.decodeFull_at_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeFull_at_zero
/-- info: 'Codec.decodeFull_cast' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeFull_cast
/-- info: 'Codec.decodeFull_ne_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeFull_ne_none
/-- info: 'Codec.decodeFull_reroot_cursor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeFull_reroot_cursor
/-- info: 'Codec.decodeFull_some' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeFull_some
/-- info: 'Codec.decodeFull_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeFull_spec
/-- info: 'Codec.decodeFull_spec_byte' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeFull_spec_byte
/-- info: 'Codec.decodeFull_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeFull_succ
/-- info: 'Codec.decodeFull_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeFull_zero
/-- info: 'Codec.decodeNormal_encode' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.decodeNormal_encode
/-- info: 'Codec.decodeNormal_of_fixed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.decodeNormal_of_fixed
/-- info: 'Codec.decodeOne_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeOne_mem
/-- info: 'Codec.decodeRepeat_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeRepeat_eq
/-- info: 'Codec.decodeRepeat_mem_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeRepeat_mem_iff
/-- info: 'Codec.decodeRepeat_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeRepeat_spec
/-- info: 'Codec.decodeSepBy_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeSepBy_spec
/-- info: 'Codec.decodeTakeWhile_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeTakeWhile_spec
/-- info: 'Codec.decodeWholeBytes_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeWholeBytes_eq
/-- info: 'Codec.decodeWholeBytes_size' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.decodeWholeBytes_size
/-- info: 'Codec.decodeWholeOneBytes_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeWholeOneBytes_eq
/-- info: 'Codec.decodeWholeOne_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeWholeOne_eq
/-- info: 'Codec.decodeWhole_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeWhole_eq
/-- info: 'Codec.decode_cast' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.decode_cast
/-- info: 'Codec.decode_congr_bdrop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.decode_congr_bdrop
/-- info: 'Codec.decode_encode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.decode_encode
/-- info: 'Codec.decode_genuine_suffix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.decode_genuine_suffix
/-- info: 'Codec.decode_genuine_suffix_pointwise' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.decode_genuine_suffix_pointwise
/-- info: 'Codec.decode_seq_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.decode_seq_mem
/-- info: 'Codec.decode_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.decode_spec
/-- info: 'Codec.drop_prepend' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.drop_prepend
/-- info: 'Codec.drop_trans_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.drop_trans_eq
/-- info: 'Codec.drop_zero_eq_id' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.drop_zero_eq_id
/-- info: 'Codec.emptyBytes_unique' depends on axioms: [Quot.sound] -/
#guard_msgs in
#print axioms Codec.emptyBytes_unique
/-- info: 'Codec.emptyConsumesByte' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.emptyConsumesByte
/-- info: 'Codec.encodeArrayFold_toList' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.encodeArrayFold_toList
/-- info: 'Codec.encodeArray_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.encodeArray_eq
/-- info: 'Codec.encodeByteArrayBytes_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.encodeByteArrayBytes_eq
/-- info: 'Codec.encodeChainl1_injective_of_unambiguous' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.encodeChainl1_injective_of_unambiguous
/-- info: 'Codec.encodeChainl1_ne_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.encodeChainl1_ne_none
/-- info: 'Codec.encodeChainl1_of_decode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.encodeChainl1_of_decode
/-- info: 'Codec.encodeChainl1_rel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.encodeChainl1_rel
/-- info: 'Codec.encodeChainr1_injective_of_unambiguous' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.encodeChainr1_injective_of_unambiguous
/-- info: 'Codec.encodeChainr1_ne_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.encodeChainr1_ne_none
/-- info: 'Codec.encodeChainr1_of_decode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.encodeChainr1_of_decode
/-- info: 'Codec.encodeChainr1_rel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.encodeChainr1_rel
/-- info: 'Codec.encodeRepeat_ne_none' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.encodeRepeat_ne_none
/-- info: 'Codec.encodeRepeat_rel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.encodeRepeat_rel
/-- info: 'Codec.encodeSepBy_ne_none' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.encodeSepBy_ne_none
/-- info: 'Codec.encodeSepBy_of_decode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.encodeSepBy_of_decode
/-- info: 'Codec.encodeSepBy_rel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.encodeSepBy_rel
/-- info: 'Codec.encodeTakeWhile_ne_none' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.encodeTakeWhile_ne_none
/-- info: 'Codec.encodeTakeWhile_of_decode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.encodeTakeWhile_of_decode
/-- info: 'Codec.encodeTakeWhile_rel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.encodeTakeWhile_rel
/-- info: 'Codec.encodeWholeBytes_toList' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.encodeWholeBytes_toList
/-- info: 'Codec.encodeWholeRepeatAcc_eq_fold' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.encodeWholeRepeatAcc_eq_fold
/-- info: 'Codec.encodeWholeRepeatAcc_toList' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.encodeWholeRepeatAcc_toList
/-- info: 'Codec.encodeWholeRepeat_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.encodeWholeRepeat_eq
/-- info: 'Codec.encodeWhole_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.encodeWhole_eq
/-- info: 'Codec.encode_injective_of_unambiguous' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.encode_injective_of_unambiguous
/-- info: 'Codec.encode_ne_none' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.encode_ne_none
/-- info: 'Codec.encode_of_decode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.encode_of_decode
/-- info: 'Codec.encode_rel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.encode_rel
/-- info: 'Codec.fastEncodeRepeatAcc_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.fastEncodeRepeatAcc_eq
/-- info: 'Codec.fastEncodeRepeatAcc_full_size' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.fastEncodeRepeatAcc_full_size
/-- info: 'Codec.fastEncodeRepeatAcc_full_toList' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.fastEncodeRepeatAcc_full_toList
/-- info: 'Codec.fastEncodeRepeat_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.fastEncodeRepeat_eq
/-- info: 'Codec.fill_fixed' does not depend on any axioms -/
#guard_msgs in
#print axioms Codec.fill_fixed
/-- info: 'Codec.fill_inj' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.fill_inj
/-- info: 'Codec.fill_raw' does not depend on any axioms -/
#guard_msgs in
#print axioms Codec.fill_raw
/-- info: 'Codec.fill_surj' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.fill_surj
/-- info: 'Codec.filterMap_eq_map_of_forall' does not depend on any axioms -/
#guard_msgs in
#print axioms Codec.filterMap_eq_map_of_forall
/-- info: 'Codec.findByte_spec' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.findByte_spec
/-- info: 'Codec.findFrom_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.findFrom_complete
/-- info: 'Codec.findFrom_finds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.findFrom_finds
/-- info: 'Codec.findFrom_least' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.findFrom_least
/-- info: 'Codec.findFrom_min' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.findFrom_min
/-- info: 'Codec.findFrom_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.findFrom_sound
/-- info: 'Codec.foldl_push_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.foldl_push_append
/-- info: 'Codec.foldl_push_data' does not depend on any axioms -/
#guard_msgs in
#print axioms Codec.foldl_push_data
/-- info: 'Codec.functional_byte' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.functional_byte
/-- info: 'Codec.huniq_byte' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.huniq_byte
/-- info: 'Codec.huniq_not_derivable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.huniq_not_derivable
/-- info: 'Codec.isoConsumesByte' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.isoConsumesByte
/-- info: 'Codec.lengthConst_byte' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.lengthConst_byte
/-- info: 'Codec.lengthDetWitness_unamb' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.lengthDetWitness_unamb
/-- info: 'Codec.lengthDet_byte' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.lengthDet_byte
/-- info: 'Codec.lengthDet_not_implied_by_unamb' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.lengthDet_not_implied_by_unamb
/-- info: 'Codec.lengthDet_of_lengthConst' does not depend on any axioms -/
#guard_msgs in
#print axioms Codec.lengthDet_of_lengthConst
/-- info: 'Codec.length_filterMap_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.length_filterMap_le
/-- info: 'Codec.length_packedCands_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.length_packedCands_le
/-- info: 'Codec.lengths_eq_of_const' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.lengths_eq_of_const
/-- info: 'Codec.list_ofFn_getElem_clean' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.list_ofFn_getElem_clean
/-- info: 'Codec.map_toList_eq_ofFn_none_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.map_toList_eq_ofFn_none_iff
/-- info: 'Codec.mem_decodeArray_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.mem_decodeArray_iff
/-- info: 'Codec.mem_map_range_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.mem_map_range_iff
/-- info: 'Codec.mem_packedCands' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.mem_packedCands
/-- info: 'Codec.min_rotate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.min_rotate
/-- info: 'Codec.nil_append_size' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.nil_append_size
/-- info: 'Codec.nil_append_toList' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.nil_append_toList
/-- info: 'Codec.not_productive_pure' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.not_productive_pure
/-- info: 'Codec.ofFn_concat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.ofFn_concat
/-- info: 'Codec.ofFn_shifted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.ofFn_shifted
/-- info: 'Codec.packedCand_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.packedCand_iff
/-- info: 'Codec.packedCand_of_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.packedCand_of_mem
/-- info: 'Codec.packedCands_aligned' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.packedCands_aligned
/-- info: 'Codec.packedCands_consumes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.packedCands_consumes
/-- info: 'Codec.packedCands_eq_attach' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.packedCands_eq_attach
/-- info: 'Codec.packedCands_length_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.packedCands_length_eq
/-- info: 'Codec.packedCands_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.packedCands_mem
/-- info: 'Codec.prepend_apply' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.prepend_apply
/-- info: 'Codec.prepend_assoc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.prepend_assoc
/-- info: 'Codec.prepend_drop_of_prepend_splice' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.prepend_drop_of_prepend_splice
/-- info: 'Codec.prepend_drop_single' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.prepend_drop_single
/-- info: 'Codec.prepend_empty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.prepend_empty
/-- info: 'Codec.prepend_empty_apply' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.prepend_empty_apply
/-- info: 'Codec.prepend_empty_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.prepend_empty_eq
/-- info: 'Codec.prepend_empty_self' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.prepend_empty_self
/-- info: 'Codec.prepend_eq_of_eq_splice' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.prepend_eq_of_eq_splice
/-- info: 'Codec.prepend_id' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.prepend_id
/-- info: 'Codec.prepend_prefix_agree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.prepend_prefix_agree
/-- info: 'Codec.prepend_prefix_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.prepend_prefix_eq
/-- info: 'Codec.prepend_prefix_read' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.prepend_prefix_read
/-- info: 'Codec.prepend_single_bdrop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.prepend_single_bdrop
/-- info: 'Codec.productive_iff_consumesByte' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.productive_iff_consumesByte
/-- info: 'Codec.pushBytesFrom_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.pushBytesFrom_eq
/-- info: 'Codec.pushBytes_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.pushBytes_eq
/-- info: 'Codec.relAligned_byte' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.relAligned_byte
/-- info: 'Codec.relChainl1_cast' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.relChainl1_cast
/-- info: 'Codec.relChainr1_cast' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.relChainr1_cast
/-- info: 'Codec.relRepeatToCount' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.relRepeatToCount
/-- info: 'Codec.relRepeat_cast' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.relRepeat_cast
/-- info: 'Codec.relRepeat_cons' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.relRepeat_cons
/-- info: 'Codec.relRepeat_cons_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.relRepeat_cons_eq
/-- info: 'Codec.relRepeat_induction' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.relRepeat_induction
/-- info: 'Codec.relRepeat_length_of_const' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.relRepeat_length_of_const
/-- info: 'Codec.relRepeat_nil' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.relRepeat_nil
/-- info: 'Codec.relRepeat_prefix_inj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.relRepeat_prefix_inj
/-- info: 'Codec.relRepeat_suffix_inj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.relRepeat_suffix_inj
/-- info: 'Codec.relRepeat_unbounded_of_empty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.relRepeat_unbounded_of_empty
/-- info: 'Codec.relRepeat_unique_same_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.relRepeat_unique_same_length
/-- info: 'Codec.relSepBy_cast' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.relSepBy_cast
/-- info: 'Codec.relTakeWhile_cast' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.relTakeWhile_cast
/-- info: 'Codec.relUnambAlignedWitness_unamb' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.relUnambAlignedWitness_unamb
/-- info: 'Codec.relUnambiguous_not_implies_relAligned' does not depend on any axioms -/
#guard_msgs in
#print axioms Codec.relUnambiguous_not_implies_relAligned
/-- info: 'Codec.relUnambiguous_of_relAligned' does not depend on any axioms -/
#guard_msgs in
#print axioms Codec.relUnambiguous_of_relAligned
/-- info: 'Codec.rel_byte_cast' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.rel_byte_cast
/-- info: 'Codec.remaining_at_cursor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.remaining_at_cursor
/-- info: 'Codec.remaining_at_reroot' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.remaining_at_reroot
/-- info: 'Codec.reroot_bytes_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.reroot_bytes_eq
/-- info: 'Codec.reverse_cons_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.reverse_cons_append
/-- info: 'Codec.roundtrip' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.roundtrip
/-- info: 'Codec.satisfyConsumesByte' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.satisfyConsumesByte
/-- info: 'Codec.search_nil_left' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.search_nil_left
/-- info: 'Codec.search_nil_right' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.search_nil_right
/-- info: 'Codec.seqConsumesByte' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.seqConsumesByte
/-- info: 'Codec.seqCountConsumesByte' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.seqCountConsumesByte
/-- info: 'Codec.spec_at_advance' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.spec_at_advance
/-- info: 'Codec.splice_add' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.splice_add
/-- info: 'Codec.splice_apply' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.splice_apply
/-- info: 'Codec.splice_cast_commute' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.splice_cast_commute
/-- info: 'Codec.splice_prefix_agree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.splice_prefix_agree
/-- info: 'Codec.splice_prefix_read' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.splice_prefix_read
/-- info: 'Codec.splice_splice_assoc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.splice_splice_assoc
/-- info: 'Codec.splice_splice_len' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.splice_splice_len
/-- info: 'Codec.stepPacked_eq_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.stepPacked_eq_step
/-- info: 'Codec.step_bytes_pointwise' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.step_bytes_pointwise
/-- info: 'Codec.sub_sub_add' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.sub_sub_add
/-- info: 'Codec.sub_sub_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.sub_sub_eq
/-- info: 'Codec.sub_sub_sub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.sub_sub_sub
/-- info: 'Codec.suffix_consumed_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.suffix_consumed_lt
/-- info: 'Codec.unambiguous_byte' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.unambiguous_byte
/-- info: 'Codec.uniqCounterexample_pair' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.uniqCounterexample_pair
/-- info: 'Codec.uniqCounterexample_productive' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.uniqCounterexample_productive
/-- info: 'Codec.uniqCounterexample_single' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.uniqCounterexample_single
/-- info: 'Codec.uniqCounterexample_unambiguous' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.uniqCounterexample_unambiguous
/-- info: 'Codec.uniqSeqBo_false' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.uniqSeqBo_false
/-- info: 'Codec.uniqSeqBo_true' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.uniqSeqBo_true
/-- info: 'Codec.uniqSeqBo_unambiguous' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.uniqSeqBo_unambiguous
/-- info: 'Codec.uniqSeqD2_one' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.uniqSeqD2_one
/-- info: 'Codec.uniqSeqD2_unambiguous' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.uniqSeqD2_unambiguous
/-- info: 'Codec.uniqSeqD2_zero' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.uniqSeqD2_zero
/-- info: 'Codec.uniqSeqWhole_false' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.uniqSeqWhole_false
/-- info: 'Codec.uniqSeqWhole_true' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.uniqSeqWhole_true
/-- info: 'Codec.uniqSeq_not_congruent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.uniqSeq_not_congruent
/-- info: 'Codec.uniqSeq_not_relAligned' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.uniqSeq_not_relAligned
/-- info: 'Codec.uniqSeq_unambiguous_not_congruent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.uniqSeq_unambiguous_not_congruent
/-- info: 'Iso.apply_eq_some_of_unapply' does not depend on any axioms -/
#guard_msgs in
#print axioms Iso.apply_eq_some_of_unapply
/-- info: 'Iso.bind_eq_some' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Iso.bind_eq_some
/-- info: 'Iso.counterMeasureDecreases' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Iso.counterMeasureDecreases
/-- info: 'Iso.counterMeasureDecreasesR' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Iso.counterMeasureDecreasesR
/-- info: 'Iso.dropLast_append_last' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Iso.dropLast_append_last
/-- info: 'Iso.foldRec_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Iso.foldRec_append
/-- info: 'Iso.ite_some_eq_some' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Iso.ite_some_eq_some
/-- info: 'Iso.law' does not depend on any axioms -/
#guard_msgs in
#print axioms Iso.law
/-- info: 'Iso.map_fst_reverse_eq_some' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Iso.map_fst_reverse_eq_some
/-- info: 'Iso.map_swap_eq_none' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Iso.map_swap_eq_none
/-- info: 'Iso.map_swap_eq_some' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Iso.map_swap_eq_some
/-- info: 'Iso.unapply_eq_some_of_apply' does not depend on any axioms -/
#guard_msgs in
#print axioms Iso.unapply_eq_some_of_apply
/-- info: 'Iso.unfoldBy_eq' does not depend on any axioms -/
#guard_msgs in
#print axioms Iso.unfoldBy_eq
/-- info: 'Iso.unfoldBy_of_fold' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Iso.unfoldBy_of_fold
/-- info: 'Iso.unfoldBy_sound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Iso.unfoldBy_sound
-- END GENERATED body
