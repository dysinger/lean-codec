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

**Those two `ConstantInfo` constructors are not the namespace.** `ConstantInfo` has
seven, and until `codec-audit-round-eight` §1 the file's header claimed the universe
was "every constant in the `Codec` or `Iso` namespace" while `opaqueInfo` and
`axiomInfo` were matched by **no arm at all** — not gated, not partition-checked, not
counted. That sentence was false. What is now true, and asserted by the
`constantKindCensus` block below, is the *measured* table:

| `ConstantInfo` constructor | in the universe? | count today |
| --- | --- | --- |
| `thmInfo` | **yes** — the gated/allowlist partition | 769 |
| `defnInfo` | **yes** — the mention proxy | 348 |
| `opaqueInfo` | **NO, and that is a hole** — printed, so a non-zero count is loud | **0** |
| `axiomInfo` | **NO, and that is a hole** — printed | **0** |
| `inductInfo` / `ctorInfo` / `recInfo` / `quotInfo` | no — types and compiler machinery, no body to check | 8 / 14 / 8 / 0 |

**`opaque`/`axiom` are *deliberately out*, and the exclusion list is not the
mechanism.** An `opaque` publishes a value with no body; an `axiom` publishes a claim
with no proof. Neither has a proof to footprint-check, so neither *can* be gated — but
that is not why the gate may ignore them. The reason a count exists is that both are
law-*shaped*: an authored `opaque` asserting a property would be invisible to every
arm, and the previous defence was worse than silence — `exclusions` **refuses** an
`opaque` outright (`it is not a public theorem`), so an exclusion could not cover one
even if it leaked `Classical.choice`. The census makes a future `opaque` a printed
nonzero rather than an absence, and the arm **fails the build** on one. If a real
`opaque` is ever wanted, it needs an arm of its own; the count is the tripwire that
forces that conversation instead of letting the constant slip in unnoticed.

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

**But a mention proxy is only as strong as the filter feeding it, and until
`codec-audit-round-five` that filter had no audit arm.** `isDerivedDefName` removes a
`def` from the universe *before* the mention check is computed, so a dropped `def`
and a `def` that was never written were indistinguishable to every check above — and
the name it was dropping was **`Iso.prod`, the paper's own `×`**. Two more checks
(§1.1 / R6-01) close that:

* `derivedDefDeclinationAudit` — every public `def` the classifier drops must appear
  in `derivedDefAllowlist` **with a reason**, mirroring `partition`'s rule for
  theorems;
* `derivedDefPatternAudit` — the classifier's own pattern list is verified: a pattern
  that matches **no** declaration, or one that removes a name
  `definitionSurfaceAllowlist` describes as authorial, is a build failure naming it.

This is the same lesson every round of this audit has produced, stated as a rule:
**a gate is only as strong as its narrowest unaudited step — when you add a check, ask
what removes things from its input, and whether that removal is recorded.**

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

**425** public theorems are covered, by a partition with no third route:

| side | count | what it is |
| --- | --- | --- |
| gated (`gatedNames`) | **342** | footprint pinned by `#print axioms` |
| allowlisted (`generatedAuxAllowlist`) | **83** | not a law; reason recorded in place |
| un-gated and unlisted | **0** | a build failure, by construction |

Gated footprint distribution — **generated** from the same `collectAxioms` results the
`#guard_msgs` blocks pin (`scripts/gen-axioms.lean`), not transcribed:

-- BEGIN GENERATED distribution

| footprint | count |
| --- | --- |
| `[propext, Quot.sound]` | 219 |
| `[propext]` | 92 |
| `[Quot.sound]` | 4 |
| axiom-free | 27 |
| anything else | 0 |
| **total** | **342** |

`[propext, Classical.choice, Quot.sound]` rows: **0** — every gated law is
inside the discipline.
-- END GENERATED distribution

Definitions, by the third check:

| side | count | what it is |
| --- | --- | --- |
| public `def`s (after dropping compiler machinery) | **140** | the universe |
| named by a gated theorem's type | **115** | *mentioned* — the proxy's whole measurement (a mention, not a strength claim) |
| `definitionSurfaceAllowlist` | **25** | no law; reason recorded in place |
| silent | **0** | a build failure, by construction |

**And every name the classifier removes is now on the record too.** A fourth check
(`derivedDefDeclinationAudit`, `codec-audit-round-five` §1.1 / R6-01) requires each
`def` that `isDerivedDefName` drops to appear in `derivedDefAllowlist` **with a
reason**, and a fifth (`derivedDefPatternAudit`) verifies the classifier's own
pattern list: a pattern matching no declaration, or one that removes a name
`definitionSurfaceAllowlist` calls authorial, is a build failure. That pair is what
closed the hole this table could not see: `Iso.prod` — the paper's own `×` — had been
removed from the universe by a `"prod"` entry in `derivedDefPatterns` and was in
neither list, so
`141 / 112 / 29` was a **green gate with the paper's product functor outside it**.
An earlier revision called that a *suffix* entry; it is a **last-name-component**
pattern (`derivedDefPatterns` is matched against `n.components.getLast!`, i.e. a whole
component, not a suffix — `codec-audit-round-eight` S-6). The distinction matters
because the classifier misses `brecOn.go` by exactly that confusion.
The `"prod"` entry is gone, `Iso.prod` re-entered the universe and got a law
(`Iso.prod_apply_eq_some`), and the four dead entries (`rec`, `mk`, `sizeOf`, plus the
mis-spelled `brecOn.go`) are gone because the new pattern audit re-adds a
dead one as an error.

The middle row is a **mention proxy**, and the column says so deliberately. It
measures one thing: that no public definition can be covered by *silence*. It is
**not** a count of definitions with characterised behaviour, and it can be satisfied
vacuously — by a theorem that mentions the constant trivially. Two entries here are
exactly that: `decodeArrayFast_eq` and `decodeWholeOneBytes_eq` are `rfl` unfolds of
their own bodies, which their docstrings admit. An earlier revision of this table
said "has a stated law, by the proxy", which over-read the count by those two; what
changed is what the column claims.

**An empty axiom footprint is NOT the signature of a restatement — the diagnostic
that said so has been deleted** (`codec-audit-round-five` R6-03, design §D4). This
paragraph used to read "`#print axioms` reports *no axioms*, the signature of a
restatement rather than a law", and that is **false for one of its own two named
examples**: `Codec.decodeWholeOneBytes_eq` reports `[propext, Quot.sound]`, not *no
axioms*, so the diagnostic fails on the example it was built from. It also
over-flags the three Layer-2 `*_spec`s (`commitRemainder_spec`, `byteSlice_spec`,
`blitBytes_spec`), which are honest identities *of a definition* and load-bearing
referents for the C trust contract — they are not vacuous, and two of them report no
axioms.

Axiom-freeness is **neither necessary nor sufficient** for a restatement, so no
repair keeps the sentence true. Name an identity by **`#print`ing its body**: a
`rfl`-unfolded `def` shows as `fun … => <its own definition>`, which is checkable,
while an empty footprint is not. `Codec.Nat.eq_irrel` is the standing counterexample
on the law side — it is axiom-free and is an authored law.

**The theorem/definition counts are asserted, and the footprint table is
generated** — two mechanisms, because they have different failure modes.

* The *counts* are asserted by `headerNumbers` at the end of this file: a stale table
  is a build failure. That is not decoration — this table said `364 / 292` and
  `197 / 61 / 4 / 30` after the gated set had already reached `382 / 310` and
  `201 / 74 / 4 / 31` (correction landed in `9db99b8`, the regeneration that swapped
  the distribution table to generated), because `partition`/`gateCoverage` compare set
  *membership* and never read the prose.
* The *footprint distribution* is now **generated** by `scripts/gen-axioms.lean`
  (`codec-audit-round-three` §1.9), counting the `collectAxioms` name lists rather than
  parsing renderered prose. It keys on names, so the audit's own failure mode — a
  parser truncating at the `?` in `Codec.attach_getElem?_corr` — cannot recur (design
  D1). On the regeneration that introduced it the generated table **equalled the
  hand-written one** (`209 / 78 / 4 / 34 = 325`), which is D1's "the table is correct
  today" re-confirmed by the compiler rather than by re-reading it.

`Codec.Nat.eq_irrel` is one of the axiom-free group above, and it is in the gated set only
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

/-- `Prop`-valued structure-field projections, recognised **by name** rather than by
suffix, because a projection's last component is the field's own name (`law`,
`fixed`, `idem`) and there is no shared shape to match on.

These are not laws: each is `fun … => self.2`-shaped, reports **no axioms**, and
asserts nothing beyond the type the caller supplied (`codec-audit-round-five` R6-02,
design §D3). The `dec`-suffixed trio (`MeasureDecreases.dec`, `MeasureDecreasesR.dec`,
`Unfold.dec`) is caught by the suffix rule instead; **all seven are classified the same
way**, which is the point — the file used to gate three of them and allowlist the
other three, and a fourth (`Codec.Suffix.hle`) went unclassified until the
completeness arm below found it.

This is the same kind of data as `derivedDefPatterns`: a list the partition check
audits, so a name here that is not actually a structure-field projection would fail
rather than silently leave a law un-gated.

**`Codec.fill_fixed` is NOT here, and that decision is recorded here because it cannot
live at its pin.** A note was first written on the `gatedNames` entry for `fill_fixed`;
§5.5's regeneration diff showed the `gatedNames` region is **generated wholesale**, so a
per-name comment there is destroyed by the next `gen-axioms.lean` run. The durable home
for "why this name is/is not a projection" is this docstring, next to the predicate that
decides it.

`Codec.fill_fixed` (`Codec/Normal.lean:163`) unwraps an `h : fill nz s = …`-shaped
hypothesis, so a body-shape-only test is tempted to call it a projection. It is not: its
operand is `Codec.fill nz s`, a **constructed value**, not something the caller supplied,
and `isProjConst Codec.fill` is `false` — so `isBareProj`'s operand recursion rejects it
for the same principled reason it rejects `Codec.bidir` (`codec-gate-denominators` §3.5).
It has zero *theorem* consumers, but `Bench.lean:103` calls it, so "zero consumers" would
have been the wrong argument — and it is not the argument used. **It stays gated. Do not
re-open this without measuring `isProjConst` first.**

**Two directions, two arms** (`codec-audit-round-eight` §2). The *completeness* arm
(walks the environment, requires every bare projection to be listed) has existed since
`codec-audit-round-seven` GC-04. The *validity* arm — every **listed** name is itself
a bare projection — was only added in round eight, and until then the sentence above
was a claim about a mechanism that did not exist: a non-projection name added here
would be silently accepted and silently removed from the universe. If you add an entry
here, both arms will check it. -/
def propProjections : Array Name := #[
  `Iso.law,
  `Codec.Normal.fixed,
  `Codec.Normalizer.idem,
  /- **A seventh, found by the completeness arm below** (`codec-audit-round-seven`
  GC-02). `Codec.Suffix.hle : remaining ≤ n` is `Prop`-valued, so its projection is
  `fun … => self.2` — the same shape as `Iso.law`, reporting no axioms and asserting
  nothing beyond the type the caller supplied. It was gated as a law while its six
  siblings were allowlisted, and the prose below said "all six are classified the same
  way". The completeness arm is what caught it, which is the argument for having a
  structural check rather than only a list. -/
  `Codec.Suffix.hle,
  /- **Five captures added by `codec-gate-denominators` §3.** Each body is a selection out
  of something the *caller* supplied, so each asserts nothing beyond a type a caller
  already had. The **completeness** arm demanded them here as soon as the predicate was
  fixed; the **validity** arm checks each entry once it is here. `CandAligned_tail` is
  deliberately **absent** — its body is `And.casesOn hal fun hlen hpt => ⟨…, …⟩`, a
  genuine proof about an invariant, and it stays gated (§3.4). -/
  /- `fun hal => hal.1`, over the `RelAligned`/`LengthDet` pair. -/
  `Codec.CandAligned_fst,
  /- `fun hal => hal.2.1`, the same selection one field deeper. -/
  `Codec.CandAligned_at,
  /- `c.property.1`: a projection of an *argument*'s proof field. It asserts nothing, but
  it **names** a membership (`c.val ∈ decodeArray d a k`) that every caller would
  otherwise spell out, so it earns its keep as documentation rather than as a law.
  Recorded so a later round does not "fix" it back into the gated set (§3.6). -/
  `Codec.packedCands_mem,
  /- `Iso.law i a b` and its twin: a selection out of the *field* of an `Iso` the caller
  supplied. `Iso.law`'s **body** is what makes these projections while `Codec.roundtrip`
  is not, even though both are `Iff.mpr`/`Iff.mp` at arity 4 — `isProjConst` reads the
  body, and the recursion reads what the constant is applied to (§3.2/§3.3). -/
  `Iso.apply_eq_some_of_unapply,
  `Iso.unapply_eq_some_of_apply,
]

/-! ### `isBareProj` — one definition, read by both directions

`codec-gate-denominators` §2. Two `let rec isBareProj` literals sat five hundred lines
apart in this file under a comment asserting they were "one definition … so they cannot
drift apart". `run_cmd` blocks cannot share a `let rec`, so they **were** two copies, and
the comment was false about the mechanism. They are now one top-level definition, and the
hoist and the fix are the same edit: hoisting the old bare-`.proj` test and then
replacing it would have edited the same line twice and revisited every call site.

**Why this predicate and not a head-constant set.** Round ten measured (reproduced in
`scratch/probe-headset.lean`) that accepting a spine ending in a constant from
`{And.left, And.right, Iff.mp, Iff.mpr, Prod.fst, Prod.snd}` captures **seven**
declarations, including `Codec.roundtrip`, `Codec.findFrom_finds`,
`Iso.apply_eq_some_of_unapply` and `Iso.unapply_eq_some_of_apply` — four genuine laws.
The distinguishing fact is not the head constant (shared) and not the arity
(`Iff.mp` is at arity 4 for both `roundtrip`, a *theorem*, and
`unapply_eq_some_of_apply`, a *field*): it is **the head constant's own body**. Every
genuine projection here has a `proj` body (`Iso.law`, `And.left`, `Subtype.property`,
`Codec.Normal.fixed` all peel to `proj#0`), while a proved theorem that merely has an
`↔`/`∧` *result type* does not (`Codec.bidir`'s body is a `let`;
`Option.ne_none_iff_exists'` is `Iff.trans`). So the discriminator is the body, and the
recursion over the selected operand is what separates a projection of a *hypothesis* from
an application of a *proved theorem*.

**Four recorded blind spots**, all in the safe direction or unreachable:

1. It flags `fun (x : α × β) => x.1` — a projection of an *argument* — as a projection.
   Safe: the name is demanded in `propProjections` and a human decides. The alternative
   is a false negative, which un-gates a law.
2. It does **not** see a *wrapped* projection, `fun self => id self.law`. Measured: zero
   such theorems exist, so the hole is latent. Closing it would change what "is a
   projection" means for the completeness arm, which is a separate decision.
3. Hypothesis-vs-theorem is closed by the operand recursion (above): a proved theorem
   stops at the first step because its head is not a projection constant.
4. An **under-applied** projection constant is accepted (`args[i]? = none → true`).
   Unreachable today, and safe.

**`firstExplicitIdx`, not `args.getLast?`.** The two produce **byte-identical output** on
today's tree, so the wrong one passes every test — and it is wrong: `CandAligned_at`'s
operand is `args[2]` while `args[7]` is a different bound variable. An accessor that
agrees by luck is the `isDerivedDefName` shape again (a rule that is right for the wrong
reason), which is why the telescope is read rather than the spine indexed from the end.
"`And.left`/`And.right` at their declared arity" was the other tempting wrong answer: a
spike measured `And.right` reached at arity **8** in `CandAligned_at` and arity 3
elsewhere, so "declared arity" is a category mismatch, not a mechanism. -/

/-- Peel `lam` and `mdata` wrappers, which carry no computational content. -/
def peelLamsMdata : Expr → Expr
  | .lam _ _ b _ => peelLamsMdata b
  | .mdata _ b => peelLamsMdata b
  | e => e

/-- Decompose the outermost application spine as `(head, args)` with `args` left to
right, so `args[0]` is the head constant's first argument. -/
partial def appSpine (e : Expr) : Expr × List Expr :=
  let rec go : Expr → List Expr → Expr × List Expr
    | .app f a, acc => go f (a :: acc)
    | h, acc => (h, acc)
  go e []

/-- Index of the first **explicit** binder in a declared telescope, i.e. which argument
of the constant is the thing being selected from (the `self`, the `And`, the `iff`).
Read off the *declared* signature, not the spine — see the section docstring. -/
def firstExplicitIdx (ty : Expr) : Option Nat :=
  let rec go : Expr → Nat → Option Nat
    | .forallE _ _ b bi, i => if bi == .default then some i else go b (i + 1)
    | _, _ => none
  go ty 0

/-- Is constant `c` a **projection constant**: does its own body peel to a bare
`Expr.proj`? This is what separates a structure field from a proved theorem that happens
to have an `↔`/`∧` in its type. -/
def isProjConst (env : Environment) (c : Name) : Bool :=
  match env.find? c with
  | some (.thmInfo ti) =>
    match peelLamsMdata ti.value with
    | .proj _ _ _ => true
    | _ => false
  | some (.defnInfo di) =>
    match peelLamsMdata di.value with
    | .proj _ _ _ => true
    | _ => false
  | _ => false

/-- `True` iff `e` is a proof term whose value is **a selection from something the caller
supplied**: a bound/free variable, a bare projection, or a projection constant applied to
something that is itself such.

The `bvar`/`fvar` leaves are the hypothesis case (`CandAligned_fst := fun … hal =>
hal.left`). The recursion is the field case (`Iso.law i a b` selects from `i`, a
hypothesis). A proved theorem fails at the first step, because its head is not a
projection constant — that is the whole distinction. -/
partial def isProjOfHyp (env : Environment) (e : Expr) : Bool :=
  let e := peelLamsMdata e
  match e with
  | .proj _ _ _ => true
  | .bvar _ => true
  | .fvar _ => true
  | _ =>
    let (h, args) := appSpine e
    match h with
    | .const c _ =>
      if !isProjConst env c then false
      else
        match env.find? c with
        | none => false
        | some ci =>
          match firstExplicitIdx ci.type with
          | none => true
          | some i =>
            match args[i]? with
            | none => true
            | some src => isProjOfHyp env src
    | _ => false

/-- **The one definition of "this body is a bare projection"**, read by both the
completeness arm and the validity arm. Before this, a name list was the only mechanism;
now the mechanism is structural and the list is what the mechanism demands.

Blind spots and the reason `firstExplicitIdx` replaces `args.getLast?` are in the section
docstring above. -/
def isBareProj (env : Environment) (e : Expr) : Bool :=
  match peelLamsMdata e with
  | .proj _ _ _ => true
  | _ =>
    let (h, args) := appSpine (peelLamsMdata e)
    match h with
    | .const c _ =>
      if !isProjConst env c then false
      else
        match env.find? c with
        | none => false
        | some ci =>
          match firstExplicitIdx ci.type with
          | none => true
          | some i =>
            match args[i]? with
            | none => true
            | some src => isProjOfHyp env src
    | _ => false

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
  -- `Prop`-valued structure-field projections have no shared suffix: their last
  -- component is the field's own name. Recognised by name instead.
  if propProjections.contains n then return true
  let s := n.components.getLast!.toString
  return s == "eq_def" || s == "inj" || s == "injEq" || s == "sizeOf_spec" ||
    s == "congr_simp" || s == "dec" || s == "induct" || s == "eq"

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

/-- The compiler-machinery patterns `isDerivedDefName` matches, as data, so that the
build-time check below can audit the list rather than trust it. An entry here removes
every `def` whose **last** name component it equals from the gate's universe.

`rec`, `mk` and `sizeOf` used to be listed and matched **no** `def` in `Codec`/`Iso`
(`codec-audit-round-five` R6-37): the derived companions Lean actually emits are
`recOn`/`casesOn`/`elim`/…, and a structure's `mk` is a *constructor*, a
`ctorInfo`, so it never reaches this filter at all. They were deleted. The audit arm
below re-adds such an entry as a build **failure** rather than a silent default.

**`prod` is deliberately absent.** It used to be here, and it silently removed
`Iso.prod` — the paper's `×` — from the universe, which is the defect
`codec-audit-round-five` §1 exists to close (R6-01). -/
def derivedDefPatterns : Array String := #[
  "casesOn", "recOn", "elim",
  "noConfusion", "noConfusionType",
  "ctorIdx", "ctorElim", "ctorElimType",
  "below", "brecOn",
  -- `go` — the worker a `brecOn`-compiled mutual recursion is emitted as. It was
  -- previously listed as `"brecOn.go"`, which matched **nothing** (a name's last
  -- component is `go`, not `brecOn.go`), so the pattern was dead and R6-37 deleted it;
  -- deleting it exposed `Codec.brecOn.go` as a public `def` in the universe. Listed
  -- correctly here. Measured: it is the **only** public `Codec`/`Iso` name whose last
  -- component is `go`, so this pattern removes exactly the recursion worker.
  "go",
  -- Notation aliases: a token bound to an existing declaration, so the *declaration*
  -- is what has (or lacks) a law, not the token. `Iso.«term_≫_»` is `Infixr "≫" =>
  -- Iso.trans`, whose law is `Iso.trans`'s own `law` field.
  "«term_≫_»"
]

/-- The classifier's rule, as **one** predicate over a name.

`isDerivedDefName` is this applied to a name; `derivedDefPatternRemovals` buckets names
by this same test, so the list of causes the audit counts and the rule the classifier
applies cannot be two different lists. Named because the audit's reason string quotes
it, and because a rule with two spellings is how a list and its audit drift apart
(`codec-audit-round-eight` §7.2's mirror list is the recorded example). -/
def derivedDefMatchingPattern (n : Name) : Option String :=
  let last := n.components.getLast!.toString
  if derivedDefPatterns.contains last then some last else none

/-- Default classifier for `def` names that are **not** authorial surface: the
companions Lean emits for every inductive and structure. Same status as
`isGeneratedAux` — a heuristic, audited by the check below, never an authority. -/
def isDerivedDefName (n : Name) : Bool :=
  (derivedDefMatchingPattern n).isSome

/-- Every public `def` in the `Codec`/`Iso` namespaces **before** any name-based
declination — the universe `publicDefs` and `derivedDefAllowlist` must partition.

Same public-surface filter as `publicTheorems`: unsafe, private and internal-detail
names are not public surface at all, so they are outside the universe rather than
dropped from it. -/
def candidateDefs (env : Environment) : Array Name := Id.run do
  let mut ds : Array Name := #[]
  for (name, ci) in env.constants.toList do
    if (`Codec).isPrefixOf name || (`Iso).isPrefixOf name then
      match ci with
      | .defnInfo _ =>
        if ci.isUnsafe || isPrivateName name || name.isInternalDetail then
          pure ()
        else
          ds := ds.push name
      | _ => pure ()
  return ds.qsort (fun a b => Name.toString a < Name.toString b)

/-- The classifier's removals **decomposed by pattern** — `codec-gate-denominators` §1.

`isDerivedDefName` answers "is this name dropped", which is all `publicDefs` needs. It
does **not** answer "which pattern dropped it, and how many did that pattern take",
and that is the half the gate was missing: the audit arm printed
`{dropped.size} definitions dropped by the name classifier` — one number for twelve
patterns — so a pattern removing exactly one declaration was one rename away from
matching nothing, and nothing could tell that from a pattern removing fifteen by
design.

The rule this change installs (design D1) is that every arm reports its **denominator**
and its **removals decomposed by cause**, both asserted. For this classifier the
denominator is the two halves of `candidateDefs` — "matching some pattern" and "not" —
and the causes are the patterns, so the decomposition is a `(pattern, names it
removed)` list rather than a count: a count cannot be reviewed, and a list can.

Both halves are returned, so the arm can print `removed + kept = candidateDefs` — the
identity that makes "the decomposition covers the classifier" a checked statement
instead of an assumption. -/
def derivedDefPatternRemovals (env : Environment) :
    Array (String × Array Name) × Array Name :=
  let cands := candidateDefs env
  let pats := derivedDefPatterns.map fun p =>
    (p, cands.filter fun n => derivedDefMatchingPattern n == some p)
  (pats, cands.filter fun n => (derivedDefMatchingPattern n).isNone)

/-- What `expectedDerivedDefPatternCounts` asserts: the discriminations that make the
classifier's printed decomposition reviewable, as numbers, so a change to any of them
fails the build.

Four quantities, because one total would hide exactly what the decomposition is for:

* `patterns` — `derivedDefPatterns.size`, the denominator of the audit: how many causes
  the classifier *claims* to have. Deleting or adding a pattern moves this.
* `removed` — the names the classifier actually removes. The numerator.
* `singleton` — patterns removing **exactly one** declaration. This is the number the
  change exists to surface: each such pattern is one rename from dead, and only
  `derivedDefPatternAudit`'s dead-pattern arm would catch it. Measured today it is
  **6** of 12 — `ctorElim`, `ctorElimType`, `below`, `brecOn`, `go`, `«term_≫_»` — which
  is a fact worth seeing rather than inferring from a total.
* `uncounted` — `candidateDefs` names in **neither** the removal decomposition nor the
  kept half. Must be `0`, and is asserted rather than assumed: `removed + kept =
  candidateDefs` is the identity that makes "the decomposition covers the classifier"
  a checked statement. A single `(pattern, count)` tuple would have left it unstated —
  be the fifteenth instance or close it.

Read the numbers from the arm's log line, never from this docstring: the comment is
prose and the `throwError` is the check (`headerNumbers`' lesson — a prose count rots
while the gate stays green). -/
def expectedDerivedDefPatternCounts : Nat × Nat × Nat × Nat := (12, 54, 6, 0)

/-- Every public `def` in the `Codec`/`Iso` namespaces, **after** dropping compiler
machinery and non-public names. This is the universe `definitionSurfaceAllowlist`
and "mentioned by a gated theorem" must partition. -/
def publicDefs (env : Environment) : Array Name :=
  (candidateDefs env).filter fun n => !isDerivedDefName n

/-- The def-side twin of `generatedAuxAllowlist`: every public `def` the name
classifier drops, listed **by name with the reason it is not authorial surface**.

This is `codec-audit-round-five` §1's arm (R6-01), and it exists because the theorem
side already had it and the def side did not: `isDerivedDefName` removed a name from
the gate's universe *before* `publicDefs` was computed, so a dropped `def` and a `def`
that was never written were indistinguishable to every check. That is how `Iso.prod`
— the paper's own `×` — sat outside a green gate.

That is exactly why three of the theorem-side reason groups have no counterpart
here: a structure's `mk` is a *constructor* (`ctorInfo`), and `eq_def`/`inj`/
`injEq`/`sizeOf_spec`/`congr_simp` are **theorems**, so none of them is a `defnInfo`
and the classifier never sees them. Only the genuinely `defnInfo`-shaped companions
belong in this list, and each is recorded below.

Keep the reason next to the entry. A bare name here is the dumping ground this list
exists to avoid, and the `derivedDefPatternAudit` check below will not let one in
without a reason. -/
def derivedDefAllowlist : Array Name := #[
  -- **Derived recursors and case eliminators.** Lean emits one per inductive and per
  -- structure; they are the machinery a `def`-by-recursion is compiled *through*, not
  -- definitions a human wrote about a codec.
  `Codec.casesOn, `Codec.recOn, `Iso.casesOn, `Iso.recOn,
  `Codec.Normal.casesOn, `Codec.Normal.recOn,
  `Codec.Suffix.casesOn, `Codec.Suffix.recOn,
  `Iso.Unfold.casesOn, `Iso.Unfold.recOn,
  `Iso.MeasureDecreases.casesOn, `Iso.MeasureDecreases.recOn,
  `Codec.Normalizer.casesOn, `Codec.Normalizer.recOn,
  `Iso.MeasureDecreasesR.casesOn, `Iso.MeasureDecreasesR.recOn,

  -- **Per-constructor case eliminators** (`casesOn` specialised to one constructor).
  `Codec.byte.elim, `Codec.empty.elim, `Codec.iso.elim, `Codec.alt.elim,
  `Codec.satisfy.elim, `Codec.pure.elim, `Codec.seq.elim,

  -- **`noConfusion` / `noConfusionType`** — the constructor-disjointness lemma and
  -- the type it goes through. Says two different constructors cannot be equal, which
  -- the inductive's own typing already gives.
  `Codec.noConfusion, `Codec.noConfusionType, `Iso.noConfusion,
  `Iso.noConfusionType,
  `Codec.Normal.noConfusion, `Codec.Normal.noConfusionType,
  `Codec.Normal.mk.noConfusion,
  `Codec.Suffix.noConfusion, `Codec.Suffix.noConfusionType,
  `Codec.Suffix.mk.noConfusion,
  `Codec.alt.noConfusion, `Codec.iso.noConfusion, `Codec.pure.noConfusion,
  `Codec.satisfy.noConfusion, `Codec.seq.noConfusion, `Codec.empty.noConfusion,
  `Iso.Unfold.noConfusion, `Iso.Unfold.mk.noConfusion, `Iso.mk.noConfusion,
  `Iso.Unfold.noConfusionType,

  -- **`ctorIdx` / `ctorElim` / `ctorElimType` / `below` / `brecOn`** — the constructor
  -- index, the constructor eliminator and its type, and the `below`/`brecOn` pair
  -- Lean derives for a *mutually* or *structurally* recursive inductive. Recursion
  -- machinery.
  `Codec.ctorIdx, `Iso.ctorIdx,
  `Codec.Normal.ctorIdx, `Codec.Suffix.ctorIdx, `Iso.Unfold.ctorIdx,
  `Codec.ctorElim, `Codec.ctorElimType,
  `Codec.below, `Codec.brecOn, `Codec.brecOn.go,

  -- **A notation alias.** `Iso.«term_≫_»` is `Infixr "≫" => Iso.trans`; the token is
  -- bound to an existing declaration, and *that* declaration is what has (or lacks) a
  -- law. `Iso.trans` is in `definitionSurfaceAllowlist` with its own reason.
  `Iso.«term_≫_»,
]

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

Each entry is one of four shapes, and the reason is in place at the entry:

* an `Iso` combinator whose correctness is the `law` **structure field**, proved at its
own definition site (so the kernel checks it at construction) and therefore stated by
no separate theorem — the mention proxy cannot see a field proof. (`Iso.prod` left this
group in `codec-audit-round-five` §D2 because a gated law *does* name it;
`Iso.subset`/`Iso.element` left it because their **domain** laws do, since for a
*partial* iso the `law` field is vacuous and the domain is what a caller needs.);
* a **type spelling** (`candsAt`) that exists only so one proof can name a list type
at a spelling the elaborator can match;
* an internal witness or instance (`uniqSeqBt`, `instDecidableEqBytes`, …) that exists
to make another proof go through, not to be a codec a caller uses.

Keep the reason next to the entry: a bare name here would be the dumping ground this
list exists to avoid. -/
def definitionSurfaceAllowlist : Array Name := #[
  -- **`Iso` combinators: correctness is the `law` structure field**, proved at the
  -- definition site (`law := by …`), so the kernel checks it at construction and no
  -- separate theorem names it. The mention proxy cannot see a field proof.
  --
  -- **`Iso.prod` is deliberately NOT here** (`codec-audit-round-five` §D2). It is the
  -- paper's `×`, and `README [S1]` tells the reader its unconditional-iso list is
  -- complete, so a law naming it is the honest resolution: `Iso.prod_apply_eq_some` /
  -- `Iso.prod_unapply_eq_some` are gated. An allowlist reason for the one member of a
  -- list the reader is told is complete would be the dumping ground this docstring
  -- forbids.
  --
  -- **`Iso.subset`/`Iso.element` are NOT here** (`codec-audit-round-five` R6-07/R6-38,
  -- design §D5). They are the two *partial* isos, for which the "correctness is the
  -- `law` field" reason above is **vacuous**: `subset p` is
  -- `if p x then some x else none`, so the `↔` holds by construction whatever `p` is.
  -- What a caller needs is the domain, and it is now stated by a gated theorem that
  -- mentions the constant (`Iso.subset_apply_eq_some_iff`,
  -- `Iso.element_unapply_eq_some_iff`), so the mention proxy reports them as
  -- *mentioned* and an entry here would fail the "already has a gated law" check.
  `Iso.associate,
  `Iso.commute,
  `Iso.id,
  `Iso.inverse,
  `Iso.ofTotal,
  `Iso.optionSome,
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

  -- **A type spelling, not a codec.** `candsAt` names the candidate-list type so that
  -- `search_nil_left` can bind its `[]` candidate at a spelling the elaborator
  -- matches; its whole content is a `List` of subtype, so there is no law to state.
  -- (Its two siblings `candsRoot`/`retypeCands` were **deleted** in
  -- `codec-audit-round-five` R6-11: no theorem and no definition referenced either,
  -- so they were a closed dead island — the "dumping ground" this docstring warns
  -- about, and deletion was the honest fix rather than a longer reason.)
  `Codec.candsAt,

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

Why each entry is not a law. Four groups, each with its own reason in place.

**Read the next sentence before trusting any reason below.** Only *two* of these four
groups carry a **measurement**; the other two are **classifications by name**, and the
register says which is which (`codec-audit-round-eight` §3.4). The distinction is the
whole point of the round-eight finding: this file's own doctrine (§"An empty axiom
footprint is NOT the signature of a restatement") forbids presenting a content claim as
measured, and two of the reasons below were doing exactly that.

* **`inj`, `injEq`, `sizeOf_spec`, `eq_def`** — compiler auxiliaries, established
  **by construction, not by a body sample**: each name is emitted by Lean for every
  `ctorInfo`/`structure mk`/`def` and its shape is fixed by Lean's environment
  extension, not by this library. **Classification, machine-checked at the name
  level only.** `partition` proves such a name is dropped and unreferenced-as-a-law;
  it does not read the body. (History: this group used to add the content claim "each
  restates its own definition", presented as if measured. No body evidence was ever
  recorded, so the claim was withdrawn — see §3.2's note on the group.)
* **`Prop`-valued structure-field projections** — **measured**, by the structural arm
  at the end of this file (`isBareProj`, added in `codec-audit-round-seven` GC-04 for
  completeness and in round eight §2.1 for validity): each entry's *body* is walked
  from the environment and must be a bare `Expr.proj`. That is the strongest check in
  this list, and it is why these entries are the only ones whose reason asserts
  something about content.
* **`congr_simp`** — **measured by sample** (`codec-audit-round-eight` §3.3).
  `Codec.decodeFull.congr_simp` is
  `∀ …, s = s₁ → decodeFull p h n s = decodeFull p₁ … n s₁`: the argument-rewriting
  shape `simp` needs to analyse recursion through a changing argument. **The
  reviewer's alternative was checked and refuted**: this is *not* a genuine congruence
  law — a congruence law *constructs* an equality from a hypothesis (`f a = f b` for a
  given `a = b`), whereas these *transport* equality through positions `simp` cannot
  see directly, which is precisely why the compiler emits them. Nothing in them says
  anything about which bytes a codec accepts.
* **`Codec.findFrom.induct`** — **measured**: the arm above shows
  `Codec.findFrom`'s `termination_by`/structural recursion is what generates it, so it
  is a recursion principle, not a statement about the codec.

`Codec.Nat.eq_irrel` is deliberately **not** here. It is an authored theorem — its
docstring explains the proof-irrelevance role it plays in closing the laws without
`Classical.choice` — so it belongs in the gated set even though its name matches the
`eq_irrel` pattern. The classifier no longer drops it either (`isGeneratedAux` names
it as an authored exception), which is why it is absent from the group above. That is
the shape of every future correction: a law the heuristic misclassifies moves into
the gated set, and the allowlist keeps only what is genuinely not a law. -/
def generatedAuxAllowlist : Array Name := #[
  -- **`Prop`-valued structure-field projections**: part of the type a caller
  -- supplies, not a theorem proved about it.
  --
  -- `Iso.law`, `Codec.Normal.fixed` and `Codec.Normalizer.idem` are `fun … => self.3` /
  -- `self.2` / `self.1` — the same shape as the three `MeasureDecreases*.dec` /
  -- `Unfold.dec` entries below, which this file's prose already described as "not a
  -- theorem proved about it" while gating these three as laws
  -- (`codec-audit-round-five` R6-02, design §D3). Measured: all seven report **no
  -- axioms**, because a projection asserts nothing beyond the type it projects. The
  -- file cannot argue both ways in its own prose, so the two groups are one group.
  -- Note that the *satisfiability* of the `dec` obligations is a law and is gated
  -- (`counterMeasureDecreases` / `counterMeasureDecreasesR`); `Iso.law`'s
  -- satisfiability is `counterIso` / `counterIsoR`, gated for the same reason.
  `Iso.law,
  `Codec.Normal.fixed,
  `Codec.Normalizer.idem,
  `Codec.Suffix.hle,
  `Iso.MeasureDecreases.dec,
  `Iso.MeasureDecreasesR.dec,
  `Iso.Unfold.dec,

  -- **Five more of the same classification, found by the fixed predicate**
  -- (`codec-gate-denominators` §3.4/§3.9). These are *not* `Prop`-valued structure
  -- fields; they are theorems whose **body** selects a field out of something the
  -- caller supplied (`hal.1`, `hal.2.1`, `c.property.1`, `(Iso.law i).1`,
  -- `(Iso.law i).2`). They are here, not in the gated set, because gating them measures
  -- the shape of a hypothesis rather than any behaviour — the same principle as
  -- `propProjections`, reached structurally rather than by a name list.
  --
  -- `Codec.packedCands_mem` is the one worth a second sentence: it *names* a membership
  -- (`c.val ∈ decodeArray d a k`) that callers would otherwise spell out, so it earns
  -- its keep as documentation (§3.6). It still asserts nothing, so it is not a law;
  -- "useful" and "a law" are different questions and the gate asks the second.
  --
  -- `Codec.CandAligned_tail` is deliberately **absent**: its body is
  -- `And.casesOn hal fun hlen hpt => ⟨…, …⟩`, a real proof about an invariant (§3.4).
  `Codec.CandAligned_fst,
  `Codec.CandAligned_at,
  `Codec.packedCands_mem,
  `Iso.apply_eq_some_of_unapply,
  `Iso.unapply_eq_some_of_apply,

  -- **The recursion principle of a `def`** (`findFrom`'s structural recursion).
  `Codec.findFrom.induct,

  -- **`Codec.brecOn.eq` — the compiled-body equation of `def Codec.brecOn`.**
  -- `codec-audit-round-eight` §3.1 rewrote this reason. It used to say this is "the
  -- only authorial theorem in the `Codec`/`Iso` namespaces ending in `eq` (environment
  -- walk)", which stated the *logical* claim (the uniqueness) and never what the
  -- theorem *is*. Measured with `#check`/`#print`: its type is
  -- `brecOn motive t F = F _ t (brecOn.go … motive t F).2` and its body is the
  -- `casesOn` machinery — i.e. the defining equation Lean emits for the `brecOn`
  -- helper, not a theorem anyone wrote. It **is** also the only `Codec`/`Iso` name
  -- ending in `eq` (re-walked: the array is `[Codec.brecOn.eq]`), which is why the
  -- suffix rule can safely carry `"eq"`; that is a fact about the *suffix*, not this
  -- entry's justification. Both statements are true; only the second is a reason.
  `Codec.brecOn.eq,

-- **`inj` — the injectivity equation of a constructor.** Lean emits it for every
-- inductive constructor and structure `mk`: two applications are equal iff their
-- fields are, which the constructor's own typing already gives. It states nothing
-- about which bytes a codec accepts. **Classified by name** (`inj` at the end of a
-- constructor name is Lean's own spelling for this), machine-checked only for
-- existence and for being dropped from the universe — see the register note above.
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
-- about a codec's behaviour. **Classified by name**, not by a body sample; one entry
-- (`Codec.Normal.mk.sizeOf_spec`) was `#print`ed in `codec-audit-round-eight` §3.2 to
-- confirm the shape (`sizeOf (mk …) = 1 + sizeOf raw + sizeOf fixed`), which is a
-- **sample**, not evidence for the other ten. The sample agrees with the
-- classification; the classification is what the gate enforces.
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

-- **`congr_simp` — the `@[congr]` lemma Lean derives** so that `simp` can rewrite
-- under a recursion's argument (well-founded or `partial` definitions). **Measured by
-- sample, not classified** (`codec-audit-round-eight` §3.3): `#print`ed,
-- `Codec.decodeFull.congr_simp` has the shape
-- `s = s₁ → decodeFull p h n s = decodeFull p₁ (cast h) n s₁` — argument transport,
-- not a congruence law *constructing* an equality from a hypothesis. The reviewer
-- suspected this suffix could hide a real congruence law; it cannot, because
-- transport is structurally what `simp` needs here and what the compiler emits.
-- Sample-verified for `Codec.decodeFull`, `Codec.fill`, `Iso.foldl` and
-- `Codec.Normal.mk` — four of sixteen, i.e. a sample and said to be one.
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
-- regenerated automatically whenever the body changes. **Classified by name**, not
-- sampled: the last component `eq_def` is Lean's own spelling, and a name so spelled
-- cannot be an authored law about a codec.
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
  ,`Codec.CandAligned_tail
  ,`Codec.Fin.cast_val
  ,`Codec.Nat.eq_irrel
  ,`Codec.Normal.ext
  ,`Codec.Normal.ext_iff
  ,`Codec.Rab_fails_huniq
  ,`Codec.Rab_fails_huniq_full
  ,`Codec.Rab_four
  ,`Codec.Rab_lengthDet
  ,`Codec.Rab_productive
  ,`Codec.Rab_two
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
  ,`Codec.Suffix_cast_remaining
  ,`Codec.aligned_alignedNotLengthDetWitness
  ,`Codec.altConsumesByte
  ,`Codec.append_toArray_ofFn_concat
  ,`Codec.arrayToBytes_bytesToArray
  ,`Codec.arrayToBytes_bytesToArray_apply
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
  ,`Codec.decodeRepeat_mem_iff_general
  ,`Codec.decodeRepeat_spec
  ,`Codec.decodeSepBy_spec
  ,`Codec.decodeTakeWhile_spec
  ,`Codec.decodeWholeBytes_eq
  ,`Codec.decodeWholeBytes_size
  ,`Codec.decodeWholeBytes_spec
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
  ,`Codec.functional_iff_relFunctional
  ,`Codec.huniq_byte
  ,`Codec.huniq_not_derivable
  ,`Codec.huniq_not_derivable_full
  ,`Codec.isoConsumesByte
  ,`Codec.lengthConst_byte
  ,`Codec.lengthDetWitness_unamb
  ,`Codec.lengthDet_byte
  ,`Codec.lengthDet_not_implied_by_unamb
  ,`Codec.lengthDet_not_implies_relAligned
  ,`Codec.lengthDet_not_implies_relAligned_productive
  ,`Codec.lengthDet_of_lengthConst
  ,`Codec.lengthDet_relUnambAlignedWitness
  ,`Codec.length_packedCands_le
  ,`Codec.lengths_eq_of_const
  ,`Codec.list_ofFn_getElem_clean
  ,`Codec.map_toList_eq_ofFn_none_iff
  ,`Codec.mem_decodeArray_iff
  ,`Codec.mem_map_range_iff
  ,`Codec.mem_packedCands
  ,`Codec.nil_append_size
  ,`Codec.nil_append_toList
  ,`Codec.not_lengthDet_alignedNotLengthDetWitness
  ,`Codec.not_productive_pure
  ,`Codec.ofFn_concat
  ,`Codec.ofFn_shifted
  ,`Codec.packedCand_iff
  ,`Codec.packedCand_of_mem
  ,`Codec.packedCands_aligned
  ,`Codec.packedCands_consumes
  ,`Codec.packedCands_eq_attach
  ,`Codec.packedCands_length_eq
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
  ,`Codec.prod_relUnambAlignedWitness
  ,`Codec.productive_iff_consumesByte
  ,`Codec.pushBytesFrom_eq
  ,`Codec.pushBytes_eq
  ,`Codec.relAligned_byte
  ,`Codec.relAligned_not_implies_lengthDet
  ,`Codec.relChainl1_cast
  ,`Codec.relChainr1_cast
  ,`Codec.relRepeatToCount
  ,`Codec.relRepeat_cast
  ,`Codec.relRepeat_cons
  ,`Codec.relRepeat_cons_eq
  ,`Codec.relRepeat_functional_of_step
  ,`Codec.relRepeat_induction
  ,`Codec.relRepeat_length_of_const
  ,`Codec.relRepeat_nil
  ,`Codec.relRepeat_prefix_inj
  ,`Codec.relRepeat_suffix_inj
  ,`Codec.relRepeat_unbounded_of_empty
  ,`Codec.relRepeat_unique_same_length
  ,`Codec.relSepBy_cast
  ,`Codec.relSepBy_functional
  ,`Codec.relTakeWhile_cast
  ,`Codec.relTakeWhile_functional
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
  ,`Codec.satisfy_sigmaFunctional
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
  ,`Iso.bind_eq_some
  ,`Iso.counterMeasureDecreases
  ,`Iso.counterMeasureDecreasesR
  ,`Iso.dropLast_append_last
  ,`Iso.element_unapply_eq_some_iff
  ,`Iso.foldRec_append
  ,`Iso.ite_some_eq_some
  ,`Iso.map_fst_reverse_eq_some
  ,`Iso.map_swap_eq_none
  ,`Iso.map_swap_eq_some
  ,`Iso.prod_apply_eq_some
  ,`Iso.prod_unapply_eq_some
  ,`Iso.subset_apply_eq_some
  ,`Iso.subset_apply_eq_some_iff
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
  -- **A staleness arm for `exclusions`, ported from `basen`** (`codec-audit-round-seven`
  -- GC-06). The check above *honours* `exclusions` — a listed name is skipped — so a
  -- listed name that no longer exists, or one that was measured clean, was invisible.
  -- `basen` gained this arm in `round-six` §2.4 (R7-17); `codec`, where that fix was
  -- written, did not. Both failures matter: an exclusion is a *measured footprint plus
  -- a reason*, so one that names nothing is an unfalsifiable claim and one on a clean
  -- law is un-gating by silence.
  let mut exclProblems : Array String := #[]
  let pubThms := CodecAxioms.publicTheorems env
  for n in CodecAxioms.exclusions do
    match env.find? n with
    | none =>
      exclProblems := exclProblems.push
        s!"exclusion names a declaration that does not exist (rename or deletion?): {n}"
    | some _ =>
      if !pubThms.contains n then
        exclProblems := exclProblems.push
          s!"exclusion names something that is not a public theorem: {n}"
      else
        let axs ← liftCoreM <| Lean.collectAxioms n
        let clean := axs.all fun a => a == ``propext || a == ``Quot.sound
        if clean then
          exclProblems := exclProblems.push
            s!"exclusion lists {n}, whose measured footprint [{axs.toList.map toString}] is already inside the discipline — remove the exclusion"
  if !unGated.isEmpty || !stale.isEmpty || !exclProblems.isEmpty then
    let mut msg : MessageData := ""
    if !unGated.isEmpty then
      msg := msg ++ m!"theorems not pinned by this gate (regenerate `Axioms.lean`):\n" ++
        m!"{String.join (unGated.toList.map fun n => s!"  {Name.toString n}\n")}"
    if !stale.isEmpty then
      msg := msg ++ m!"pinned names with no matching theorem:\n" ++
        m!"{String.join (stale.toList.map fun n => s!"  {Name.toString n}\n")}"
    if !exclProblems.isEmpty then
      msg := msg ++ m!"exclusion-list defects:\n" ++
        m!"{String.join (exclProblems.toList.map fun s => s!"  {s}\n")}"
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
  -- **`defs.size - allow.size` is correct here, and `mentioned.length` is not.**
  -- A reviewer proposed printing `mentioned.toList.length` "because it measures what
  -- the message names". Measured: that prints **311**, not 115, because
  -- `mentionedByGated` is the set of *every constant used by a gated theorem's type* —
  -- it includes other namespaces and compiler machinery, and is subsequently
  -- intersected with `defs` by the `silent`/`both` filters above. The subtraction is
  -- the count of public defs that are mentioned, and it is *guarded*: the header arm
  -- asserts `defs.size - defAllow == expectedMentioned` **and** `defs.size ==
  -- expectedDefs` separately (see below), so the identity cannot hide a mismatch it
  -- did not cause. Keep the subtraction; do not "fix" it again.
  logInfo m!"axiom gate: {defs.size} public definitions covered, {defs.size - CodecAxioms.definitionSurfaceAllowlist.size} mentioned and {CodecAxioms.definitionSurfaceAllowlist.size} allowlisted (mention proxy)"

/-! **Def-side declination audit**, run on every `lake build` — `codec-audit-round-five`
§1.1, R6-01.

The theorem side has had this since `codec-audit-round-two` (`partition`); the def side
never did. `isDerivedDefName` removes a name from the universe **before** `publicDefs`
is computed, so a dropped `def` and a `def` that was never written are the same thing
to every check above. That is how `Iso.prod` — the paper's own `×`, listed in
`README [S1]`'s unconditional-iso list — sat outside a green gate.

Two failures, each naming what is wrong:

* a public `def` the classifier **drops** and that is in **neither**
  `derivedDefAllowlist` nor (redundantly) the universe — removal from the gate's
  universe must be a recorded decision, exactly as it is for theorems;
* an allowlist entry the classifier does **not** drop — a stale name, or a typo, or an
  attempt to hide a `def` that is actually in the universe.

The classifier's *pattern list* is audited separately by `derivedDefPatternAudit`. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let candidates := CodecAxioms.candidateDefs env
  let droppedAllow := Std.HashSet.ofList CodecAxioms.derivedDefAllowlist.toList
  let dropped := candidates.filter CodecAxioms.isDerivedDefName
  let unexplained := dropped.filter fun n => !droppedAllow.contains n
  let notDropped := CodecAxioms.derivedDefAllowlist.filter fun n =>
    !candidates.contains n || !CodecAxioms.isDerivedDefName n
  if !unexplained.isEmpty || !notDropped.isEmpty then
    let mut msg : MessageData := ""
    if !unexplained.isEmpty then
      msg := msg ++ m!"public definitions dropped from the gate's universe by `isDerivedDefName` with no reason in `derivedDefAllowlist` (removal must be a recorded decision):\n" ++
        m!"{String.join (unexplained.toList.map fun n => s!"  {Name.toString n}\n")}"
    if !notDropped.isEmpty then
      msg := msg ++ m!"`derivedDefAllowlist` entries the classifier does not drop (stale name, or a definition that IS in the universe):\n" ++
        m!"{String.join (notDropped.toList.map fun n => s!"  {Name.toString n}\n")}"
    throwError msg
  -- **The decomposition, not the total** (`codec-gate-denominators` §1.1). This line
  -- used to print `{dropped.size} definitions dropped ... all reason-recorded` — one
  -- number for twelve patterns. That is a *total* whose causes are unaudited: a pattern
  -- removing exactly one declaration and a pattern removing fifteen by design read the
  -- same, and the second clause ("all reason-recorded") describes a different question
  -- than the count does. Both halves are now stated: `removed + kept` against the
  -- candidate universe, then the removals split by the pattern that made them. The
  -- per-pattern count is what makes a one-name pattern visible; the kept half is what
  -- makes the split a *partition* rather than a sample of it.
  let (decomp, kept) := CodecAxioms.derivedDefPatternRemovals env
  let removed := decomp.foldl (fun a x => a + x.2.size) 0
  let singletons := decomp.filter fun x => x.2.size == 1
  let uncounted := (CodecAxioms.candidateDefs env).size - removed - kept.size
  let (expPats, expRemoved, expSingleton, expUncounted) :=
    CodecAxioms.expectedDerivedDefPatternCounts
  let mut drift : Array String := #[]
  if decomp.size != expPats then
    drift := drift.push s!"patterns: constant says {expPats}, decomposition has {decomp.size}"
  if removed != expRemoved then
    drift := drift.push s!"removed: constant says {expRemoved}, environment has {removed}"
  if singletons.size != expSingleton then
    drift := drift.push s!"patterns removing exactly one declaration: constant says {expSingleton}, environment has {singletons.size} ({String.intercalate ", " (singletons.toList.map (·.1))})"
  if uncounted != expUncounted then
    drift := drift.push s!"names in neither half of the decomposition: constant says {expUncounted}, environment has {uncounted}"
  if removed != dropped.size then
    drift := drift.push s!"removed: the decomposition sums to {removed} but `isDerivedDefName` drops {dropped.size} — classifier and decomposition disagree"
  unless drift.isEmpty do
    throwError m!"the def-classifier decomposition is stale (update `expectedDerivedDefPatternCounts` in lockstep with the log line):\n{String.join (drift.toList.map fun s => s!"  {s}\n")}"
  let perPattern := String.intercalate ", " (decomp.toList.map fun (p, ns) => s!"{p} {ns.size}")
  logInfo m!"axiom gate: definitions dropped by the name classifier — {removed} removed + {kept.size} kept = {(CodecAxioms.candidateDefs env).size} candidates, all removals reason-recorded; by pattern ({singletons.size} of {decomp.size} remove exactly one; {uncounted} uncounted): {perPattern}"

/-! **Classifier audit**, run on every `lake build` — `codec-audit-round-five` §1.1's
second arm.

The allowlist above records every *name* the classifier drops. This check audits the
classifier itself, so the pattern list cannot rot into a set of defaults that quietly
removes API:

* a pattern that matches **no** declaration in the environment is a build failure
  naming the pattern — a dead pattern is either a rename or a word nobody should be
  matching on, and either way it is not a default worth keeping silently;
* a pattern whose matched set contains a name that is **not** in
  `derivedDefAllowlist` is a build failure — authorial API removed from the gate with
  no recorded reason;
* a pattern whose matched set contains public surface that a
  `definitionSurfaceAllowlist` reason describes as authored (`Iso` combinator, `Type`
  alias, witness, instance) is a build failure — the classifier and the allowlist must
  not both be describing the same declaration as authorial.

This is the arm that makes `derivedDefPatterns` safe to *shrink*: deleting `rec`,
`mk`, `sizeOf` (R6-37) is only sound because a re-added dead entry now fails here.

**Failure-branch status: none of the four arms in this file (here, `partition`,
`definitionSurfaceCoverage`, `headerNumbers`) is exercised by this tree** — every one is
on its passing path, which is the point of a gate. A maintainer can verify each one is
live by making a deliberate one-line edit (add `"sizeOf"` to `derivedDefPatterns` for
the dead-pattern arm; delete an entry from `derivedDefAllowlist` for the unexplained
arm; change `expectedPub` for the header arm) and confirming `lake build` fails naming
it, then reverting. Recorded as absence of evidence, not as proof the checks are dead. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let candidates := CodecAxioms.candidateDefs env
  let droppedAllow := Std.HashSet.ofList CodecAxioms.derivedDefAllowlist.toList
  let surface := Std.HashSet.ofList CodecAxioms.definitionSurfaceAllowlist.toList
  let mut dead : Array String := #[]
  let mut unexplained : Array Name := #[]
  let mut removesAuthored : Array Name := #[]
  -- **The same decomposition the classifier prints** (`codec-gate-denominators` §1.2).
  -- This loop used to recompute `candidates.filter (getLast! == p)` itself, which is a
  -- second copy of the classifier's rule ("last component equals a pattern") sitting
  -- next to `isDerivedDefName`. One rule, two spellings. `derivedDefPatternRemovals`
  -- is the single list read by the classifier and by every arm that counts it.
  let (decomp, kept) := CodecAxioms.derivedDefPatternRemovals env
  for (p, hits) in decomp do
    if hits.isEmpty then
      dead := dead.push p
    else
      for n in hits do
        if !droppedAllow.contains n then unexplained := unexplained.push n
        if surface.contains n then removesAuthored := removesAuthored.push n
  if !dead.isEmpty || !unexplained.isEmpty || !removesAuthored.isEmpty then
    let mut msg : MessageData := ""
    if !dead.isEmpty then
      msg := msg ++ m!"`derivedDefPatterns` entries that match no definition in the `Codec`/`Iso` namespaces (a dead pattern is not a default — delete it, or record why it stays):\n" ++
        m!"{String.join (dead.toList.map fun p => s!"  {p}\n")}"
    if !unexplained.isEmpty then
      msg := msg ++ m!"names a `derivedDefPatterns` entry removes that are in no `derivedDefAllowlist` entry:\n" ++
        m!"{String.join (unexplained.toList.map fun n => s!"  {Name.toString n}\n")}"
    if !removesAuthored.isEmpty then
      msg := msg ++ m!"names the classifier drops that `definitionSurfaceAllowlist` describes as authorial API (the two lists contradict each other):\n" ++
        m!"{String.join (removesAuthored.toList.map fun n => s!"  {Name.toString n}\n")}"
    throwError msg
  -- **This arm states its denominator, and points at the tuple for the rest**
  -- (`codec-gate-denominators` §1.2). The old line printed
  -- `{derivedDefPatterns.size} def-name patterns` — how many patterns *exist*, which is
  -- the denominator and nothing else, printed as though it were a coverage claim. The
  -- per-pattern counts now belong to §1.1's arm, asserted by
  -- `expectedDerivedDefPatternCounts`; this arm asserts that the list *it* is auditing
  -- is that same list, so the two cannot report about different pattern sets.
  let listed := decomp.foldl (fun a x => a + x.2.size) 0
  let (expPats, expRemoved, _, _) := CodecAxioms.expectedDerivedDefPatternCounts
  let mut drift : Array String := #[]
  if decomp.size != expPats then
    drift := drift.push s!"patterns: constant says {expPats}, walk has {decomp.size}"
  if listed != expRemoved then
    drift := drift.push s!"matched: constant says {expRemoved}, walk matches {listed}"
  if candidates.size != listed + kept.size then
    drift := drift.push s!"matched + kept != candidates ({candidates.size}) — the pattern list does not cover the universe"
  unless drift.isEmpty do
    throwError m!"the def-name pattern audit disagrees with `expectedDerivedDefPatternCounts` (the classifier decomposition this audit is counting is not the one asserted):\n{String.join (drift.toList.map fun s => s!"  {s}\n")}"
  logInfo m!"axiom gate: {decomp.size} def-name patterns enumerated, each matching a recorded non-surface declaration; their per-pattern counts are asserted by the def-classifier arm above ({listed} of {candidates.size} candidates removed)"

/-! **Header check**, run on every `lake build`. The "Current state" tables at the top
of this file are prose, and `partition`/`gateCoverage` compare set *membership* — so a
regeneration leaves them stale silently. It happened: the tables read
`364 / 292` and `197 / 61 / 4 / 30` while the tree was already at
`382 / 310` and `201 / 74 / 4 / 31` (corrected in `9db99b8`). This check makes the
numbers **asserted**: a mismatch fails the build naming both sides. Remember the
figures and the commit are quoted as history; the *current* numbers are the ones this
check prints, never a number written in a file.

Keep these constants in lockstep with the tables above. **This is the settled design,
not a stopgap**: `codec-audit-round-three` §1.9 generated the *footprint distribution*
and deliberately left these *counts* asserted by hand, because the two have different
failure modes — a generated table cannot be stale, while these constants are the
independent second opinion that catches a generator bug. Do not "finish" §1.9 by
computing them. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let pub := CodecAxioms.publicTheorems env
  let gated := gatedNames.length
  let allow := CodecAxioms.generatedAuxAllowlist.size
  -- Lockstep with "Current state" above.
  let expectedPub := 425
  let expectedGated := 342
  let expectedAllow := 83
  let expectedDefs := 140
  let expectedMentioned := 115
  let expectedDefAllow := 25
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

/-! **Constant-kind census**, run on every `lake build` — `codec-audit-round-eight` §1.

The seven `ConstantInfo` constructors are not all in this gate's universe, and until
round eight the file said nothing about the two that are law-*shaped*: `publicTheorems`
and `candidateDefs` both match only `.thmInfo _ | .defnInfo _`, so an `opaque` — the
standard way to publish a value without a body — was matched by **no arm**, and
`exclusions` refuses one outright ("it is not a public theorem"), so it could not even
be recorded as an exclusion.

The `inductInfo` / `ctorInfo` / `recInfo` / `quotInfo` counts move when a structure or
inductive is added, so they are **printed, not asserted** — asserting them would make
the gate fire on unrelated edits and teach a maintainer to bump a constant without
reading it. Assert only what is a *decision*: `opaqueInfo` and `axiomInfo` must be
zero, unless an entry in `constantKindExceptions` records why one exists.

This is the "print the denominator" discipline applied to the universe itself: the arm
reports every kind it looked at, so a narrowed walk is visible in the log.

**Mutation-tested through the census's own predicate, not by planting a scratch
`opaque` in this file.** A `run_cmd` sees only declarations that precede it (measured:
`getEnv` inside a `run_cmd` placed above `namespace Codec opaque scratchThing` does not
see the `opaque`), so planting one here would have to live *above* the arm — which
would change the counts the arms above pin for the rest of the build, i.e. it would
break the tree to test it. What was measured instead: the same walk run as a probe
reports `opaqueInfo: 0` on the clean tree and `opaqueInfo: 1` with one `opaque` in
`namespace Codec`, so the number is a measurement rather than a constant. And the
arm's failure branch is exercised *live* by §2.3 (see `propProjections`) — this file
does have one mutation on the record. -/
def constantKindExceptions : Std.HashMap Name Nat :=
  Id.run do
    let mut m : Std.HashMap Name Nat := {}
    m := m.insert `opaque 0
    m := m.insert `axiom 0
    return m

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut thms : Nat := 0
  let mut defs' : Nat := 0
  let mut opaqueCount : Nat := 0
  let mut axioms : Nat := 0
  let mut machinery : Nat := 0
  for (nm, ci) in env.constants.toList do
    if (`Codec).isPrefixOf nm || (`Iso).isPrefixOf nm then
      match ci with
      | .thmInfo _ => thms := thms + 1
      | .defnInfo _ => defs' := defs' + 1
      | .opaqueInfo _ => opaqueCount := opaqueCount + 1
      | .axiomInfo _ => axioms := axioms + 1
      | .inductInfo _ | .ctorInfo _ | .recInfo _ | .quotInfo _ => machinery := machinery + 1
  let mut bad : Array String := #[]
  -- The two law-shaped kinds that have no proof body to footprint-check. A non-zero
  -- count is not "a stale table": it is a constant every arm is blind to. Fail and
  -- make the author either give it an arm or record it in `constantKindExceptions`.
  if CodecAxioms.constantKindExceptions.getD `opaque 0 != opaqueCount then
    bad := bad.push s!"{opaqueCount} `opaque` public constant(s) in the `Codec`/`Iso` namespaces, {CodecAxioms.constantKindExceptions.getD `opaque 0} recorded — no arm of this gate can footprint-check an `opaque`"
  if CodecAxioms.constantKindExceptions.getD `axiom 0 != axioms then
    bad := bad.push s!"{axioms} `axiom` public constant(s) in the `Codec`/`Iso` namespaces, {CodecAxioms.constantKindExceptions.getD `axiom 0} recorded — an `axiom` is a claim with no proof, so no arm can check it"
  if !bad.isEmpty then
    throwError m!"the gate's universe has a hole — a constant kind it does not walk and does not count:\n{String.join (bad.toList.map fun s => s!"  {s}\n")}"
  logInfo m!"axiom gate: constant kinds — thm {thms} (gated + allowlisted), def {defs'} (mention proxy), opaque {opaqueCount} / axiom {axioms} (no arm, must be 0), induct/ctor/rec/quot {machinery} (machinery, not walked)"

/-- True when `seg` backticks a declaration that exists and is not `selfName`.
The attribution rule for the stated-footprint check: a docstring that names another
declaration is not claiming its own footprint.

A docstring names declarations **short**, without their namespace (`relUnambiguous S`,
`lengthDet_byte`), so the lookup tries the bare name, then the enclosing namespaces.
The namespace prefix of the declaration being checked is the first thing tried, which
is what resolves `lengthDet_relUnambAlignedWitness` inside `Codec`. -/
def namesAnotherDecl (env : Environment) (selfName : String) (ns : Name) (seg : String) : Bool :=
  -- **A backticked footprint is not a declaration name.** `` `[propext,
  -- Quot.sound]`-only `` puts the footprint in backticks, so a naive backtick scan
  -- reads it as a name and the claim gets attributed away from its own declaration.
  -- Strip the two footprint spellings first; this is why the arm must be
  -- non-vacuity-tested by inserting a false claim, not only run on a clean tree.
  let seg := seg.replace "`[propext, Quot.sound]`" "FP_BOTH"
                 |>.replace "`[propext]`" "FP_PROPEXT"
  let resolves (s : String) : Bool :=
    let n := s.toName
    (env.find? n).isSome || (env.find? (ns ++ n)).isSome ||
      (env.find? (`Codec ++ n)).isSome
  ((String.splitOn seg "`").zipIdx.filterMap fun (p, i) =>
    if i % 2 == 1 then some p else none).any fun s =>
      s != selfName && resolves s

/-- True when the **nearest** backticked declaration name before the footprint claim
in `seg` is `selfName`.

This is the attribution rule's second half, and it is a *proximity* rule rather than a
"does self appear anywhere" rule. Two shapes have to be told apart:

* `Codec.Bytes.ext_iff` — "provable by `funext` (left) and `congrFun` (right), both
  `[propext, Quot.sound]`-only": the segment names other declarations, but none of them
  is the claim's subject; the claim is the docstring's own. Proximity finds no
  declaration name between the claim and the start of the segment, so it is self's.
* `Codec.RelAligned` — "`relUnambiguous S` holds (`[propext]`-only:
  `relUnambAlignedWitness_unamb`)": the nearest name is a **different** theorem, and the
  claim is about *it*. A "self appears somewhere" rule would grab this one and report
  `RelAligned` as mis-claiming, which is a false positive.

So the rule is positional: split the segment at the claim marker, take the last
backticked, resolvable declaration name in the **prefix**, and attribute the claim to
it; if the prefix holds no such name, the claim is the docstring's own. -/
def namesSelf (env : Environment) (selfName : String) (ns : Name) (seg : String) : Bool :=
  let seg := seg.replace "`[propext, Quot.sound]`" "FP_BOTH"
                 |>.replace "`[propext]`" "FP_PROPEXT"
  -- The claim marker's position: the first backticked footprint spelling.
  let marks := ["FP_BOTH", "FP_PROPEXT", "axiom-free", "Axiom-free",
                "no axioms at all", "No axioms at all"]
  -- Locate the earliest marker by splitting on it: the head's length is its offset.
  -- (`String.find?` yields a `Pos` whose projection is not stable across toolchains.)
  let cut := marks.foldl (fun acc m =>
    match String.splitOn seg m with
    | [_] => acc
    | h :: _ => Nat.min acc h.length
    | [] => acc) (seg.length)
  let before := String.ofList (seg.toList.take (Nat.min cut seg.length))
  -- `String.trim` does not exist in this toolchain; strip with the explicit helper.
  let isSp (c : Char) : Bool := c == ' ' || c == '\t' || c == '\r' || c == '\n'
  let rec dropL (cs : List Char) : List Char :=
    match cs with
    | c :: r => if isSp c then dropL r else cs
    | [] => []
  let rec dropT (cs : List Char) : List Char := (dropL cs.reverse).reverse
  let stripCh (x : String) : String := String.ofList (dropT (dropL x.toList))
  -- Backticked tokens in the prefix, last-first.
  let toks := ((String.splitOn before "`").zipIdx.filterMap fun (p, i) =>
    if i % 2 == 1 then some (stripCh p) else none).filter fun p =>
      p != "FP_BOTH" && p != "FP_PROPEXT"
  -- **A token is a *declaration name candidate* only if it looks like one**: a single
  -- identifier (optionally dotted), no spaces, no arrow, no operator glyphs. Round
  -- eight found that taking the last *resolving* token instead silently discarded real
  -- claims: `Codec.Bytes.ext_iff`'s says "provable by `funext` (left) and `congrFun`
  -- (right), both `[propext, Quot.sound]`-only", and because `funext` resolves the
  -- claim was attributed away from the theorem it was written about. The same held for
  -- `Codec.byteSlice_spec`. So: keep scanning leftwards past tokens that are not name
  -- candidates, and attribute away only when a genuine *other* declaration is the
  -- nearest name.
  let isIdentChar (c : Char) : Bool :=
    c.isAlphanum || c == '_' || c == '.' || c == '\''
  let isNameTok (t : String) : Bool :=
    !t.isEmpty && t.toList.all isIdentChar && !(t.splitOn ".").any (·.isEmpty)
  -- **Self wins if it appears anywhere in the prefix.** Attribute the claim away only
  -- when the prefix names a genuine *other* declaration and **never** names self. The
  -- earlier rule took the nearest resolving name, which mis-fires on a docstring of the
  -- form "provable by `funext` … and `congrFun` …, both `<footprint>`": the nearest
  -- name is `congrFun`, a real declaration, so the claim was attributed away from the
  -- theorem it describes. Two live sites were in exactly that state
  -- (`Codec.Bytes.ext_iff`, `Codec.byteSlice_spec`), both silently unchecked.
  -- **Only a *Codec/Iso theorem* can own a footprint claim.** A token that resolves to
  -- a library lemma (`funext`, `congrFun`, `omega`) or to a `def` is an ingredient, not
  -- a subject: nobody writes "`congrFun` is `[propext]`-only" as a claim about
  -- `congrFun`. Restricting to `thmInfo` in this package's namespaces is what makes
  -- "the segment names another declaration" mean what the rule intends.
  let isOtherTheorem (t : String) : Bool :=
    if !isNameTok t then false
    else
      let n := t.toName
      let cand := [n, ns ++ n, `Codec ++ n, `Iso ++ n]
      cand.any fun c =>
        match env.find? c with
        | some (.thmInfo _) => ((`Codec).isPrefixOf c || (`Iso).isPrefixOf c)
        | _ => false
  let names := toks.filter fun t => isNameTok t && (t.splitOn ".").getLast! == selfName
  if !names.isEmpty then true
  else !(toks.any isOtherTheorem)

/-- The claim-site count the arm asserts, beside its denominator — `codec-audit-round-eight`
N-6. `AGENTS.md` quoted the arm's count as evidence of coverage while nothing asserted
it: `headerNumbers` pins the theorem and definition counts, but the claim-site count was
**printed only**, so a docstring edit could move it and leave the quoted number rotting
behind a green build. That is exactly the "count with no denominator" defect one level
up, and it is fixed the same way: keep the constant in lockstep with the tables, and the
build names both sides when they disagree.

There are three numbers, not one, and they move for **different** reasons:

* `expectedClaimSites` — sites attributed to self and checked. A docstring edit that adds
  or removes a footprint claim moves this, and that is a real change worth noticing.
* `expectedMentioning` — docstrings mentioning any footprint spelling. Moves on the same
  edits, one level coarser; kept because a claim site and its docstring can move apart.
* `expectedLeft` — claim-shaped segments attributed to another declaration or living in a
  `def` docstring (out of scope). The arm's own removal step, counted rather than silent.

Update all three **together with the log line**, and read the log for the current values
rather than trusting these constants. -/
def expectedFootprintCounts : Nat × Nat × Nat × Nat × Nat := (155, 150, 0, 0, 11)

/-- Every spelling the stated-footprint arm treats as **a footprint claim**, as data —
so the arm can report how many docstrings mention one and how many of those it then
attributed to a theorem.

`codec-audit-round-eight` §5. Round eight's lesson was that a check is only as good as
what enters it, and the footprint arm had the same defect the round-seven predicate
bug had: it printed how many claims it **checked** and nothing about how many existed.
Narrowing this list (deleting `"no axioms at all"`, say) would have silently stopped
reading real claims with a green build and an unremarkably smaller log. Hoisting the
vocabulary here, beside the arm that reads it, makes the two counts comparable.

**Matching is case-insensitive for the lower-case phrases and exact for the two
backticked ones** — the arm lowercases the segment before testing the phrase spellings
and keeps the exact test for the markup, which is how the original inline chain
behaved. `-free` is deliberately **not** in the list: the phrase is
"axiom-free", and a bare "-free" would also match "`[propext]`-free", which is not a
claim this gate knows how to adjudicate. -/
def footprintClaimPhrases : Array String := #[
  "axiom-free",
  "no axioms at all",
  "`[propext, Quot.sound]`-only",
  "`[propext]`-only",
  "`[propext] or no axioms",
  -- **`codec-audit-round-nine` §5.3a: the bare forms, without `-only`.** These are the
  -- spellings the tree actually uses most often, and their absence from this list was
  -- the finding: the *claim* of a two-axiom footprint does not become weaker by
  -- omitting the suffix, so a vocabulary that recognised only `-only` was reading a
  -- strict subset of the claims in the tree. Measured at the time of the fix: 22
  -- `thmInfo` docstrings contained a backticked axiom-list literal and only 137 of the
  -- 159 that mention any footprint spelling were recognised; the blind set included
  -- `Codec.blitBytes_spec`, `Codec.Bytes.ext_iff` and `Codec.findByte_spec`. Widening
  -- this list moved `mentioning` 144 → 150, and the newly-read sites held two real
  -- mis-claims (`blitBytes_spec` and `commitRemainder_spec` both stated the two-axiom
  -- footprint and measure empty).
  --
  -- **Why the bare phrase is safe rather than a loosening.** A docstring that names the
  -- literal `[propext, Quot.sound]` in backticks is making an assertion about a
  -- footprint however it is suffixed; the classifier then *checks* that assertion
  -- against `#print axioms`, so a false one fails the build rather than passing
  -- silently. The risk a wider vocabulary carries is adjudicating a claim whose meaning
  -- this gate cannot decide — not reading one it can.
  "`[propext, Quot.sound]`",
  "`[propext]`",
  "`[Quot.sound]`",
  "`[Quot.sound]`-only",
  "`[propext, Classical.choice, Quot.sound]`"
]

/-- True when `phrase` must be matched against the segment **verbatim** rather than
case-insensitively: a backticked literal is code, and lowercasing it would match
`[propext, quot.sound]`, which is not the spelling Lean prints. -/
def isExactPhrase (phrase : String) : Bool := phrase.startsWith "`"

/-- The claim a segment states, or `none`. One definition, read by both the classifier
and the denominator count, so a vocabulary change moves both or neither. -/
def classifyFootprintClaim (seg : String) : Option String := Id.run do
  let low := seg.toLower
  let has (p : String) : Bool :=
    if isExactPhrase p then seg.contains p else low.contains p
  -- **Order matters, longest first**: `[propext, Classical.choice, Quot.sound]` must
  -- be tested before the bare two-name form, or a segment naming the three-axiom
  -- footprint would be read as claiming the two-axiom one and the arm would report a
  -- false overstatement.
  for (phrase, label) in [
      ("axiom-free", "axiom-free"),
      ("no axioms at all", "axiom-free"),
      ("`[propext, Classical.choice, Quot.sound]`", "[propext, Classical.choice, Quot.sound]"),
      ("`[propext, Quot.sound]`-only", "[propext, Quot.sound]-only"),
      ("`[propext]`-only", "[propext]-only"),
      ("`[Quot.sound]`-only", "[Quot.sound]-only"),
      ("`[propext, Quot.sound]`", "[propext, Quot.sound]"),
      ("`[propext]`", "[propext]"),
      ("`[Quot.sound]`", "[Quot.sound]"),
      ("`[propext] or no axioms", "[propext]-or-cleaner")] do
    if has phrase then return some label
  return none

/-- True when `doc` mentions **any** footprint spelling at all — the arm's denominator.
Independent of attribution, of segmentation and of whether the enclosing constant is a
`thmInfo`: it is the question "did this docstring say anything about a footprint",
which is the widest set the arm could ever have looked at. -/
def mentionsFootprint (doc : String) : Bool :=
  footprintClaimPhrases.any fun p =>
    if isExactPhrase p then doc.contains p else doc.toLower.contains p

/-- The backticked spans of `doc`: every odd-indexed piece after splitting on the
backtick. This is how a claim site's *markup* is read, and it is what the vocabulary's
own denominator is built from. -/
def backtickedSpans (doc : String) : List String :=
  (String.splitOn doc "`").zipIdx.filterMap fun (p, i) => if i % 2 == 1 then some p else none

/-- **The vocabulary's independent denominator** — `codec-audit-round-nine` §5.3a.

An axiom list is a *literal*: a backticked span that is `[`…`]` with only axiom-shaped
names inside, or a bare axiom name in backticks. This predicate is deliberately
**broader** than `footprintClaimPhrases` and is written from the syntax of the markup
rather than from the phrase list, because a check that asks "did the vocabulary catch
this" using the vocabulary answers itself. A span matching it is a docstring that
mentions an axiom list *somewhere*, whether or not any phrase recognises the sentence
around it.

It reads a **joined** form of the docstring: the wrapped literals in this tree break
across a newline inside the brackets, and a per-line scan would report them as
unmatched — which is precisely the hole being measured, so the denominator must not
inherit it. -/
def looksLikeAxiomList (doc : String) : Bool :=
  let joined := String.intercalate " " (String.splitOn doc "\n")
  (backtickedSpans joined).any fun s =>
    let s := ((s.splitOn "]").headD s ++ "]").trimAscii.toString
    if s == "Classical.choice" || s == "sorryAx" then true
    else if !(s.startsWith "[") || !(s.endsWith "]") then false
    else
      let inner := (s.drop 1 |>.dropEnd 1).trimAscii.toString
      inner.isEmpty ||
        (inner.splitOn ",").all fun p =>
          (["propext", "Quot.sound", "Classical.choice", "sorryAx"]).contains
            ((p.trimAscii.toString).replace "\n" "" |>.replace " " "")

/-- Docstrings that contain a backticked, axiom-list **shaped** span that is not a
footprint claim — each with its reason in place, because the reconciliation below
otherwise counts them as blind. The list is closed in **both** directions: an entry
must still be in the blind set (or the entry is stale) and every blind docstring must
be here (or a real hole is being counted as an exemption).

Motivation (`codec-audit-round-nine` §5.3a): the placeholder's job is to be an
independent denominator, so it counts *syntax*, and two docstrings state an empty
bracketed list without stating a footprint. Fixing the prose instead would be the
dishonest move — it would make the denominator agree by making the tree quieter, and
the next genuine `[]` claim would then be the one that hid.

The tree's wrapped literals are **not** here: `looksLikeAxiomList` joins the docstring
before scanning, so a claim broken across a newline is matched rather than exempted.
That is the difference between this list and the old hole — the hole was silent. -/
def vocabularyExemptions : Array (Name × String) := #[
  (``Codec.search_nil_left,
   "the bracketed span is `[]` the empty *list* constructor, named in the docstring's own " ++
   "prose about `Suffix.drop` not reducing in goal position — a `Codec` value, not an axiom list"),
  (``Codec.bdrop_consumedAbs_eq,
   "counted BY the vocabulary (the claim is a wrapped literal, which the joined scan " ++
   "reads); listed here only because the broad predicate also sees the `cast` name in the " ++
   "same span, and the two counts are taken over different predicates")
]

/-- The reconciliation the arm asserts: `recognised + blind = mentioningLiteral`, with
`mentioningLiteral` counted by `looksLikeAxiomList` over the same walk, and `blind`
being the docstrings the vocabulary does not read **that are not
`vocabularyExemptions`**. A docstring the broader predicate accepts and the vocabulary
does not is **blind** — not skipped, not out of scope, and invisible, which is the
state §5.3a found 22 of 159 docstrings in.

Update this constant together with `expectedFootprintCounts`; the arm names both sides
when they disagree, so a spelling removed from the vocabulary fails as a **blind**
count rather than as a mystery. Deleting one is the mutation test: remove
`` "`[propext]" `` from `footprintClaimPhrases` and the arm fails naming the docstrings
that spelling was reading. -/
def expectedVocabularyCounts : Nat × Nat × Nat := (140, 0, 142)

/-! **The stated-footprint check**, run on every `lake build` — `codec-audit-round-six`
§1.1, R7-01/R7-02.

The six checks above assert set **counts** and pin **membership**. None of them reads
a docstring. That left the gate's own prose about footprints unaudited, and round
seven found **eleven** docstring sites stating a footprint `#print axioms`
contradicts — in **both** directions (six "Axiom-free" claims that are not, two
"`[propext, Quot.sound]`-only" claims that are axiom-free, and three restatements).
This check closes that class.

**The rule the class teaches, and the reason it is not a syntactic test:** write a
footprint from `#print axioms`, never from inspection. A candidate predictor — "an
axiom-free claim is true only when the statement never reads a `Bytes` component" —
is **false**: 25 axiom-free theorems manipulate `Bytes` directly (`cast_bytes_val`,
`byteSlice_spec`, `Suffix_cast_remaining`, …). The footprint depends on which
tactics a proof uses, not on the types in its statement, so no rule from statement
shape to footprint is sound. Measurement is the only oracle.

**Attribution.** A claim attaches to the declaration whose docstring it is, *unless
the same segment names a different declaration* — because a docstring that surveys
several footprints (`LengthDet` carries the whole four-way table) is not claiming its
own. Segments are split on newlines and sentence boundaries, so one paragraph is not
treated as one sentence. A hedged lower bound — "`[propext]` or no axioms" — is
satisfied by any footprint inside the hedge, and is not an exact-set claim.

Failure modes handled as their own cases:
* an exact claim that does not match the measured set (either direction);
* a hedged claim whose measured set is outside the hedge. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut bad : Array String := #[]
  let mut claims : Nat := 0
  -- **The denominator** (`codec-audit-round-eight` §5). `claims` is how many claim
  -- *sites* the arm read; `mentioning` is how many docstrings in the walked universe
  -- mention a footprint spelling at all, and `scanned` is how many docstrings the arm
  -- was offered. Round eight's finding was that the arm's scope could narrow
  -- invisibly — a narrower vocabulary or a narrower walk would just print a slightly
  -- smaller `claims`. Printed together, the three distinguish "fewer claims exist"
  -- from "fewer claims are read", which is exactly what the round-seven `getPrefix`
  -- bug (139 declarations silently dropped) looked like from the log: nothing.
  let mut mentioning : Nat := 0
  -- The vocabulary's own denominator and its blind set (§5.3a).
  let mut mentioningLiteral : Nat := 0
  let mut blind : Array String := #[]
  -- Blind docstrings carrying a recorded exemption, counted so the exemption list
  -- cannot rot: `exempt` must match its size, or an entry is stale.
  let mut exempt : Nat := 0
  let mut scanned : Nat := 0
  -- **`skipped` is now decomposed by cause** (`codec-gate-denominators` §1.3). It was
  -- one number covering three unrelated removal reasons, which is instance 14 of the
  -- defect class this change exists to close. The three, and why they are different
  -- facts about the gate:
  --
  -- * `skippedOtherTheorem` — a theorem docstring whose claim names a **different**
  --   resolvable declaration (a survey paragraph, a four-way table). Legitimate by
  --   design: the claim is about that declaration and is checked there.
  -- * `skippedNoOwner` — a claim-shaped segment with **no** resolvable declaration name
  --   in its prefix, in a docstring that *somewhere* names another declaration. This is
  --   the bucket that must be **reviewed, not merely counted**: nothing owns the claim,
  --   so nothing checks it, and a single total would hide it inside the survey count.
  -- * `skippedDefDocstring` — a footprint claim in a `def`/`abbrev` docstring. Out of
  --   scope by design (no proof to adjudicate), counted since R8-06.
  let mut skippedOtherTheorem : Nat := 0
  let mut skippedNoOwner : Nat := 0
  let mut skippedDefDocstring : Nat := 0
  -- **The arm's own "found" total**: every site the arm was offered and did not
  -- ignore — a claim-shaped segment in a theorem docstring, or a footprint-mentioning
  -- `def` docstring. `checked + every skip cause = found` is then an identity the run
  -- can check, rather than an arithmetic restatement of the counters.
  let mut found : Nat := 0
  for (nm, ci) in env.constants.toList do
    -- `isPrefixOf`, matching the six arms above — NOT `getPrefix`, which matched only
    -- immediate children. (`codec-audit-round-eight` R8-08 corrects the round-seven
    -- narrative here: that prefix narrowing was **not** what hid
    -- `Codec.Bytes.ext_iff` — that theorem is an *immediate* child of `Codec`, so its
    -- `getPrefix` was already `Codec` and the prefix filter never removed it. What
    -- hid it was the **attribution** rule, fixed in the same commit. Two defects, one
    -- commit; the prefix one's own casualty count is still unmeasured.)
    --
    -- **The filters live in the `thmInfo` arm, not in this `if`** (`codec-audit-round-eight`
    -- R8-05). `ConstantInfo.isPartial` is `defnInfo.isPartial`, so it is `false` for
    -- every theorem: `&& !ci.isPartial` here removed nothing while reading as a guard,
    -- and the `match` below is what actually selects theorems. One filter, not a
    -- filter plus a match shaped to contradict it.
    --
    -- **`thmInfo` only.** A `def`/`abbrev` has no proof, so a footprint claim in its
    -- docstring describes its *unfolders* or its callers, not itself — `PackedCand`'s
    -- says "the spelling that keeps both `decreasing_by` and the unfolders
    -- `[propext, Quot.sound]`-only", which has no proof to adjudicate. Those docstrings
    -- are counted as `skipped`, not silently ignored.
    if (`Codec).isPrefixOf nm || (`Iso).isPrefixOf nm then
      match ci with
      | .thmInfo _ => if ci.isUnsafe then pure () else
        scanned := scanned + 1
        let some doc ← Lean.findDocString? env nm | pure ()
        if CodecAxioms.mentionsFootprint doc then mentioning := mentioning + 1
        -- **The vocabulary's own denominator** (§5.3a): the broader, independently
        -- written predicate, and the docstrings it accepts that the vocabulary does
        -- not. Both accumulate on the same walk, so they cannot drift apart.
        if CodecAxioms.looksLikeAxiomList doc then
          mentioningLiteral := mentioningLiteral + 1
          unless CodecAxioms.mentionsFootprint doc do
            if CodecAxioms.vocabularyExemptions.any (fun (n, _) => n == nm) then
              exempt := exempt + 1
            else
              blind := blind.push s!"{nm}"
        let selfName := nm.components.getLast!.toString
        let ns := nm.getPrefix
        let footprint ← liftCoreM <| Lean.collectAxioms nm
        let fp := footprint.toList.map toString
        let isFree := fp.isEmpty
        let isPropextOnly := fp == ["propext"]
        let isBothOnly := fp == ["propext", "Quot.sound"]
        let isQuotOnly := fp == ["Quot.sound"]
        -- The footprint no law in this package may have: it is what the gate exists
        -- to forbid, so a docstring stating it is stating a *defect*, and the arm must
        -- still adjudicate the claim rather than quietly pass it.
        let isChoiceFootprint := fp == ["propext", "Classical.choice", "Quot.sound"]
        -- Segments: newlines and sentence breaks, so a paragraph is not one
        -- sentence.
        let lines := String.splitOn doc "\n"
        let segs := lines.flatMap (String.splitOn · ". ")
        -- **Paragraphs by offset, not by `String.contains`** (`codec-audit-round-eight`
        -- R8-04). The old lookup was
        -- `(paras.filter (·.contains seg.trim)).head?`, which has two failure modes:
        -- an empty fragment matches **every** paragraph (`q.contains ""` is `true`),
        -- so `head?` hands back the docstring's *first* paragraph and the survey test
        -- runs against the wrong window; and a fragment occurring in two paragraphs
        -- picks the earlier one. Offsets are what the segment actually has.
        let paras := String.splitOn doc "\n\n"
        -- `(paragraph start offset, paragraph)` in `doc` order.
        let mut paraStarts : Array (Nat × String) := #[]
        let mut off : Nat := 0
        for q in paras do
          paraStarts := paraStarts.push (off, q)
          off := off + q.length + 2
        -- Locate each segment in `doc` in sequence: segments come from `lines` in
        -- order, so a running cursor is enough and cannot mis-pair a repeat.
        let mut cursor : Nat := 0
        for seg in segs do
          let segStart :=
            match String.splitOn (String.ofList (doc.toList.drop cursor)) seg with
            | [h, _] => cursor + h.length
            | _ => cursor
          cursor := segStart
          -- The paragraph **containing** this offset: the last one that starts at or
          -- before it.
          let para := paraStarts.foldl (fun acc (o, q) => if o <= segStart then some q else acc) none
          -- Attribute away when this segment, **or the paragraph it sits in**,
          -- names a different declaration. A survey paragraph (`LengthDet` and
          -- `RelAligned` carry the whole four-way table) states other theorems'
          -- footprints; a claim split from its theorem's name by a sentence break
          -- still belongs to that theorem's line, so the paragraph is the window.
          let namesOther :=
            CodecAxioms.namesAnotherDecl env selfName ns seg ||
            para.any fun q => CodecAxioms.namesAnotherDecl env selfName ns q
          let namesOwn := CodecAxioms.namesSelf env selfName ns seg
          -- **A segment with no footprint claim is not a skipped claim.** The
          -- attribution test runs before the vocabulary test, so without this guard
          -- every ordinary sentence of every docstring would be counted as "attributed
          -- away" — measured at **253** on the first run of this arm, which is the
          -- exact defect the arm exists to prevent: a number nobody can interpret.
          -- The order is: does this segment state a claim at all, then is a claim read.
          if (CodecAxioms.classifyFootprintClaim seg).isNone then continue
          -- `namesOwn` is the proximity rule: the claim belongs to whoever the
          -- segment names *nearest*, and a segment naming nobody is self's own.
          -- `namesOther` (the paragraph-level survey test) still excludes a
          -- docstring that tabulates several footprints without stating its own.
          found := found + 1
          if !namesOwn && namesOther then
            -- **Which cause?** Both arms of this `if` are "attributed away", and they
            -- are not the same fact. `namesAnotherDecl` on the **segment** means a
            -- named declaration owns the claim. When only the **paragraph** matches
            -- (`para` arm), the claim's own prefix names nothing resolvable and the
            -- attribution came from somewhere else in the paragraph — that is the
            -- no-owner bucket, and it is the one a reader has to look at.
            if CodecAxioms.namesAnotherDecl env selfName ns seg then
              skippedOtherTheorem := skippedOtherTheorem + 1
            else
              skippedNoOwner := skippedNoOwner + 1
            continue
          -- **One vocabulary, read here and by the denominator above**
          -- (`footprintClaimPhrases` / `classifyFootprintClaim`). The classifier used
          -- to be inline in this loop, which is how a narrowed vocabulary could stop
          -- reading claims without moving a single printed number.
          let some claim := CodecAxioms.classifyFootprintClaim seg | continue
          claims := claims + 1
          let measured := if isFree then "axiom-free"
            else "[" ++ String.intercalate ", " fp ++ "]"
          -- Every label the vocabulary can produce has an arm here, and the
          -- `_ => true` fallthrough that remains is reached only by a label no
          -- vocabulary phrase emits — so it is a compile-time-shaped guard, not a
          -- silent pass. `codec-audit-round-nine` §5.3a added five labels and this
          -- match is where an unhandled one would have gone green.
          let ok := match claim with
            | "axiom-free" => isFree
            | "[propext, Quot.sound]-only" => isBothOnly
            | "[propext, Quot.sound]" => isBothOnly
            | "[propext]-only" => isPropextOnly
            | "[propext]" => isPropextOnly
            | "[Quot.sound]-only" => isQuotOnly
            | "[Quot.sound]" => isQuotOnly
            | "[propext, Classical.choice, Quot.sound]" => isChoiceFootprint
            | "[propext]-or-cleaner" => isFree || isPropextOnly
            | _ => true
          unless ok do
            bad := bad.push s!"  {nm}: says {claim}, measured {measured}\n"
      | _ =>
        -- **Out of scope, but counted** (`codec-audit-round-eight` R8-06): a `def`
        -- docstring can mention a footprint, and the `thmInfo` filter above drops it.
        -- Dropping it is right (there is no proof to adjudicate); dropping it
        -- *silently* is what makes `claims` indistinguishable from "claims of 200".
        -- Counted as its **own** cause (`codec-gate-denominators` §1.3), because a
        -- claim with no proof and a claim with no owner are different facts.
        if let some doc ← Lean.findDocString? env nm then
          if CodecAxioms.mentionsFootprint doc then
            skippedDefDocstring := skippedDefDocstring + 1
            -- Counted in `found` too: it is a claim site the arm was offered and did
            -- not check, which is exactly what the identity below reconciles.
            found := found + 1
  unless bad.isEmpty do
    throwError m!"stated footprints disagree with the environment ({bad.size} claim site(s)). Write the footprint from `#print axioms`, never from inspection:\n{String.join bad.toList}"
  -- **The count is asserted, not just printed** (`codec-audit-round-eight` N-6), the way
  -- `headerNumbers` asserts the theorem and definition counts. Without this the numbers
  -- `AGENTS.md` quotes as the arm's evidence of coverage could move under a green build.
  -- **Every cause of a skip is asserted separately** (`codec-gate-denominators` §1.3):
  -- the old single `skipped` constant could not be told apart from a change in which
  -- "attributed away" was doing the attributing.
  let (expectClaims, expectMentioning, expectOther, expectNoOwner, expectDefDoc) :=
    CodecAxioms.expectedFootprintCounts
  let mut drift : Array String := #[]
  if claims != expectClaims then
    drift := drift.push s!"claim sites: constant says {expectClaims}, environment has {claims}"
  if mentioning != expectMentioning then
    drift := drift.push s!"docstrings mentioning a footprint: constant says {expectMentioning}, environment has {mentioning}"
  if skippedOtherTheorem != expectOther then
    drift := drift.push s!"claim sites attributed to a named other theorem: constant says {expectOther}, environment has {skippedOtherTheorem}"
  if skippedNoOwner != expectNoOwner then
    drift := drift.push s!"claim sites with NO resolvable owner (review each one): constant says {expectNoOwner}, environment has {skippedNoOwner}"
  if skippedDefDocstring != expectDefDoc then
    drift := drift.push s!"footprint-mentioning `def` docstrings (out of scope): constant says {expectDefDoc}, environment has {skippedDefDocstring}"
  unless drift.isEmpty do
    throwError m!"the stated-footprint counts are stale (update `expectedFootprintCounts` in lockstep with the log line):\n{String.join (drift.toList.map fun s => s!"  {s}\n")}"
  -- **The vocabulary's completeness is asserted too** (`codec-audit-round-nine` §5.3a).
  -- This is the third quantity the arm obligation asks for: a matcher's vocabulary is
  -- an input filter of its own, so it needs its own denominator — counted here by
  -- `looksLikeAxiomList`, which is written from the markup's syntax and does not read
  -- `footprintClaimPhrases`. Without this, the *only* evidence that the phrase list is
  -- complete was that nobody had looked, and 22 of 159 docstrings mentioning an axiom
  -- list were invisible behind a green build.
  let (expectRecognised, expectBlind, expectLiteral) := CodecAxioms.expectedVocabularyCounts
  let recognised := mentioningLiteral - blind.size - exempt
  let mut vdrift : Array String := #[]
  if recognised != expectRecognised then
    vdrift := vdrift.push s!"docstrings whose axiom-list literal the vocabulary recognises: constant says {expectRecognised}, environment has {recognised}"
  if blind.size != expectBlind then
    vdrift := vdrift.push s!"BLIND docstrings (a literal the vocabulary cannot see; each one is read by NOTHING): constant says {expectBlind}, environment has {blind.size}{if blind.isEmpty then "" else " — " ++ String.join (blind.toList.map toString)}"
  if mentioningLiteral != expectLiteral then
    vdrift := vdrift.push s!"docstrings containing a backticked axiom-list literal at all: constant says {expectLiteral}, environment has {mentioningLiteral}"
  -- The reconciliation is an identity, not three independent constants: the broad count
  -- decomposes into what was read and what was not, so a cause that stops being counted
  -- shows up here rather than as three numbers that happen to agree.
  if recognised + blind.size + exempt != mentioningLiteral then
    vdrift := vdrift.push s!"the vocabulary's decomposition does not reconstruct its denominator: {recognised} recognised + {blind.size} blind + {exempt} exempt != {mentioningLiteral} containing a literal"
  -- **The exemption list is audited in both directions** — the round-eight rule for
  -- every name list, applied to this one: a stale entry (naming a docstring that is no
  -- longer blind, or no longer exists) is a silently un-checked claim.
  if exempt != CodecAxioms.vocabularyExemptions.size then
    vdrift := vdrift.push s!"vocabulary exemptions: the list has {CodecAxioms.vocabularyExemptions.size} entr(ies) but the walk matched {exempt}; a stale entry exempts nothing, which is a claim nobody checks"
  unless vdrift.isEmpty do
    throwError m!"the footprint vocabulary is not reconciled with the tree (update `expectedVocabularyCounts` in lockstep with the log line; a BLIND entry must be FIXED in the docstring or recognised by `footprintClaimPhrases`, never added to a count):\n{String.join (vdrift.toList.map fun s => s!"  {s}\n")}"
  -- **The identity the decomposition must satisfy.** `checked + every cause = found`,
  -- asserted rather than left to arithmetic: a cause that silently stops being counted
  -- (a `continue` before the bucketing, say) shows up here, not as a smaller log line.
  let skipped := skippedOtherTheorem + skippedNoOwner + skippedDefDocstring
  if claims + skipped != found then
    throwError m!"the stated-footprint arm's removal causes do not reconstruct its claim sites: {claims} checked + {skipped} skipped ({skippedOtherTheorem} other-theorem + {skippedNoOwner} no-owner + {skippedDefDocstring} `def`-docstring bucket) != {found} found. A cause has stopped being counted."
  -- **Print every number, with the asserted ones named.** `mentioning` is the
  -- denominator: how many docstrings in the walked universe mention a footprint at all.
  -- `claims` is how many sites survived segmentation **and** attribution. `scanned` is
  -- how many `thmInfo` docstrings were offered. A narrowing of the predicate
  -- (`isPrefixOf` → `getPrefix`) shows up as `scanned` collapsing; a narrowing of the
  -- vocabulary shows up as `mentioning` and `claims` dropping while `scanned` holds. The
  -- skips are printed decomposed by cause, so "no claim is unowned" is a readable fact
  -- (`0 no-owner`) rather than an inference from a single total.
  logInfo m!"axiom gate: stated footprints verified ({scanned} theorem docstrings scanned, {mentioning} mention a footprint spelling; {claims + skipped} claim site(s) found = {claims} checked + {skipped} skipped as {skippedOtherTheorem} other-theorem + {skippedNoOwner} no-owner + {skippedDefDocstring} `def`-docstring. Asserted: {claims} checked, {mentioning} mentioning, and all three skip causes; printed-only: {scanned} scanned, {claims + skipped} found. A narrowed vocabulary moves `mentioning`; a narrowed walk moves `scanned`; and `{mentioningLiteral}` docstrings contain a backticked axiom-list literal at all — `{recognised}` recognised + `{blind.size}` blind + `{exempt}` exempt, asserted separately so the vocabulary itself has a denominator)"

/-! **`propProjections` completeness check** — `codec-audit-round-seven` GC-04, the
structural fix for GC-02.

`propProjections` is a *name list*, and it was audited only in the dead-entry
direction (`partition`'s `notDropped`). Nothing asserted the other direction — that
the list covers every `Prop`-valued structure-field projection that exists — so a
**seventh** such projection sat on the kept side and was gated as a law while its six
siblings were allowlisted: `Codec.Suffix.hle`, whose value is `fun … => self.2`,
reports no axioms, and asserts nothing beyond the type the caller supplied. The file's
own prose said "all six are classified the same way"; there were seven.

This is round five's lesson one level up. `isDerivedDefName` removed names from the
universe *before* any check could see them; a **name list** has the same shape — a
`Prop` field whose name nobody added is invisible to a check that reads the list. So
this arm does not read the list's contents as the claim: it walks the environment and
asks, structurally, which public theorems *are* bare projections, then requires each
to be in `propProjections`. A new `Prop` field is now a build failure rather than a
new law.

**The `isGeneratedAux` disjunct in the predicate below is an exemption this arm does not
record** (`codec-audit-round-eight` N-2): a bare projection whose last component matches
the suffix rule (`dec`, …) is exempt here. That is benign rather than a hole, because
those names are still forced into `generatedAuxAllowlist` **with a prose reason** by
`partition`, which is the arm that audits them. Recorded so the next reader does not
have to work out which of the two arms owns the reason. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  -- **One definition, read by both arms** (`codec-gate-denominators` §2.2). The
  -- `let rec` that sat here was one of two copies five hundred lines apart, under a
  -- comment claiming they were one. `CodecAxioms.isBareProj` replaces both, so the
  -- comment is now backed by their sharing it, not by the sentence asserting it.
  let isBareProj := CodecAxioms.isBareProj env
  let mut unlisted : Array Name := #[]
  for (nm, ci) in env.constants.toList do
    if ((`Codec).isPrefixOf nm || (`Iso).isPrefixOf nm) && !ci.isUnsafe && !ci.isPartial then
      match ci with
      | .thmInfo ti =>
        -- A projection is a law-shaped claim on nothing, so it must be *dropped* from
        -- the universe — either by the name list or by the suffix rule (`dec`, …).
        -- Anything that is neither is gated as a law, which is the defect.
        if !isPrivateName nm && !nm.isInternalDetail && isBareProj ti.value then
          unless CodecAxioms.propProjections.contains nm ||
                 CodecAxioms.isGeneratedAux nm do
            unlisted := unlisted.push nm
      | _ => pure ()
  unless unlisted.isEmpty do
    throwError m!"theorems whose body is a bare structure-field projection but which are NOT in `propProjections` (a projection is not a law; allowlist it with the group's reason):\n{String.join (unlisted.toList.map fun n => s!"  {n}\n")}"
  logInfo m!"axiom gate: propProjections covers every bare projection ({CodecAxioms.propProjections.size} listed)"

/-! ### The other direction: *validity* of `propProjections`

`codec-audit-round-eight` §2. The arm above is symmetric in name only — it asserts
that **every bare projection is listed**, which is the *completeness* direction. The
*validity* direction (every **listed** name is a bare projection) had no arm, while
`propProjections`' docstring said a name "that is not actually a structure-field
projection would fail" and that the list is "the same kind of data as
`derivedDefPatterns`", i.e. audited both ways. `derivedDefPatterns` does have both
(`derivedDefPatternAudit`); this list had one. The sentence was false about the
mechanism.

Why it matters even though all four current entries are genuine projections: a
non-projection added to the list is **removed from the gated universe** by
`isGeneratedAux` and then accepted by `partition` as an allowlisted not-a-law, so a
real theorem would stop being footprint-checked with no build failure anywhere. That
is the same shape as round five's `Iso.prod` (`a name list removes a name before any
check can see it`), one level up.

The reviewer's escalation — "adding `Codec.roundtrip` to `propProjections` makes it
invisible to **every** arm" — is **refuted as stated**. Measured: the "in NEITHER"
arm and the `headerNumbers` arm both fire, because the removal changes the partition
count. The narrow true statement is the one this arm enforces: the list silently
*accepts* a name that is not a projection, and until now nothing said so in the
failure that names the offending entry.

**What `isBareProj` does and does not recognise, recorded because the predicate is the
weakest step here** (`codec-audit-round-eight` R8-09). It matches a projection under a
spine of `lam`/`mdata`/`app`, so:

* it flags `fun (x : α × β) => x.1` — a projection of an *argument* — as a bare
  projection. That is a **false positive in the safe direction**: the name is demanded
  in `propProjections` and a human then decides.
* it does **not** see a *wrapped* projection of the structure, `fun self => id self.law`
  or `fun self => (self.law)`. Such a body would be gated as a law while asserting
  nothing. **Measured: zero such theorems exist** (a walk for projections under `id` /
  parentheses finds none, and the 19 theorems whose bodies *contain* a projection
  without being one are all `eq_def`/`eq` machinery plus `Codec.decodeFull_some`, whose
  projection is on a destructed pair). So the hole is **latent, not live** — stated
  here rather than fixed, because tightening the predicate to demand that the projection
  be rooted at the *last* binder is a change to the *completeness* arm's definition of
  "is a projection", and that is a separate decision from making this list valid.

Both directions print their counts (`4 listed of 7 found`, plus the `dec`-suffixed
three), so a drift between the list and the environment is readable in the log and not
only in a partition failure. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  -- The same predicate the completeness arm uses — now literally the same
  -- definition (`codec-gate-denominators` §2.2), not a second copy a comment calls one.
  let isBareProj := CodecAxioms.isBareProj env
  let mut notProj : Array String := #[]
  let mut found : Nat := 0
  -- Count the walk's own view of the set, so the two sides of the claim are
  -- comparable (`codec-audit-round-eight` R8-09(iii)): a shrinking list against a
  -- constant `found` is visible in the log, not only in a partition failure.
  for (nm, ci) in env.constants.toList do
    if ((`Codec).isPrefixOf nm || (`Iso).isPrefixOf nm) && !ci.isUnsafe then
      match ci with
      | .thmInfo ti =>
        -- **Every bare projection in the namespace**, before either exclusion — the
        -- widest set, so the printed pair is `4 listed` of `7 found` and the
        -- decomposition is stated in the log rather than inferred. The extra three
        -- are `MeasureDecreases.dec`, `MeasureDecreasesR.dec`, `Unfold.dec`, which
        -- are bare projections classified by the `dec` *suffix* rather than by this
        -- list; the completeness arm's predicate is `listed ∨ suffix`, so it is
        -- satisfied by construction. Printing `0` here (the narrow reading, applying
        -- `isGeneratedAux`) would be a number nobody can interpret — the defect this
        -- whole round is about.
        if !isPrivateName nm && !nm.isInternalDetail && isBareProj ti.value then
          found := found + 1
      | _ => pure ()
  for n in CodecAxioms.propProjections do
    match env.find? n with
    | none =>
      notProj := notProj.push s!"  {n}: does not exist (a stale name here removes nothing and hides a typo)\n"
    | some ci =>
      match ci with
      | .thmInfo ti =>
        unless isBareProj ti.value do
          notProj := notProj.push s!"  {n}: its body is not a bare structure-field projection — listing it REMOVES a real theorem from the gated universe\n"
      | _ =>
        notProj := notProj.push s!"  {n}: not a theorem at all, so it cannot be a projection\n"
  unless notProj.isEmpty do
    throwError m!"`propProjections` entries that are not `Prop`-valued structure-field projections. A name here is dropped from the gate, so an entry that is not a projection un-gates a law:\n{String.join notProj.toList}"
  -- **Both sides printed.** `found` is what the environment walk sees; the list size
  -- is what the gate claims. They must be equal (the completeness arm enforces that),
  -- and printing both is what makes a divergence readable in the log.
  logInfo m!"axiom gate: propProjections entries are all bare projections ({CodecAxioms.propProjections.size} listed of {found} bare projections in the namespaces; the rest are the `dec`-suffixed three, classified by suffix)"

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
/-- info: 'Codec.Rab_fails_huniq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.Rab_fails_huniq
/-- info: 'Codec.Rab_fails_huniq_full' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.Rab_fails_huniq_full
/-- info: 'Codec.Rab_four' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.Rab_four
/-- info: 'Codec.Rab_lengthDet' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.Rab_lengthDet
/-- info: 'Codec.Rab_productive' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.Rab_productive
/-- info: 'Codec.Rab_two' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.Rab_two
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
/-- info: 'Codec.Suffix_cast_remaining' does not depend on any axioms -/
#guard_msgs in
#print axioms Codec.Suffix_cast_remaining
/-- info: 'Codec.aligned_alignedNotLengthDetWitness' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.aligned_alignedNotLengthDetWitness
/-- info: 'Codec.altConsumesByte' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.altConsumesByte
/-- info: 'Codec.append_toArray_ofFn_concat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.append_toArray_ofFn_concat
/-- info: 'Codec.arrayToBytes_bytesToArray' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.arrayToBytes_bytesToArray
/-- info: 'Codec.arrayToBytes_bytesToArray_apply' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.arrayToBytes_bytesToArray_apply
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
/-- info: 'Codec.decodeRepeat_mem_iff_general' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeRepeat_mem_iff_general
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
/-- info: 'Codec.decodeWholeBytes_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeWholeBytes_spec
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
/-- info: 'Codec.functional_iff_relFunctional' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.functional_iff_relFunctional
/-- info: 'Codec.huniq_byte' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.huniq_byte
/-- info: 'Codec.huniq_not_derivable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.huniq_not_derivable
/-- info: 'Codec.huniq_not_derivable_full' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.huniq_not_derivable_full
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
/-- info: 'Codec.lengthDet_not_implies_relAligned' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.lengthDet_not_implies_relAligned
/-- info: 'Codec.lengthDet_not_implies_relAligned_productive' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.lengthDet_not_implies_relAligned_productive
/-- info: 'Codec.lengthDet_of_lengthConst' does not depend on any axioms -/
#guard_msgs in
#print axioms Codec.lengthDet_of_lengthConst
/-- info: 'Codec.lengthDet_relUnambAlignedWitness' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.lengthDet_relUnambAlignedWitness
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
/-- info: 'Codec.nil_append_size' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.nil_append_size
/-- info: 'Codec.nil_append_toList' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.nil_append_toList
/-- info: 'Codec.not_lengthDet_alignedNotLengthDetWitness' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.not_lengthDet_alignedNotLengthDetWitness
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
/-- info: 'Codec.prod_relUnambAlignedWitness' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.prod_relUnambAlignedWitness
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
/-- info: 'Codec.relAligned_not_implies_lengthDet' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.relAligned_not_implies_lengthDet
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
/-- info: 'Codec.relRepeat_functional_of_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.relRepeat_functional_of_step
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
/-- info: 'Codec.relSepBy_functional' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.relSepBy_functional
/-- info: 'Codec.relTakeWhile_cast' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.relTakeWhile_cast
/-- info: 'Codec.relTakeWhile_functional' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.relTakeWhile_functional
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
/-- info: 'Codec.satisfy_sigmaFunctional' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Codec.satisfy_sigmaFunctional
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
/-- info: 'Iso.element_unapply_eq_some_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Iso.element_unapply_eq_some_iff
/-- info: 'Iso.foldRec_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Iso.foldRec_append
/-- info: 'Iso.ite_some_eq_some' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Iso.ite_some_eq_some
/-- info: 'Iso.map_fst_reverse_eq_some' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Iso.map_fst_reverse_eq_some
/-- info: 'Iso.map_swap_eq_none' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Iso.map_swap_eq_none
/-- info: 'Iso.map_swap_eq_some' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Iso.map_swap_eq_some
/-- info: 'Iso.prod_apply_eq_some' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Iso.prod_apply_eq_some
/-- info: 'Iso.prod_unapply_eq_some' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Iso.prod_unapply_eq_some
/-- info: 'Iso.subset_apply_eq_some' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Iso.subset_apply_eq_some
/-- info: 'Iso.subset_apply_eq_some_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Iso.subset_apply_eq_some_iff
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
