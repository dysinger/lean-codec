/- Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later -/

import Codec
import Lean.Elab.Command

/-!
# Reproduce the README's `Iso`/`Codec` value counts

`codec-drift-closure` §2.3 + `docs-conformance`: "A count stated in documentation
SHALL be either generated from the tree or accompanied by the command that produces
it." `README.md` states two such counts in `[S1]` and `[S3]`:

* **19** public `Iso`-valued definitions, decomposed `13 + 4 + 2`;
* **15** `Codec` values a porter must reproduce: **7 constructors + 8 bounded
  definitions**, with **4** further `Codec` values that are counterexample witnesses.

Neither is asserted by a gate arm — they are claims about README prose, not about a
law, and adding an arm that counts a category defined by a README sentence would be
the tail wagging the dog. What the docs-conformance requirement asks for instead is
the **command**, so this file is that command:

```
nix develop --command lake env lean scripts/count-values.lean
```

Expected output is reproduced in the file's own last section, and the two counts are
re-asserted here with `#guard_msgs` so this script fails if the tree moves under them.
That is the whole point: the numbers in `README.md` are now checkable by running one
file, instead of by trusting a paragraph.

## The predicate, and why it is written out here

A count of "`Iso`-valued definitions" is only as good as its predicate — the lesson
`AGENTS.md` records from round six is that `grep '^def'` misses multi-line signatures
and cannot see through an alias. So the walk is an **environment walk**:

* candidate: a `defnInfo` constant in the `Codec` or `Iso` namespace;
* valued at `Iso`/`Codec`: the result type's **head constant** is `Iso`/`Codec` after
  stripping the `forall`/typeclass binders — i.e. `{α} → {β} → … → Iso α β` counts,
  which is how every combinator in this library is written;
* **compiler auxiliaries removed by the same rule the gate's def classifier uses**:
  the `_f`, `_sunfold`, `_unsafe_rec` last components that `derives`-style unfolding
  emits. Stated explicitly because a count whose removals are invisible is the defect
  `codec-gate-denominators` exists to stop.

`Iso.mk._flat_ctor` is removed for the same reason: it is the structure's compiled
constructor, not a declaration anyone wrote.
-/

open Lean Elab Command in
/-- Walk the environment and collect `(Iso-valued, Codec-valued)` definition names,
with the compiler auxiliaries removed **and counted**, so the removal is visible. -/
def countValues : CommandElabM (Array Name × Array Name × Nat × Nat) := do
  let env ← getEnv
  let isAux (n : Name) : Bool :=
    let last := n.components.getLast!
    last.toString == "_f" || last.toString == "_sunfold" ||
      last.toString == "_unsafe_rec" || last.toString == "_flat_ctor"
  -- Strip the leading `forall`/typeclass binders (this library writes every
  -- combinator as `{α} → … → Iso α β`), then take the head of the application
  -- spine. Two steps rather than one recursive function, because a self-call on
  -- `e.getAppFn` is not structurally decreasing and Lean rightly refuses it.
  let rec stripForalls (e : Expr) : Expr :=
    match e with
    | .forallE _ _ b _ => stripForalls b
    | _ => e
  let resultHead (e : Expr) : Name :=
    match stripForalls e |>.getAppFn with
    | .const c _ => c
    | _ => .anonymous
  let mut isos : Array Name := #[]
  let mut codecs : Array Name := #[]
  let mut dropped := 0
  for (n, ci) in env.constants.toList do
    if (`Codec).isPrefixOf n || (`Iso).isPrefixOf n then
      if let .defnInfo di := ci then
        let head := resultHead di.type
        if head == `Iso || head == `Codec then
          if isAux n then
            dropped := dropped + 1
          else if head == `Iso then
            isos := isos.push n
          else
            codecs := codecs.push n
  return (isos, codecs, dropped, 0)

/-- The numbers `README.md` states. **These are the assertion**, and they are the
point of this file: if a combinator is added or removed, this fails and whoever moved
the tree must decide whether the README sentence moves with it — which is exactly the
decision a silent count change would have hidden. -/
def expectedIsoValues : Nat := 19
def expectedCodecValues : Nat := 12

open Lean Elab Command in
#eval unsafe (show CommandElabM Unit from do
  let (isos, codecs, dropped, _) ← countValues
  logInfo m!"Iso-valued definitions: {isos.size} (plus {dropped} compiler auxiliary(ies) removed)"
  for n in isos.qsort (fun a b => a.toString < b.toString) do
    logInfo m!"  Iso  {n}"
  logInfo m!"Codec-valued definitions: {codecs.size}"
  for n in codecs.qsort (fun a b => a.toString < b.toString) do
    logInfo m!"  Codec  {n}"
  -- Asserted, not logged: a printed count rots, an asserted one fails the run.
  unless isos.size == expectedIsoValues do
    throwError m!"README [S1] says {expectedIsoValues} Iso-valued definitions; the walk found {isos.size}. Update README.md AND expectedIsoValues together."
  unless codecs.size == expectedCodecValues do
    throwError m!"README [S3] says 8 bounded + 4 witnesses = {expectedCodecValues} Codec-valued definitions; the walk found {codecs.size}. Update README.md AND expectedCodecValues together.")
