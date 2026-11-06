/- Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later -/

import Codec
import Lean.Elab.Command

/-!
# Generator for the `Axioms.lean` gate body

Run from the repository root:

```
nix develop --command lake env lean scripts/gen-axioms.lean
```

It rewrites the two regions of `Axioms.lean` delimited by

    -- BEGIN GENERATED gatedNames ... -- END GENERATED gatedNames
    -- BEGIN GENERATED body ...       -- END GENERATED body

from the **compiled environment**: every public `Codec`/`Iso` theorem.

The set is defined once, in `CodecAxioms.gatedTheorems` in `Axioms.lean`, and
mirrored here by `localGatedTheorems`. The two cannot silently disagree: if this
mirror drifts, `CodecAxioms`' build-time coverage `run_cmd` fails the next
`lake build` naming every theorem that ended up un-gated, so a drift is a build
failure rather than a hole. (This script cannot simply import `Axioms`: the gate it
regenerates has to be able to build *before* the gate does — a bootstrap cycle.)

This script is a **tool**, not part of the gate. The gate is the generated
`#guard_msgs` blocks plus `CodecAxioms`' coverage `run_cmd`, both of which run on
every `lake build`.
-/

open Lean Elab Command

/-- Mirror of `CodecAxioms.isGeneratedAux` in `Axioms.lean` — see the module header
for why this cannot be imported.

Deliberate difference from the classifier it mirrors: an `eq_irrel`-suffixed name is
**not** dropped, because `Codec.Nat.eq_irrel` is an authored law (the audit's finding
— the suffix rule silently un-gated it). The suite partition check in `Axioms.lean`
forces the two sides to agree: the allowlist there lists exactly the names this
predicate drops, so if this mirror ever drops something the gate expects, `lake
build` fails naming it. -/
def localIsGeneratedAux (n : Name) : Bool := Id.run do
  -- Authored laws that happen to carry a generated-looking suffix. Keep in sync
  -- with `CodecAxioms.gatedTheorems`'s comment; the partition check is the guard.
  let authored : Array Name := #[`Codec.Nat.eq_irrel]
  if authored.contains n then return false
  let s := n.components.getLast!.toString
  return s == "eq_def" || s == "inj" || s == "injEq" || s == "sizeOf_spec" ||
    s == "congr_simp" || s == "dec" || s == "induct"

/-- Mirror of `CodecAxioms.gatedTheorems` in `Axioms.lean`. -/
def localGatedTheorems (env : Environment) : Array Name := Id.run do
  let mut thms : Array Name := #[]
  for (name, ci) in env.constants.toList do
    if (`Codec).isPrefixOf name || (`Iso).isPrefixOf name then
      match ci with
      | .thmInfo _ =>
        if ci.isUnsafe || isPrivateName name || name.isInternalDetail ||
            localIsGeneratedAux name then
          pure ()
        else
          thms := thms.push name
      | _ => pure ()
  return thms.qsort (fun a b => Name.toString a < Name.toString b)

/-- Render the `#print axioms` diagnostic for `n` verbatim (the text a `#guard_msgs`
must pin). -/
def renderFragments (n : Name) : CommandElabM String := do
  let ax ← Lean.collectAxioms n
  return match ax.toList with
    | [] => "does not depend on any axioms"
    | l => s!"depends on axioms: [{String.intercalate ", " (l.map Name.toString)}]"

/-- One `#guard_msgs` block pinning `n`'s exact `#print axioms` output. -/
def renderOne (n : Name) : CommandElabM String := do
  let frag ← renderFragments n
  return s!"/-- info: '{Name.toString n}' {frag} -/\n#guard_msgs in\n#print axioms {n}\n"

/-- Replace the text between `begin` and `end_` markers, keeping both markers. -/
def splice (src begin end_ body : String) : Except String String := do
  let parts := src.splitOn begin
  if parts.length ≤ 1 then throw s!"marker not found: {begin}"
  let before := parts.head!
  let tail := String.intercalate begin parts.tail!
  let parts2 := tail.splitOn end_
  if parts2.length ≤ 1 then throw s!"marker not found: {end_}"
  let after := String.intercalate end_ parts2.tail!
  return s!"{before}{begin}{body}{end_}{after}"

/-- The footprint distribution, counted from the same `collectAxioms` output the
`#guard_msgs` blocks pin. Emitted into `Axioms.lean`'s header between markers so the
table is **generated rather than transcribed** — see `codec-audit-round-three` §1.9.

The renderer keys on the `collectAxioms` *name list* rather than by parsing prose, which
is precisely the check design D1 says the audit's own parser got wrong (it truncated at
the `?` in `Codec.attach_getElem?_corr` and `Codec.map_toList_eq_ofFn_none_iff`). Here
the names come straight from the elaborator, so there is nothing to truncate. -/
def renderDistribution (thms : List Name) : CommandElabM String := do
  let mut pq := 0
  let mut p := 0
  let mut q := 0
  let mut none_ := 0
  let mut other : Array (Name × List Name) := #[]
  for n in thms do
    let ax := (← Lean.collectAxioms n).toList
    if ax.isEmpty then none_ := none_ + 1
    else if ax == [``propext, ``Quot.sound] then pq := pq + 1
    else if ax == [``propext] then p := p + 1
    else if ax == [``Quot.sound] then q := q + 1
    else other := other.push (n, ax)
  let total := thms.length
  let mut out := "\n"
  out := out ++ s!"| footprint | count |\n| --- | --- |\n"
  out := out ++ s!"| `[propext, Quot.sound]` | {pq} |\n"
  out := out ++ s!"| `[propext]` | {p} |\n"
  out := out ++ s!"| `[Quot.sound]` | {q} |\n"
  out := out ++ s!"| axiom-free | {none_} |\n"
  out := out ++ s!"| anything else | {other.size} |\n"
  out := out ++ s!"| **total** | **{total}** |\n"
  if other.isEmpty then
    out := out ++ s!"\n`[propext, Classical.choice, Quot.sound]` rows: **0** — every gated law is\ninside the discipline.\n"
  else
    out := out ++ s!"\n**OUTSIDE THE DISCIPLINE** ({other.size}) — fix or exclude with a reason:\n\n"
    for (n, ax) in other do
      out := out ++ s!"* `{Name.toString n}` — `[{String.intercalate ", " (ax.map Name.toString)}]`\n"
  if pq + p + q + none_ + other.size != total then
    throwError "distribution does not add up to the gated count"
  return out

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let thms := localGatedTheorems env |>.toList
  let mut body := "\n"
  for n in thms do
    body := body ++ (← renderOne n)
  let names := thms.map fun n => s!"`{Name.toString n}"
  let namesBlock := "/-- The names this file actually pins a `#guard_msgs` block for. GENERATED — written\nin lockstep with the body, so it is a record of what is gated rather than a second\nlist to maintain by hand. -/\ndef gatedNames : List Lean.Name := [\n  " ++ String.intercalate "\n  ," names ++ "]\n"
  let path : System.FilePath := "Axioms.lean"
  let src ← IO.FS.readFile path
  let .ok src := splice src "-- BEGIN GENERATED gatedNames\n" "-- END GENERATED gatedNames\n" namesBlock
    | throwError "gatedNames splice failed"
  let .ok src := splice src "-- BEGIN GENERATED body\n" "-- END GENERATED body\n" body
    | throwError "body splice failed"
  let dist ← renderDistribution thms
  let .ok src := splice src "-- BEGIN GENERATED distribution\n" "-- END GENERATED distribution\n" dist
    | throwError "distribution splice failed"
  IO.FS.writeFile path src
  logInfo s!"Axioms.lean: rewrote {thms.length} gates and the distribution table"
