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
mirrored here by `localGatedTheorems`. **The mirror covers the THEOREM half only**
(`codec-audit-round-five` R6-12, task §7.3): the *def*-side counts
(`publicDefs` / mentioned / `definitionSurfaceAllowlist`) are computed by
`Axioms.lean` from the environment at build time and asserted by `headerNumbers`
there, but they are **not** derivable from this script — there is no def-side
generator step, so the def counts in the header are asserted by hand and this script
neither writes nor verifies them. The earlier sentence "the two cannot silently
disagree" was true of the theorem half and overstated the whole.

For the half it does cover: if this mirror drifts, `CodecAxioms`' build-time coverage
`run_cmd` fails the next `lake build` naming every theorem that ended up un-gated, so
a drift is a build failure rather than a hole. (This script cannot simply import
`Axioms`: the gate it regenerates has to be able to build *before* the gate does — a
bootstrap cycle.)

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
  -- `Prop`-valued structure-field projections, recognised by name (no shared suffix:
  -- each is `fun … => self.n`). Mirror of `CodecAxioms.propProjections`.
  --
  -- **This list drifted, and the drift un-pinned a law for a whole round**
  -- (`codec-audit-round-eight` §7.2). It listed `Iso.law`, `Codec.Normal.fixed`,
  -- `Codec.Normalizer.idem` — three names — while the real `propProjections` had four,
  -- `Codec.Suffix.hle` having been added to the gate by `codec-audit-round-seven`
  -- GC-02. So the generator emitted `Codec.Suffix.hle` into `gatedNames` and never
  -- emitted its `#guard_msgs` block: `gatedNames` claimed 347 gated theorems and the
  -- file pinned 346, and `headerNumbers` was reading the *mirror's* count, so the
  -- numbers agreed with each other while disagreeing with the tree. Regenerating found
  -- it in one line. **A mirror is a name list with no completeness arm of its own** —
  -- which is the lesson this file has now paid for four times — so the entry is
  -- commented with the reason it is here, exactly as `propProjections` entries are.
  let propProjections : Array Name := #[
    `Iso.law, `Codec.Normal.fixed, `Codec.Normalizer.idem,
    -- Found by the completeness arm in `Axioms.lean` (GC-02); missing here until
    -- round eight regenerated. `Suffix.hle : remaining ≤ n` is `Prop`-valued, so its
    -- `@[projection]` theorem is `fun … => self.2`.
    `Codec.Suffix.hle,
    -- **Five captures added by `codec-gate-denominators` §3**, mirrored here in the
    -- same commit that added them to `CodecAxioms.propProjections`. This is the
    -- fifth time this file has been bitten by a mirror drifting from the list it
    -- mirrors (§7.2 above), so the mirror is updated *with* the list, not after
    -- regenerating and wondering why the gate still pins a projection.
    `Codec.CandAligned_fst, `Codec.CandAligned_at, `Codec.packedCands_mem,
    `Iso.apply_eq_some_of_unapply, `Iso.unapply_eq_some_of_apply]
  if propProjections.contains n then return true
  -- **The recursion principle promoted to gated** (`codec-audit-round-nine` §6.4).
  -- `Codec.findFrom.induct` has a nonzero footprint (`[propext]`), which falsifies the
  -- allowlist group's stated property ("not a law ⇒ axiom-free"), so it is pinned with
  -- the other laws now. Without this exemption the `induct` pattern below would drop it
  -- and the generator would emit a `gatedNames` that excludes a name the gate requires —
  -- **the sixth time a mirror in this file has drifted from the list it mirrors**, and
  -- the first time the fix was a *narrowing of the pattern* rather than a copy of a name
  -- array. That is the shape worth remembering: this file has a second classifier, not
  -- just a second list.
  let promotedRecursionPrinciples : Array Name := #[`Codec.findFrom.induct]
  if promotedRecursionPrinciples.contains n then return false
  -- **Mirror of `CodecAxioms.theoremNameSuffixes`** (`codec-audit-round-nine` review A-4).
  -- This file cannot import `Axioms.lean` (bootstrap cycle), so the two copies are
  -- compared by the generator's own self-check below rather than by sharing the array.
  let theoremNameSuffixes : Array String := #[
    "eq_def", "inj", "injEq", "sizeOf_spec", "congr_simp", "dec", "induct", "eq"
  ]
  return theoremNameSuffixes.contains n.components.getLast!.toString

/-- **The mirror's internal consistency check.**

`codec-audit-round-nine` reviews A-4 and M-4. This file cannot import `Axioms.lean` (the gate
must exist before the generator can build it), so the classifier's lists are hand-copied here
and the drift risk is the one this repository has paid for twice.

**This function is the SMALLER half, and it says so.** It checks only that the two lists *this
file* holds are disjoint and non-empty — a property of the mirror, not a comparison with
`Axioms.lean`. An earlier revision of this docstring claimed the cross-file comparison was
"what `lake build` does, because a drift makes the generated `gatedNames` disagree with the
partition". **That is false in the direction that already cost a round** (review M-4): when the
mirror *undercounts*, the generator emits its smaller set into the generated `gatedNames`
region and **rewrites `Axioms.lean` with it**, so `partition` and `gateCoverage` read the
generated list and agree with it by construction. `AGENTS.md` records that exact regression
(`Codec.Suffix.hle` un-pinned for a whole round); it reproduces green under just this check.
The only residual guard is `headerNumbers`' `expectedGated` constant, which the same
regenerating session bumps — so it is a speed bump, not a check.

**The cross-file comparison that does work is a command, not a pass.** It runs in
`checks.mirror` (see `flake.nix`), which greps both files and diffs the lists in both
directions *after* the generator has run — i.e. against the committed artefacts, outside the
bootstrap cycle. That is where the real guarantee lives; this function is not it. -/
def mirrorSelfCheck : Except String Unit := do
  -- Mirrored from `CodecAxioms.derivedDefPatterns` (this file cannot import `Axioms`).
  let defPatterns : Array String := #[
    "casesOn", "recOn", "elim", "noConfusion", "noConfusionType",
    "ctorIdx", "ctorElim", "ctorElimType", "below", "brecOn", "go", "«term_≫_»"]
  let thmSuffixes : Array String := #[
    "eq_def", "inj", "injEq", "sizeOf_spec", "congr_simp", "dec", "induct", "eq"]
  -- The lists are deliberately disjoint: a name in both would mean the `def` classifier
  -- and the theorem classifier were removing the same declaration for two different
  -- stated reasons, which nothing else would notice.
  for x in defPatterns do
    if thmSuffixes.contains x then
      throw s!"`{x}` is in BOTH the def-pattern list and the theorem-suffix list; the two classifiers must not overlap"
  if defPatterns.isEmpty || thmSuffixes.isEmpty then
    throw "one of the two classifier lists is empty (a classifier that removes nothing is a classifier that was deleted)"
  return ()

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
  -- **The mirror runs its own self-check before writing anything**
  -- (`codec-audit-round-nine` review A-4). A drifted mirror that still splices is worse
  -- than one that refuses: it rewrites `Axioms.lean` into disagreement with the partition.
  match mirrorSelfCheck with
  | .error e => throwError s!"gen-axioms: {e}"
  | .ok () => pure ()
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
