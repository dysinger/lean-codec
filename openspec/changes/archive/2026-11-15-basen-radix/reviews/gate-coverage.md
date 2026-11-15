# Gate-coverage review — `openspec/changes/basen-radix/`

**Target:** `proposal.md`, `design.md`, `specs/basen/spec.md` (3 ADDED), `tasks.md` (291 lines).
**Mandate:** the gates and the law surface — are the proposed laws statable and gated, and does
the plan account for the gate consequences?
**Mode:** read-only. `openspec validate basen-radix` → _"Change 'basen-radix' is valid"_
(3 long-requirement warnings). All line numbers below are from commands run this session.

## Summary

| rank        | id  | one line                                                                                                                                                                                                                                                                                                                  |
| ----------- | --- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| **MUST**    | M-1 | Task 4.1 says "regenerate"; `basen` has **no `scripts/`, no generator, no `BEGIN GENERATED` region** — `gatedNames` is a hand-edited `BEGIN PINNED` list. The instruction is a `lean-codec` construct the target repo does not have.                                                                                      |
| **MUST**    | M-2 | Task 3.2's six block-iso equalities **guaranteed fail** the def-coverage arm: each iso is in `definitionSurfaceAllowlist`, and the `both` branch throws when a def is mentioned by a gated theorem _and_ allowlisted. The plan claims these are gate-satisfying laws; they are the one shape the gate rejects.            |
| **MUST**    | M-3 | Task 4.3 says "update the header counts". The gate asserts **11** constants across **4** arms (theorem table ×3, prose ×4, def table ×3, plus a footprint distribution), not "the header counts". The plan under-scopes the gate consequence of adding theorems _and defs_.                                               |
| **MUST**    | M-4 | A radix-parameter `digitVal : Nat → …` / `toNat : Nat → …` contradicts `BaseN.lean:20–22`'s stated design ("never on a dispatch index") and the live spec's "no per-format function" family. No artifact in the change addresses it.                                                                                      |
| **SHOULD**  | S-1 | Task 4.1's "regenerate" is vacuous, so the `gatedNames` blocks are hand-written; the plan must state the **hand-pin + partition-arm** loop explicitly, or the first un-pinned law is discovered at build time rather than planned for.                                                                                    |
| **SHOULD**  | S-2 | `[propext, Quot.sound]`-only for `Nat` arithmetic is **plausible** (measured: `Nat.div`/`mod` lemmas are clean), but the plan names only _two_ leak shapes; `AGENTS.md` records **three**, and the third (`omega` closing a disjunction) is confirmed live and is exactly what task 2.4's rejection laws are shaped like. |
| **SHOULD**  | S-3 | The change deleted `basen-nat-iso` (task 6.1 `[x]`) with **no archive**, then cites "its analysis carried forward". The cited artifact no longer exists; the carry-forward is unverifiable.                                                                                                                               |
| **NITPICK** | N-1 | `basen/Axioms.lean` has **8** `run_cmd` arms, not the six the gate's own header prose enumerates. The change inherits the "six" phrasing.                                                                                                                                                                                 |
| **NITPICK** | N-2 | The spec delta's "Scenario: A lax spelling does not have its own image" is a _rule about how to write the theorem_, not an observable behaviour of the library — it cannot be a gate scenario in the sense the other scenarios are.                                                                                       |

## MUST

### M-1 — "regenerate" has no referent in `../lean-basen`

**tasks.md:203** — _"4.1 Pin every new law in `../lean-basen/Axioms.lean` and **regenerate**."_

`lean-codec` has a generator; `lean-basen` does not. Measured:

```
$ ls /Users/user/_/lean-basen/scripts/
ls: scripts/: No such file or directory
$ grep -n 'BEGIN GENERATED|END GENERATED' /Users/user/_/lean-basen/Axioms.lean
(exit 1)          # no GENERATED region at all
$ grep -n 'BEGIN|END ' /Users/user/_/lean-basen/Axioms.lean
2061:-- BEGIN PINNED gatedNames
2512:-- END PINNED gatedNames
```

Contrast `lean-codec`, which does have the mirror:

```
$ grep -n 'BEGIN GENERATED|END GENERATED' /Users/user/_/lean-codec/Axioms.lean
156:-- BEGIN GENERATED distribution
169:-- END GENERATED distribution
1157:-- BEGIN GENERATED gatedNames
1507:-- END GENERATED gatedNames
3167:-- BEGIN GENERATED body
4204:-- END GENERATED body
$ ls /Users/user/_/lean-codec/scripts/
audit-method-sentences.py  count-values.lean  gen-axioms.lean  gen-readme-gate.sh
```

**Mechanism.** In `codec`, "regenerate" runs `scripts/gen-axioms.lean`, which rewrites the
`BEGIN GENERATED` regions from the environment and whose theorem list is _mirrored_ by
`localGatedTheorems` (`scripts/gen-axioms.lean:147`), reconciled by `checks.mirror`. In
`basen` there is no such script, no mirror, and the region is named `BEGIN **PINNED**`
(not GENERATED) precisely because it is **hand-written**. The lockstep is enforced only by
the coverage `run_cmd` (`Axioms.lean:2624`), which compares `gatedNames` against the
environment at build time. So the correct loop is: write the `#guard_msgs` block by hand,
add the name to `gatedNames` by hand, and let the coverage arm tell you if you missed one.

**Why it matters.** A session that reads task 4.1 literally will `ls scripts/`, find nothing,
and either (a) stall, or (b) go looking for the `codec` script and run it in the wrong repo
(the change's own §6b warns that mixing repos is the likeliest error). It is the
"a sentence that states a method is a claim about code" defect class from `AGENTS.md`.

**Exact fix.** Replace tasks.md:203 with the measured loop:

> 4.1 Add a `#guard_msgs` `#print axioms` block **by hand** for every new law, and add each
> name to `BaseNAxioms.gatedNames` (`Axioms.lean:2066`, the `BEGIN PINNED` list). There is
> **no** generator in this repo — `scripts/` does not exist and the region is `BEGIN PINNED`,
> not `BEGIN GENERATED` (unlike `lean-codec`, whose `scripts/gen-axioms.lean` rewrites its
> regions). The coverage arm (`Axioms.lean:2624`) fails the build naming any public `BaseN`
> theorem that is in neither `gatedNames` nor `generatedAuxAllowlist` — that is the loop.

### M-2 — Task 3.2's equality theorems are the exact shape the def-coverage arm rejects

**tasks.md:171–173** — _"3.2 Prove, for each of the six power-of-two bases, that its block iso
agrees with `toNat` … These are the 'kept and proved equal' theorems of D6."_
**design.md D6** presents them as laws that stop the duplication being independent code.

The six isos are **allowlisted defs**, and a theorem that proves their agreement _mentions_
them. The def-coverage arm's `both` branch fails on exactly that:

```
$ sed -n 2860,2862p /Users/user/_/lean-basen/Axioms.lean
  let both := defs.filter fun n => mentioned.contains n && allow.contains n
  if !both.isEmpty then
    throwError m!"definitions that HAVE a gated law but are also allowlisted (drop the entry, or delete the law):\n{…}"

$ sed -n 1925,1930p /Users/user/_/lean-basen/Axioms.lean
  `BaseN.Base2.bitBlockIso,
  `BaseN.Base4.quartetBlockIso,
  `BaseN.Base8.octBlockIso,
  `BaseN.Base10.digBlockIso,
  `BaseN.Base16.hexBlockIso,
  `BaseN.Base16.hexBlockIsoF,
```

**Mechanism.** `mentionedByGated` (`Axioms.lean:1893`) collects every constant in every
gated theorem's **type**. Task 3.2's theorem type will name `bitBlockIso` (it _states_ the
agreement of that iso), so `bitBlockIso` becomes `mentioned` while still `allow`listed →
`both` non-empty → **build failure** naming all six. The allowlist reason for these entries
is _"the `law` structure field is proved at the definition site, so the kernel checks it at
construction and no theorem names it"_ (`Axioms.lean:1923–1924`) — a reason that becomes
**false the moment task 3.2 lands**, which is precisely what the `both` arm exists to catch.

**What the plan says.** Nothing. Task 3.2 does not mention `definitionSurfaceAllowlist`, the
`both` arm, or that landing it _changes the classification_ of six existing defs from
"allowlisted because no theorem names it" to "mentioned". D6 claims the isos stay fast paths;
it does not say the gate's def table must be edited.

**Exact fix.** Add a task 3.2b:

> 3.2b **Drop the six block-iso entries from `definitionSurfaceAllowlist`**
> (`Axioms.lean:1925–1931`) in the same commit as 3.2's theorems, and re-state the reason
> where it moves: the "no theorem names it" justification is now false, because 3.2's
> equality _does_ name it. The def-coverage `both` arm (`Axioms.lean:2860`) fails with all six
> named if this is forgotten. `expectedDefAllow` and `expectedMentioned` (`Axioms.lean:2867–2868`)
> move together: allowlist `-6`, mentioned `+6`, so `137 = 128 + 9` (re-derive, do not paste).

**And the theorem-side consequence the plan also misses.** The 3.2 equalities are **public
`BaseN` theorems**, so they must be pinned too — they will be counted in `expectedPub`
(`Axioms.lean:2742`) and `expectedGated` (`:2743`), and in the footprint distribution
(`statedDistPS`, `:2817`). So 3.2 is not "a theorem that exists beside the gate"; it is a
`+6` on the theorem table, a `+6` on the pinned count, a `+6` on `[propext, Quot.sound]` in
the distribution, **and** a `-6/+6` on the def table. One task, four constants.

### M-3 — "update the header counts" under-scopes what the gate asserts

**tasks.md:208** — _"4.3 Update the header counts the `headerNumbers` arm asserts."_

The gate asserts **11** numeric constants, in **four** different `run_cmd` arms. Measured:

```
$ grep -n 'let expected\|let stated' /Users/user/_/lean-basen/Axioms.lean
2742:  let expectedPub := 490
2743:  let expectedGated := 444
2744:  let expectedAllow := 46
2784:  let statedPrintBlockCount := 447
2785:  let statedGatedNamesCount := 444
2817:  let statedDistPS := 381
2818:  let statedDistP := 48
2819:  let statedDistZ := 15
2866:  let expectedDefs := 137
2867:  let expectedMentioned := 122
2868:  let expectedDefAllow := 15
```

- **Theorem table arm** (`:2742–2744`): `expectedPub`, `expectedGated`, `expectedAllow`.
- **Prose arm** (`:2784–2819`): `statedPrintBlockCount`, `statedGatedNamesCount`, and the
  three-way distribution `statedDistPS`/`statedDistP`/`statedDistZ`.
- **Def-table arm** (`:2866–2868`): `expectedDefs`, `expectedMentioned`, `expectedDefAllow`.
- **Bench arm** (`:2905`): `stated := 12` `native_decide` — unaffected by this change, but it
  is an asserted constant in the same file and should be named in 4.3 as _not_ moving.

Plus the **header prose table itself** (`Axioms.lean:1655–1700`), which the arm checks
against the constants — so "the header counts" is really "the constants _and_ the table they
mirror". "headerNumbers" is one arm; the distribution and def-table arms are **separate**.

**Exact fix.** Rewrite task 4.3 to enumerate, and say which move for _this_ change (theorem
additions move 4, the def-classification move moves 2, the prose's footprint distribution
moves 1, the bench count moves 0):

> 4.3 Update **every** asserted constant the S arms check, in the same commit as the
> regeneration: `expectedPub`/`expectedGated`/`expectedAllow` (`:2742–2744`);
> `statedPrintBlockCount`/`statedGatedNamesCount` and the distribution
> `statedDistPS`/`2`/`3` (`:2784–2819`); `expectedDefs`/`expectedMentioned`/`expectedDefAllow`
> (`:2866–2868`); and the "universe, as measured" prose tables they mirror (`:1655–1700`).
> `stated := 12` (`:2905`, bench `native_decide`) does **not** move. The `both` arm (M-2) also
> moves `expectedMentioned`/`expectedDefAllow` by ±6 with no law added.

### M-4 — a radix-parameter entry point contradicts `BaseN.lean`'s stated design

**proposal.md:44–49** proposes `digitVal : (radix : Nat) → UInt8 → Option Nat`,
`toNat : (radix : Nat) → …`, `ofNat : (radix : Nat) → …`.

`BaseN.lean:20–22` states, in the module docstring of the package root:

```
There is **no** `Base` enum and **no** `encode (b : Base)` / `decode (b : Base)`
facade: the radix lives in the value the caller already holds, never on a
dispatch index.
```

**Mechanism.** This is not a `Codec` decoder and so does not violate the live spec's
"no per-format `decode`/`encode` triple" (Requirement at `spec.md:24`, `spec.md:94`) —
the new functions are numeral helpers, not decoders of the format's value. **But** the
`BaseN.lean` docstring sentence is broader than the spec: it says _the radix never lives on a
dispatch index_, and `toNat : (radix : Nat) → …` puts it on exactly that. The change's own
Risk section and D1 argue the generic layer is right (seven proofs become one), so the
**decision may well be correct** — but the plan must _reconcile_ the sentence, not leave a
reader to discover that `BaseN.lean`'s docstring now describes a package that no longer
exists. This is the same class `AGENTS.md` records as "a claim whose stated method is not its
code's method", and round nine's finding #6 in its table.

**Exact fix.** Add to D1 a paragraph and a task:

> D1 note: `BaseN.lean:20–22` states "the radix lives in the value the caller already holds,
> never on a dispatch index." `toNat`/`ofNat` are a **numeral** layer above the `Codec` values,
> not a decoder facade, so the _spirit_ of the sentence (no `decode (b : Base)` dispatch
> replacing `Codec.decode`) still holds — but the _letter_ ("never on a dispatch index") does
> not. Amend the docstring in the same change: say the radix-parameterised functions exist as
> a numeral helper layered **above** the per-base `Codec` values, and that no `Codec`-level
> dispatch was introduced.

(And note it is a `BaseN.lean` docstring, so the footprint/stated-claim arm at
`Axioms.lean:2990` walks it — a sentence here that stated a footprint would be a claim site.
Not a footprint claim, so safe, but amend rather than delete-and-forget.)

## SHOULD

### S-1 — the hand-pin loop is not stated, so the first un-pinned law is a build-time discovery

Follows from M-1. With no generator, every new law needs (a) a `#guard_msgs`/`#print axioms`
block and (b) a `gatedNames` entry, both by hand. The plan's 4.1 says "pin … and regenerate",
which tells a session _what_ but not _how_, in a repo where "how" is manual. The pinned list
is 444 entries (`Axioms.lean:2066–2512`) maintained by hand and kept honest only by the
coverage `run_cmd`. Fix: state the two-step manual loop in 4.1 (see M-1's fix text), and add
to §5 the exact failure text to expect when a name is missed — the coverage arm's
`"theorems not pinned by this gate (add a `#guard_msgs` block)"` (`Axioms.lean:2673`).

### S-2 — `[propext, Quot.sound]`-only is plausible, but the plan lists two leak shapes and three exist

**tasks.md:205–207** — _"Watch for the two recorded leaks — a dependent `cases` carrying an
equation, and `decide_eq_true (by omega)` over a disjunction (`AGENTS.md`)."_

`AGENTS.md` records **three** shapes (`Classical.choice` trap, shapes 1–3); tasks 4.2 lists
two. The third — _"a `match`/`if` on a `Bool` in the goal"_ — is the one task 2.4's rejection
laws (`toNat` on an out-of-alphabet byte) and 1.3's `ofNat` (`if n < radix then …`) are
shaped like.

**Measured on this tree** (`nix develop --command lake env lean /tmp/probe*.lean`):

```
'Codec.fill_surj'       depends on axioms: [propext]              # the quotient is clean
'Codec.fill_inj'        depends on axioms: [propext]
'Codec.decodeNormal_encode' depends on axioms: [propext]
'Nat.div_eq' / 'Nat.div_add_mod' / 'Nat.mod_lt' / 'Nat.div_lt_self'
                        depend on axioms: [propext, Quot.sound]   # Nat arithmetic is clean
'disjOmega'  (omega closing a disjunction)
                        depends on axioms: [propext, Classical.choice, Quot.sound]   # LEAK
'disjExp'    (explicit Or.inl/Or.inr) depends on axioms: [propext, Quot.sound]        # clean
```

So the **expectation holds plausibly**: `Nat` div/mod and the `Normal` quotient are both
`[propext, Quot.sound]`-clean, and the only _confirmed_ leak in the primitive set is the
omega-disjunction, which is avoidable (`disjExp`). The plan should say so with the
measurement rather than name two shapes from memory.

**Exact fix.** Replace 4.2 with: all three shapes from `AGENTS.md`, add that the
rejection laws (2.4) are `Option`/disjunction-shaped and must use explicit `Or.inl`/`Or.inr`
(measured: `omega` on a disjunction leaks `Classical.choice`, explicit constructors do not),
and add the measured evidence that `Nat.div`/`mod` and `Codec.fill_surj` are clean, so the
base expectation is sound and the risk is localised.

### S-3 — the "carried forward" analysis was deleted with no archive

**tasks.md:250–252 (6.1, `[x]`)** — _"Delete `openspec/changes/basen-nat-iso/`… its three
ADDED requirements are subsumed."_ **tasks.md:255–257 (6.2)** — _"Confirm nothing in that
change's analysis is lost."_

Measured:

```
$ git log --oneline -3 -- openspec/changes/basen-nat-iso
10f601f openspec: author basen-radix, and retire basen-nat-iso into it
$ ls openspec/changes/basen-nat-iso
ls: openspec/changes/basen-nat-iso: No such file or directory
$ ls openspec/changes/archive | grep -i 'nat-iso'
(no output)
```

The change is **deleted, not archived**. Task 6.2 asks a reader to "confirm nothing is lost"
from an artifact that no longer exists. Its §Risk (quoted in the proposal and D2) and its
"empty encoding for zero was a defect" measurement (D4) are now cited but unrecoverable —
the exact `/tmp`-citation failure `AGENTS.md` forbids ("an id whose record lives only in
`/tmp` is a citation to a file that will not exist"). Since it was 0/18 and never started,
deletion is defensible; **citing it as a carried-forward evidence base is not.**

**Exact fix.** Either (a) quote the two carried-forward facts inline in `design.md` (D2 the
quotient decision, D4 the empty-encoding-is-a-defect measurement) so they survive the
deletion — the proposal already paraphrases them, so promote that paraphrase to `design.md`
with attribution "from the retired `basen-nat-iso`" — or (b) `git show 10f601f^` and copy
the relevant snippets into `design.md` as a quoted appendix. Do not leave task 6.2 asking a
reader to confirm against a deleted file.

## NITPICK

### N-1 — `basen`'s gate has 8 `run_cmd` arms, not the "six" the header prose names

```
$ grep -c '^run_cmd do' /Users/user/_/lean-basen/Axioms.lean
8
```

`Axioms.lean:1645` says _"Two `run_cmd` checks make the gate a partition"_ and the file's
header prose (and `AGENTS.md`'s six-line gate quotation) enumerate six _printed_ lines, but
there are eight `run_cmd` blocks: derived-def classifier, derived-def-pattern audit,
coverage, partition, header table, def coverage, bench count, stated footprints. The change's
§1/§4 talk about "the gate" generically; a session counting arms from the header prose will
undercount by two. Not a defect _of this change_, but the change is the place a session will
first touch the arms. Fix in passing: when 4.1/4.3 touch "the gate", point at the **grep**,
not at the header's count.

### N-2 — "Scenario: A lax spelling does not have its own image" is a rule, not a behaviour

**spec delta, `specs/basen/spec.md:~95`** — _"WHEN the iso is stated over raw digit syntax
rather than over the quotient / THEN that is a defect: … The codomain SHALL be the
quotient, and a three-spelling witness SHALL exist and be mutation-tested."_

Every other scenario in this delta names an observable of the library (a decode returns
`some`, an encode has no leading zeros). This one names an _anti-pattern_ and prescribes a
mutation test — which is a claim about the change's _process_, not about `basen`'s behaviour.
`AGENTS.md` ("assert the effect, not the rule") is the governing lesson: the _effect_ is
"three spellings reach one image" (scenario 1 of the same requirement) and "`fill_inj` gives
`norm s = norm t`" — both assertable. The anti-pattern sentence belongs in `design.md` D2,
which already has it verbatim.

Fix: drop the scenario, keep D2's paragraph. Or, if kept, restate as the effect: _"WHEN
`"007"`, `"7"` and `"  7"` are each passed through `fill`, THEN the three `Normal` values are
equal — a theorem (`fill_inj`), not a comment."_

## Refuted / could not confirm

- **Refuted: "the plan's `[propext, Quot.sound]` expectation is implausible for `Nat`."**
  Measured false-of-the-worry: `Nat.div_eq`, `Nat.div_add_mod`, `Nat.mod_lt`,
  `Nat.div_lt_self` are all `[propext, Quot.sound]`; the `Normal` layer is `[propext]`-only.
  The expectation is plausible; only the omega-disjunction shape (S-2) is a confirmed hazard.
- **Refuted: "the delta contradicts a live requirement."** All 10 live requirements
  (`spec.md:10,24,94,204,233,259,409,476,497,518`) were read. The three ADDED requirements
  are _additive_: they add a numeral layer above the `Codec` values, and the closest live
  requirement ("The `basen` bases are `Codec` values", `spec.md:24`) constrains the
  **decoder/encoder**, which this change does not touch (no decoder/encoder statement
  changes — proposal.md Non-goals). The _tension_ is with `BaseN.lean`'s **docstring**
  (M-4), not with the spec. One residual, **UNVERIFIED**: the live spec's "conformance laws
  are gated" requirement (`spec.md:259`) mandates a **bench-lane vector** for every new
  theorem; task 5.3 says "if any run-time check is added, it goes in the bench", which reads
  as permissive where the requirement reads as mandating. Whether `basen`'s convention treats
  non-decode laws as exempt from the bench vector is a question the spec does not answer for
  me — measurement would be: `grep` the bench for a vector per existing non-decode law. Not
  confirmed either way this session.
- **UNVERIFIED: whether `numeralIso`'s `unapply` can be total.** `Iso` (`Codec/Iso.lean:27`)
  has `unapply : β → Option α`; a numeral `Iso Nat X` with `apply := ofNat`/`unapply := toNat`
  is fine, but the plan's claim that "`toNat`/`ofNat` are **total** functions on the quotient
  representative" (design D2) must become "`apply` is total via `some`" to match `Iso`'s
  Option-valued fields. That is a wording fix, not a blocker, but the plan states it as
  totality of the pair, which `Iso.law` alone does not give. Measurement deferred until a
  `numeralIso` is written; noted, not claimed.
- **Not measured (by design):** the actual `Nat`-valued fold laws and the three-spelling
  witness do not exist yet, so "is it non-vacuous" cannot be measured — only that the plan
  carries mutation tests for both (tasks 1.4, 2.3, 3.3), which is the correct posture.
