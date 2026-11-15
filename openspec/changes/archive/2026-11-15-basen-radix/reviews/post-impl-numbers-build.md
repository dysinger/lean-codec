# `basen-radix` — numbers, build claims and repo hygiene

Audit of the completed change (44/44 tasks) across:
`lean-codec/openspec/changes/basen-radix/tasks.md` (MUST-READ: §3.2, 3.3, 4.1, 4.2, 4.2b, 4.3, 5.1, 5.1b, 5.1c, 5.3),
`lean-basen/CHANGELOG.md` (the 2026-11-15 entry), `lean-basen/Axioms.lean` (header tables + asserted constants).

Landing HEAD in `lean-basen`: `bae490a`. Baseline: `4e85200`. In `lean-codec`: `829c3bb`.

## Summary

| severity    | count |
| ----------- | ----- |
| **MUST**    | 4     |
| **SHOULD**  | 5     |
| **NITPICK** | 4     |

Findings are ranked by whether a reader acting on the document would be misled about a
_number that a command contradicts_.

No soundness defect is alleged: I did not run `lake build`, but a parse of every one of the
**676** committed `#guard_msgs` footprint blocks shows **no `Classical.choice`, no `sorryAx`**
anywhere — so the discipline claim survives. What fails is the _arithmetic and the prose_
around it.

---

## MUST

### M-1 — `Axioms.lean`'s header paragraph is stale by 189 theorems and its own check does not read it

**Location:** `lean-basen/Axioms.lean:38-43`
**Claim (stated):**

```
The file carries **487 pins**: **484** are `BaseN.*` laws and **3** are `Codec.*` …
`publicTheorems` walks only `BaseN`, so the gate's own universe is **533 = 484 + 49 allowlisted**.
The 484 `BaseN` pinned footprints are 412 `[propext, Quot.sound]`, 50 `[propext]`-only and 22 axiom-free
(412 + 50 + 22 = 484) …
```

**Truth (derived):**

- Header table at `Axioms.lean:1668-1673` and asserted constants (`expectedPub := 722`,
  `expectedGated := 670`, `expectedAllow := 52`) give **722 = 670 + 52**.
- Measured distribution from the committed blocks (see M-2): **546 / 83 / 41 = 670**.

Every figure in the paragraph is wrong:
`487`→**673** pins (670+3), `533`→**722**, `484`→**670**, `49`→**52**,
`412/50/22`→**546/83/41**.

**Arithmetic:**

```
paragraph:  533 = 484 + 49           (✓ self-consistent, but 533 ≠ 722)
truth:      722 = 670 + 52           (Axioms.lean:3803-3805, table :1668-1670)
paragraph dist:  412 + 50 + 22 = 484
truth dist:      546 + 83 + 41 = 670   (from the 676 #guard_msgs blocks)
```

**Root cause — the check that _claims_ to guard this paragraph does not:**
`Axioms.lean:3835-3840` asserts `if baseNPins + codecPins != 673` — a **literal 673** compared
against a **computed** `baseNPins + 3`. It never reads the prose's `487`. The comment above it
(`:3836`) says "The prose states the total as `baseNPins + codecPins`" — **false**: the prose
states `487`. So the paragraph is unasserted and has rotted (last meaningfully set at `c1cfe50`,
2026-11-14, before this session), while `git blame` shows the session touched these lines' file
159 times without fixing them.

**Correction:** rewrite `:38-43` to
`The file carries **673 pins**: **670** `BaseN._`and **3**`Codec._`… the gate's own
universe is **722 = 670 + 52 allowlisted**. The 670`BaseN`pinned footprints are 546`[propext, Quot.sound]`, 83 `[propext]`-only and 41 axiom-free (546 + 83 + 41 = 670) …`,
and either delete the `487`/`533`-shaped claim or bind it to `expectedPub`/`expectedGated`.
(The header docstring already promises "the figures here are now computed by `headerNumbers`" —
make that true or delete it.)

**Evidence:**

```
$ sed -n '38,43p' Axioms.lean        # 487 / 533 = 484 + 49 / 412+50+22
$ sed -n '3803,3805p' Axioms.lean    # 722 / 670 / 52
$ sed -n '1668,1670p' Axioms.lean    # 722 / 670 / 52
```

---

### M-2 — `tasks.md` 4.3's footprint distribution matches neither the tree nor any commit

**Location:** `lean-codec/.../tasks.md:850`
**Claim:**

```
plus the distribution
(`546 + 82 + 41 = 669` before the isos' `apply` laws, `553/82/41` after)
```

**Truth (from git + the tree):**

- "before the apply laws" = commit `b29c38c`: `expectedGated := 660`,
  `statedDistPS := 539`, `statedDistP := 82`, `statedDistZ := 39` →
  **539 + 82 + 39 = 660**.
- "after" = HEAD `5044f95`/`bae490a`: **546 + 83 + 41 = 670**.

The task's "before" `546 + 82 + 41 = 669` is neither the before-state nor the after-state;
it is a spliced tuple. The task's "after" `553/82/41` sums to **676 ≠ 670** and appears in no
constant of any commit.

**Arithmetic:**

```
claimed before: 546 + 82 + 41 = 669   (equals no commit; b29c38c is 660)
claimed after:  553 + 82 + 41 = 676   (≠ baseNPins 670  → fails the gate's own sum check)
true before:    539 + 82 + 39 = 660   (git show b29c38c:Axioms.lean)
true after:     546 + 83 + 41 = 670   (git show 5044f95:Axioms.lean / HEAD)
true delta:     PS +7, P +1, Z +2   (sum +10), not the implied +7/0/0
```

This is exactly the "padded range / parts-that-do-not-sum" defect the repo's AGENTS.md tabulates
four times over: a derived triple whose parts do not add to the stated total.

**Correction:** replace with
`the distribution `539 + 82 + 39 = 660`before the isos'`apply`laws,`546 + 83 + 41 = 670`
after (PS +7, P +1, Z +2)`, and note the source is `statedDist*` at `b29c38c` vs HEAD, not a
remembered triple.

**Evidence:**

```
$ for c in b29c38c 5044f95; do git show $c:Axioms.lean | grep -E 'statedDist(PS|P|Z)'; done
  statedDistPS := 539 / statedDistP := 82 / statedDistZ := 39      # b29c38c
  statedDistPS := 546 / statedDistP := 83 / statedDistZ := 41      # 5044f95
$ python3 -c "print(539+82+39, 546+83+41, 546+82+41, 553+82+41)"
  660 670 669 676
```

---

### M-3 — `CHANGELOG.md` states "Every law is `[propext, Quot.sound]`-only" — false for ~64 of the 229 new laws

**Location:** `lean-basen/CHANGELOG.md:40`
**Claim:** "Every law is `[propext, Quot.sound]`-only with zero `Classical.choice`; each is
pinned by a `#guard_msgs` block …"
**Truth:** the 229 gated blocks for the new modules (`Radix`, `RadixAlphabets`, `RadixCodec`,
`RadixTie`) decompose as **165 `[propext, Quot.sound]`, 35 `[propext]`-only, 29 axiom-free**.
"The discipline [⊆ {propext, Quot.sound}] holds" is true; "is `[propext, Quot.sound]`-only"
is false for **64 of 229**. The `zero Classical.choice` half of the sentence IS true.

**Arithmetic:**

```
new-module #print blocks: 229
  165 [propext, Quot.sound]
   35 [propext]
   29 axiom-free
  ---
  229  (sum closes)
laws NOT '[propext, Quot.sound]'-only: 35 + 29 = 64
```

This is precisely the imprecision `tasks.md` 4.5 itself records (84 / 21 / 12 for the 117
`RadixCodec` laws alone) — so the CHANGELOG contradicts its own source document.

**Correction:** "Every new law's footprint is within `{propext, Quot.sound}` — measured
165 `[propext, Quot.sound]`, 35 `[propext]`, 29 axiom-free — with **zero** `Classical.choice`."

**Evidence:**

```
$ python3 -c "<walk 676 #guard_msgs blocks, filter new modules>"   # 165 / 35 / 29 = 229
$ grep -c 'Classical' Axioms.lean                                    # 0 hits in footprints
```

---

### M-4 — `basen`'s `lakefile.lean` claims `-DwarningAsError` reaches `bench`; it does not

**Location:** `lean-basen/lakefile.lean:37-40` (comment) vs `:49-50` (the `lean_exe bench`)
**Claim (in the lakefile's own docstring, repeated in effect by the `basen` bench write-up in
AGENTS.md that this audit's mandate covers):**

> "the flag belongs on the _library_ rather than on one consumer so every path that
> compiles `BaseN` **inherits it (including `bench`** and the sandboxed `nix build .#checks.lean)`."
> **Truth:** `lean_lib BaseN` (`:39`) and `lean_lib Axioms` (`:47`) set
> `moreLeanArgs := #["-DwarningAsError=true"]`, but `lean_exe bench where root := \`Bench` (`:49-50`)
sets **no** `moreLeanArgs`. An exe is a separate root; the library flag does not ride on
`Bench.lean`'s own theorems. This is the exact over-read `codec-audit-round-nine`§1.8
corrected in`lean-codec`— where`lakefile.lean:74+`now sets the flag **on the`bench`exe**.`basen` never got the port.

**Arithmetic / classification:** not a numeric defect; a **build claim that is false** (axis C:
"Is `-DwarningAsError=true` on **every** root that compiles gated modules (lib AND exe)?" → **No**).

**Correction:** add

```lean
lean_exe bench where
  root := `Bench
  moreLeanArgs := #["-DwarningAsError=true"]
```

and fix the `:37-40` comment, which asserts the opposite ("including `bench`"). Until then,
`tasks.md` 5.1b's "zero warnings" for the bench lane is _observed_, not _enforced_ — a `sorry`
in a `Bench.lean` theorem would warn and pass.

**Evidence:**

```
$ sed -n '49,50p' lakefile.lean        # lean_exe bench / root := `Bench   (no moreLeanArgs)
$ sed -n '37,40p' lakefile.lean        # "…inherits it (including `bench` …)"
$ grep -n 'lean_exe bench' -A6 /Users/user/_/lean-codec/lakefile.lean   # codec DOES set it
```

_(Scope note: this defect predates the session — `lakefile.lean` last changed at `9686749` — but
it is a live build claim in the exact files this audit covers, and §5.1b leans on it.)_

---

## SHOULD

### S-1 — `tasks.md` 4.3's line citations for every constant are off by ~1000 lines

**Location:** `tasks.md:852-861`
**Claim:** the four constant groups are at `Axioms.lean:2742-2744`, `:2784-2785`,
`:2817-2819`, `:2866-2868`; `stated := 12` at `:2905`; `mentionedCount` at `:2858`;
`silent` at `:2852`; the sum check at `:2830`.
**Truth:** actual locations are `:3803-3805`, `:3845-3846`, `:3878-3880`, `:3927-3929`,
`stated := 12` at `:3966`. The cited lines are `#print axioms` blocks, not the constants.

**Correction:** `:3803-3805` / `:3845-3846` / `:3878-3880` / `:3927-3929`, `stated := 12`
at `:3966`, `mentionedCount` at `:3937`, `silent` at `:3914`, sum check at `:3944`.
Same class in §4.1: `BEGIN PINNED` is `:2896`/`:2901`, not `:2061`/`:2066`; and §4.2:
`definitionSurfaceAllowlist` is at `:1943`, not `:1922-1946`.

**Evidence:**

```
$ grep -n 'let expectedPub\|let statedDistPS\|let stated := \|def definitionSurfaceAllowlist\|BEGIN PINNED' Axioms.lean
3803, 3878, 3966, 1943, 2896
```

---

### S-2 — §4.2's "Allowlist 18 → 11, mentioned 143 → 150 / 161 = 150 + 11" is verified ✓ but its _premise_ line cites wrong places

**Location:** `tasks.md:781-783` and `:800-816`
**Claim:** "Allowlist 18 → 11, mentioned 143 → 150" and `161 = 150 + 11`; region `:1922-1946`
"holds **ten** `Iso`-law-as-field entries".
**Truth:** the _counts are correct_ — `definitionSurfaceAllowlist` has **11** entries, header
table says **161 = 150 + 11**, asserted constants `expectedDefs := 161`, `expectedMentioned :=
150`, `expectedDefAllow := 11` all agree; `18 − 7 = 11` and `143 + 7 = 150` and `143 + 18 =
150 + 11 = 161`. **But** the allowlist `Array` starts at `:1943` and holds the ten `Iso`-field
entries spread across the RadixAlphabets/Run group, not "at `:1922-1946`".

**Arithmetic:**

```
143 + 18 = 161    150 + 11 = 161    ✓ sum closes both ways
11 − 18 = −7      150 − 143 = +7    ✓ delta consistent
definitionSurfaceAllowlist entries (grep): 11   ✓
```

**Verdict:** numeric claim **confirmed**; the file-line reference is wrong (fold into S-1).

---

### S-3 — §3.3's mutation results are named-theorem claims measured as raw error counts

**Location:** `tasks.md:661-668`
**Claim:** "Seven theorems, seven mutations. … base 2 / 4 / 8 / 16 / 10 → **3 errors** each; base
32 → **2**; base 64 → **4**. Working tree restored after each; `git status --porcelain` empty."
**Truth / assessment:** these are **single-run observations from one session** with no committed
log, no captured compiler output, and no named theorem in the failure. They are **not
reproducible claims** by any committed artifact — the only way to confirm is to re-run seven
mutations by hand (each a build). Worse, the _wording_ overstates: "7 theorems, 7 mutations" but
the numbers (3/3/3/3/3/2/4) are **error counts from one build per base**, and a base whose
mutation produced 3 errors is evidence that 3 _dependent_ theorems failed, not that "the tie" was
constrained once. Error counts 3/3/3/3/3/2/4 are also un-summed against the "7" and the spread
(2 vs 4) is unexplained.

**Why this matters:** the `AGENTS.md` rule is "measure the mutation before you believe it", and a
count of compiler errors is one step below that — it does not name _which_ theorem survived or
failed, and a mutation that perturbs digit order in `*_of_toNat` may also break theorems that are
not the tie.

**Correction:** either record the compiler's first error line per base (naming the theorem, as
the 4.1 mutation table does) or downgrade the language to "each base's build failed after the
mutation; error counts were 3/3/3/3/3/2/4, not archived". Do **not** state a bare count as a
reproducible result. _(Unverifiable without re-running seven builds — I did not, per the mandate.)_

---

### S-4 — §5.1c's "53 jobs" and §5.1b's "51 jobs" are unreproducible and cross-contradict a candidate baseline

**Location:** `tasks.md:944` (51 jobs) and `:955` (53 jobs)
**Claim:** `lake build bench` = **51 jobs**; sandboxed `nix build '.#bench'` = **53 jobs**.
**Truth:** no committed artifact records a bench job count for `basen` — `AGENTS.md` in both
repos records only `lake build` numbers (25 → 27 → 28), never a bench count. The only way to
confirm 51/53 is to run both lanes. They are **defensible as a pair** (the sandboxed lane adds
~2 jobs for the derivation phases), but they are **unreproducible one-offs** and the doc presents
them as measured fact.

**Which cell I could not check:** both — `51` and `53`. There is no baseline anywhere to compare
against, and numbers in this repo have been wrong before (`AGENTS.md` "This box has gone stale
twelve times").

**Correction:** either drop the job counts (they prove nothing the "Build completed successfully"
line does not) or add "not cross-checked against any committed baseline; single run 2026-11-15".

---

### S-5 — §6b.3 quotes "68 commits" behind the pin; §0.2 the same doc explicitly refuses to quote it, and the truth is 90

**Location:** `tasks.md:1031` (§6b.3 "a bump would move **68** commits …") vs `:100-103`
(§0.2 "the exact count moves on every commit, so it is **not** quoted here")
**Claim:** "a bump would move 68 commits of unrelated `codec` work".
**Truth:** `git rev-list --count 14b54fa..HEAD` = **90** (the pin is now 90 commits behind;
`14b54fa` is an ancestor of `829c3bb`). §0.2 correctly declines to state this ("a previous draft
said 68, which reproduced at no stable revision: 67 at the authoring commit, 69 and 70 …"), then
§6b.3 re-introduces the very `68` that §0.2 calls unreproducible.

**Arithmetic:**

```
$ git merge-base --is-ancestor 14b54fa HEAD && echo ancestor   → ancestor
$ git rev-list --count 14b54fa..HEAD                          → 90
```

**Correction:** §6b.3 should read "moves ~90 commits" _or_ "moves the whole span between the pin
and HEAD (a count that changes on every commit — never quote it)". As written the doc
contradicts itself and states the retracted figure.

---

## NITPICK

### N-1 — §4.3's per-session deltas (`+7 +8 +13 +3 +7`) do not sum to the actual gate delta

**Location:** `tasks.md:851-854`
**Claim:** "this session's real deltas were `+7` (base 16), `+8` (base 10), `+13` (bases 32/64),
`+3` (radix instances), `+7` (`*BlockIso_apply`)".
**Arithmetic:** `7 + 8 + 13 + 3 + 7 = 38`; the gate moved `601 → 670` = **+69** (or `660 → 670`
gated = +10 across the apply-law step alone). The five figures describe new _theorems per task_,
not pinned-count deltas — but the sentence calls them "real deltas" beside a count that moved by a
different number. There is no stated reconciliation.

**Correction:** state them as "theorems added per task (sum 38)" and give the pinned-count delta
separately (`601 → 670`), or drop the sum's appearance of adding up.

---

### N-2 — §4.1's "607 `#print axioms` blocks / 601 `gatedNames`" is an intermediate state quoted as current

**Location:** `tasks.md:761` (and `:743`, `:924` "all 601 pinned names")
**Claim:** "`grep -c '^#print axioms'` gives **607**; `gatedNames` holds **601**."
**Truth:** at HEAD the counts are **676** blocks and **670** `gatedNames` (measured). The `607/601`
figures were accurate at the _2.2c landing_ (`9d547dd`) and are quoted in §4.1/4.5 as if live.
The 607−601=6 relation is the correct _shape_ (3 `Codec` + 3 `eq_def`); at HEAD it is 676−670=6.

**Correction:** label them "at `9d547dd`" or update to 676/670. (Axioms.lean's own prose at `:1724`
correctly says 676/670 — so the doc and the code disagree.)

**Evidence:**

```
$ grep -c '^#print axioms' Axioms.lean                            → 676
$ sed -n '2901,3572p' Axioms.lean | grep -oE "\`[A-Za-z0-9_.'?]+" | wc -l   → 670
$ comm -23 printed.txt gated.txt   # 3 Codec + 3 eq_def = 6
```

---

### N-3 — §5.1's "653 = 601 + 52 at 28 jobs" is restated after the same task's own 4.3 says the gate ended at 722

**Location:** `tasks.md:936` vs `tasks.md:848`
**Claim:** §5.1's final-build line is "`653 = 601 + 52`, … count rose 27 → 28", but §4.3's line is
"`header numbers verified (722 = 670 + 52)`".
**Truth:** 653 is the _2.2c_ gate; 722 is the _final_ gate. §5.1 is the build verification task
and should quote the last build (722-wide, a larger job count than 28). Presenting 653 as the
outcome of the session's verification is stale by 189 theorems.

**Correction:** §5.1 should reflect the final build (`722 = 670 + 52`, job count re-run), or state
explicitly "this is the 2.2c run; the §3.2 ties raised it further — see 4.3".

---

### N-4 — §4.1's "117 blocks and 117 `gatedNames` entries" omits the 3 `eq_def` blocks it counts elsewhere

**Location:** `tasks.md:739-740` vs `:761`
**Claim:** "**117** `#guard_msgs` blocks and **117** `gatedNames` entries".
**Truth:** the `BaseN.RadixCodec` namespace has **120** `#print axioms` blocks (measured), because
the 3 `eq_def` blocks (`digitTail`/`isDigits`/`strip`) are block-only. That is stated correctly at
`:761` (607 vs 601) but contradicted at `:739` ("117 blocks and 117 entries"). 4.5's footprint
decomposition (84/21/12 = 117) is correct _for the 117 theorems_; the block count is 120.

**Correction:** "117 `gatedNames` entries and 120 `#guard_msgs` blocks (the 3 extra are the
`eq_def` blocks outside `publicTheorems`)".

---

## Refuted / could not confirm

**Refuted (claims I checked that hold):**

- §4.2 "Allowlist 18 → 11, mentioned 143 → 150, `161 = 150 + 11`" — **confirmed**:
  `definitionSurfaceAllowlist` = 11 entries, `expectedDefs/Mentioned/DefAllow = 161/150/11`, all sums close.
- §3.2 "`722 = 670 + 52`" final and "`712 = 660 + 52`" at ties-close — **confirmed** against
  `expectedPub/Gated/Allow` and `git show b29c38c`.
- §4.3 "11 constants in four arms" — **confirmed**: `3 + 2 + 3 + 3 = 11`, matching
  `expectedPub/Gated/Allow`, `statedPrintBlockCount/statedGatedNamesCount`,
  `statedDistPS/P/Z`, `expectedDefs/Mentioned/DefAllow`.
- Cross-repo claim (item 7): **no** `codec` code change was made or claimed. `git diff --name-only
49238a3~1 HEAD` in `lean-codec` touches only `AGENTS.md` and `openspec/**`; `6b.2` explicitly says
  "A `codec` change is not needed". Confirmed correct.
- Toolchains: all three repos pin `leanprover/lean4:v4.35.0`. `lean-toolchain` is read by neither
  `default.nix` nor `flake.nix` (inert, as `AGENTS.md` claims).
- Repo hygiene: `lake-manifest.json` untracked in both repos, `.gitignore` correct, `git status`
  clean, no strays in either tree.
- `basen` `packages.bench` (package) vs `checks.lean` (build check) matches `AGENTS.md`.

**Could not confirm without a fresh build:**

- §5.1c `53 jobs` and §5.1b `51 jobs` (S-4) — no committed baseline exists; would need both lanes
  run on an idle host.
- §3.3's 3/3/3/3/3/2/4 error counts (S-3) — would need the seven mutations re-run.
- The gate itself (`lake build`) — per the mandate I did not run it; every count above is derived
  from the committed `#guard_msgs` blocks, the asserted constants, and `git show`, not from a build.
