# Numbers & Build-Claims Review — `openspec/changes/basen-radix`

Audited: `design.md`, `proposal.md`, `tasks.md`, `specs/basen/spec.md` (delta),
against `/Users/user/_/lean-basen` and `/Users/user/_/lean-codec`. Every figure
below was re-derived by command. No files modified; no `lake build`/`nix build` run.

## Summary

| axis                     | verdict                                                                                                                      |
| ------------------------ | ---------------------------------------------------------------------------------------------------------------------------- |
| A. performance figures   | n/a — this plan commits **no** ns/step figures (correct: it adds no bench row)                                               |
| B. counts                | 5 defects (2 MUST, 2 SHOULD, 1 NITPICK)                                                                                      |
| C. build claims          | 2 defects (1 MUST, 1 SHOULD) — `490=444+46`, `25 jobs`, `native_decide 12` all reproduce; the two-repo §0.5 claim reproduces |
| D. pin / version hygiene | **1 MUST** — "68 commits behind" is stale and never true at any authoring revision                                           |
| E. hygiene               | clean (basen tree clean, branch master, pin checked out)                                                                     |

**7 findings: 3 MUST, 3 SHOULD, 1 NITPICK.** The single most serious is D-1
(the pin is **70** commits behind, not 68) and D-2 (the "`Normal.lean` is identical"
claim, whose _conclusion_ is true but whose _stated method_ is false).

---

## MUST

### M-1 — D0's "no `Nat` codomain except the `digVal` family" is false

**Location:** `design.md:16-17`

> `grep -rn 'radix|base : Nat|pow' BaseN/*.lean` → **nothing.** There is no radix
> parameter anywhere, and no function whose codomain is `Nat` other than the
> single-digit `digVal` family.

**Arithmetic / command:**

```
$ cd /Users/user/_/lean-basen
$ grep -rnE 'def \w+ \(e : Nat\) : Nat' BaseN/*.lean     # the "digVal family"
BaseN/Base2.lean:35:def bitVal (e : Nat) : Nat :=
BaseN/Base4.lean:33:def quartetVal (e : Nat) : Nat :=
BaseN/Base8.lean:40:def octToVal (e : Nat) : Nat :=
BaseN/Base16.lean:43:def hexToNibble (e : Nat) : Nat :=
BaseN/Base32.lean:28:def b32ToVal (e : Nat) : Nat :=
BaseN/Base64.lean:34:def b64ToVal (e : Nat) : Nat :=
BaseN/Base10.lean:45:def digVal (e : Nat) : Nat :=
# but ALSO:
BaseN/Base2.lean:49:def valToBit (b : Nat) : Nat :=
BaseN/Base4.lean:37:def valToQuartet (d : Nat) : Nat := 48 + d
BaseN/Base8.lean:37:def valToOct (d : Nat) : Nat := 48 + d
BaseN/Base32.lean:24:def valToB32 (i : Nat) : Nat :=
BaseN/Base64.lean:26:def valToB64 (i : Nat) : Nat :=
BaseN/Base10.lean:49:def valToDig (d : Nat) : Nat := 48 + d
BaseN/Base16.lean:39:def nibbleToHex (n : Nat) : Nat :=
BaseN/Base2.lean:89:def bitAt (v : Nat) (i : Nat) : Nat := (v / 2 ^ (7 - i)) % 2
```

**Verdict:** FALSE as written. There are **8** more `Nat → Nat` functions outside the
seven-alphabet family (`valToBit`/`valToQuartet`/`valToOct`/`valToDig`/`valToB32`/`valToB64`
/`nibbleToHex`/`bitAt`). They are the _inverse_ (value→digit-char) maps and the per-bit
selector, not numeral folds — so they do not weaken the plan's actual point (no
digit-list→number fold exists).

**Correction:** replace "no function whose codomain is `Nat` other than the single-digit
`digVal` family" with a bounded claim, e.g. "no function folds a _digit list_ to a `Nat`:
`grep -rnE 'def (toNat|ofNat|numeral)\b' BaseN/*.lean` → none, and the only digit-list
folds (`*BlockApply`) land in `Option UInt8`/`Option (List UInt8)`." The un-qualified
universal is the defect; the _conclusion_ (no number layer) is sound.

---

### M-2 — D0's grep pattern is BRE, so `|` is literal; it "proves nothing" only vacuously

**Location:** `design.md:16`

> `grep -rn 'radix|base : Nat|pow' BaseN/*.lean` → **nothing.**

**Command:**

```
$ grep -rn 'radix|base : Nat|pow' BaseN/*.lean ; echo "exit=$?"
exit=1                      # literal string "radix|base : Nat|pow" — matches nothing, ever
$ grep -rnE 'radix'    BaseN/*.lean | wc -l   # 0
$ grep -rnE 'base : Nat' BaseN/*.lean | wc -l # 0
$ grep -rnE 'pow'      BaseN/*.lean | wc -l   # 0
```

**Verdict:** The three alternatives are _genuinely_ absent (each 0 under `-E`), so the
**conclusion holds** — but the command as printed is in basic regex, where `|` is a literal
character. It returns 1 for _any_ file set, so it cannot distinguish "absent" from "present".
A reader reproducing it gets exit 1 regardless of the tree: the command proves nothing.

**Correction:** `grep -rnE 'radix|base : Nat|pow' BaseN/*.lean` (`-E`), or three separate
greps, and paste the three `0` counts. State that the result is 0 for each alternative.

---

### M-3 — "68 commits behind" is stale; the pin is **70** behind, and was **67** at authoring HEAD

**Location:** `design.md` §D? n/a; `tasks.md:35`, `tasks.md:64`; carried unchanged into
`AGENTS.md:44,48`.

> The `codec` pin is `14b54fa` (**68 commits behind** `lean-codec`'s HEAD) …

**Command:**

```
$ cd /Users/user/_/lean-codec
$ git rev-list --count 14b54fa..master
70
$ for c in 10f601f~1 10f601f 45fa6e2 969138d 9a7231f; do
    echo "$c: $(git rev-list --count 14b54fa..$c)"; done
10f601f~1: 66      # before basen-radix was authored
10f601f: 67        # the authoring commit ("openspec: author basen-radix")
45fa6e2: 68        # <-- the 68: a transient mid-sequence state
969138d: 69
9a7231f: 70        # current master HEAD
```

**Verdict:** The number **does not reproduce at any stable revision**. It equals the count
at commit `45fa6e2` only — one of three docs commits that landed _after_ authoring. It is a
remembered/captured figure, now 2 short of reality and 3 short of the authoring HEAD. This is
precisely the recurring "a remembered count" defect `AGENTS.md` itself forbids believing.

**Correction:** replace with "70 commits behind as of `9a7231f`" and say which HEAD the count
is against; or drop the count and keep "the pin predates `Codec/Normal`, which is present
there" (the load-bearing fact). Fix `AGENTS.md:44,48` in the same commit — they carry the
same 68.

---

### M-4 (SHOULD-line, ranked MUST because it is the load-bearing §0.2 claim) — "`Normal.lean` is identical at pin and HEAD" is **false**; only the _conclusion_ survives

**Location:** `tasks.md:35-38` and `tasks.md:62-72` (§0.2)

> **`Codec/Normal` is identical at that pin and at HEAD**, `fill_surj` included.

**Command:**

```
$ cd /Users/user/_/lean-codec
$ git diff --quiet 14b54fa master -- Codec/Normal.lean && echo IDENTICAL || echo DIFFERS
DIFFERS
$ git diff --stat 14b54fa master -- Codec/Normal.lean
 Codec/Normal.lean | 38 +++++++++++++++++++++++++++++---------
 1 file changed, 29 insertions(+), 9 deletions(-)
$ git rev-list --count 14b54fa..master -- Codec/Normal.lean
3
```

The diff is **docstring prose only** (three hunks: a RFC "MUST"/"MAY" correction, a
length-preservation bullet rewrite, and a `decodeNormal` lossy-half rewrite). Every
declaration is unchanged:

```
$ diff <(git show 14b54fa:Codec/Normal.lean | grep -oE '^(theorem|def|structure|class|abbrev) [A-Za-z0-9_.]+') \
       <(git show master:Codec/Normal.lean   | grep -oE '^(theorem|def|structure|class|abbrev) [A-Za-z0-9_.]+')
IDENTICAL DECL NAMES     # 12 declarations, same names and signatures
$ git show 14b54fa:Codec/Normal.lean | grep -A1 'theorem fill_surj'
theorem fill_surj ... (nz : Normalizer S norm) (f : Normal S norm) : fill nz f.raw = f := by
$ git show master:Codec/Normal.lean | grep -A1 'theorem fill_surj'
theorem fill_surj ... (nz : Normalizer S norm) (f : Normal S norm) : fill nz f.raw = f := by
```

**Verdict:** The claim "identical" is **false** (29/9 lines differ). The claim that matters
— "the API this change needs is present at the pin with identical signatures, `fill_surj`
included" — is **true** and reproduced above. This is the exact defect class the repo's
own `AGENTS.md` names: _"a claim whose stated method is not its code's method."_

**Correction:** change "identical at that pin and at HEAD" to "the declarations this change
needs — `Normal`, `Normalizer`, `fill`, `fill_raw`, `fill_fixed`, `fill_surj`, `fill_inj`,
`decodeNormal`, `decodeNormal_of_fixed`, `decodeNormal_encode` — have **identical names and
signatures** at both revisions (verified by diffing the decl lines). The two files differ in
docstring prose only (29 insertions / 9 deletions, from `codec-audit-round-nine` §4), which
does not affect the pin." Re-derive the decl-line diff, not the file diff.

---

## SHOULD

### S-1 — Base 10's `digBlockIso` is a 7th block iso, silently dropped with no stated reason

**Location:** `proposal.md:68,73`; `design.md:128`; `tasks.md:19,191-193`

> The **six** power-of-two block isos (`bitBlockIso`, `quartetBlockIso`, `octBlockIso`,
> `hexBlockIso`, `b32BlockIso`, `b64BlockIso`) are special cases of the generic fold.

**Command:**

```
$ cd /Users/user/_/lean-basen
$ grep -rnE 'def \w*BlockIso\w* *: *Iso' BaseN/*.lean
BaseN/Base2.lean:401:def bitBlockIso     : Iso (List UInt8) UInt8
BaseN/Base4.lean:286:def quartetBlockIso : Iso (List UInt8) UInt8
BaseN/Base8.lean:266:def octBlockIso     : Iso (List UInt8) UInt8
BaseN/Base10.lean:250:def digBlockIso    : Iso (List UInt8) UInt8   <-- base 10
BaseN/Base16.lean:248:def hexBlockIso    : Iso (List UInt8) UInt8
BaseN/Base32.lean:725:def b32BlockIso    : Iso (List UInt8) (List UInt8)
BaseN/Base64.lean:421:def b64BlockIso    : Iso (List UInt8) (List UInt8)
# 7 block isos total; 6 power-of-two + digBlockIso(base 10)
```

`digBlockIso` is a genuine fold-to-value of the same shape — its law is
`digBlockApply cs = some b ↔ digBlockUnapply b = some cs` with the value equation
`digVal d0*100 + digVal d1*10 + digVal d2 = b.toNat` (`BaseN/Base10.lean:57,73`), i.e.
`toNat 10` on a block, exactly what `numeralIso` at radix 10 specialises.

```
$ grep -rniE 'digBlockIso|base ?10.*block|decimal.*block' openspec/changes/basen-radix/
(no output)        # digBlockIso is never mentioned anywhere in the plan
```

**Verdict:** The _exclusion is factually correct_ (base 10 is not power-of-two), but it is
**nowhere justified**. Task 3.2 lists the six and stops; a reader cannot tell whether base 10
was (a) excluded on purpose because its block is decimal not binary, or (b) simply forgotten —
especially since D1/D3 claim the generic fold "is identical across radices", under which
`digBlockIso` _would_ also be a special case needing an equality theorem. This is the
"un-stated exclusion" shape: a silently dropped entry in an enumerated list.

**Correction:** State explicitly in D6 and task 3.2: "There are **seven** block isos; the
six power-of-two ones are proved equal to `toNat b` for `b ∈ {2,4,8,16,32,64}`. `digBlockIso`
(base 10) is **also** a special case and SHALL likewise be proved equal — it folds three
decimal digits to a byte-value; it is excluded from the _power-of-two_ grouping only because
its block is 3 decimal digits, not `k` bits." Then either add `digBlockIso` to 3.2/3.3 or
record, with a reason, why the decimal block is out of scope. An unexplained 6-of-7 list is
a completeness claim that fails silently.

---

### S-2 — `AGENTS.md` says `basen-radix` is `0/29`; the file has **37** checkboxes

**Location:** `AGENTS.md:261`, `AGENTS.md:327`

> `basen-radix` (open, **0/29**) … **in-progress, 0/29, THE NEXT SESSION'S WORK.**

**Command:**

```
$ cd /Users/user/_/lean-codec/openspec/changes/basen-radix
$ grep -cE '^\s*[-*] \[x\]' tasks.md   # done
6
$ grep -cE '^\s*[-*] \[ \]' tasks.md   # todo
31
$ grep -cE '^\s*[-*] \[[x ]\]' tasks.md # total
37
```

**Verdict:** Stale in **both** components. It is not `0/N` — six tasks are `[x]` (§0.1–0.5,
§6.1). And the denominator is 37, not 29. `AGENTS.md`'s own "START HERE" box warns _"It has
named … and undercounted tasks, repeatedly. Believe the command, never this box"_ — and this
is another instance.

**Correction:** update both to `6/37` (or, if only the _unstarted main work_ is meant,
say so — e.g. §1–§7 excluding the measured §0 preconditions). Do not leave `0/29`.

---

### S-3 — tasks.md §1.1 promises "proved-equal" for seven alphabets but §3.1/3.2 enumerate the block isos from `toNat`, a different equality — the two are not reconciled for base 10

**Location:** `tasks.md:114-118` vs `tasks.md:184-193`

`tasks.md:116` says "Prove it [the generic `digitVal`] agrees with each base's existing
alphabet function (`bitVal`,`quartetVal`,`octToVal`,`hexToNibble`,`b32ToVal`,`b64ToVal`,
`digVal`) at that radix" — that is 7 alphabets, including `digVal`. §3.2 then proves only the
**6** block isos equal to `toNat`. So base 10 gets its _alphabet_ proved equal (§1.1) but not
its _block iso_ proved equal (excluded from §3.2). Combined with S-1, a base-10 block-iso
equality is the one rung the plan neither states nor excludes. `tasks.md:118` refers to "D1's
'proved-equal specialisation'", and D1 (`design.md:34-37`) says "**the per-base functions**
become proved-equal specialisations" — plural, unspecified whether block isos or alphabets.

**Verdict:** Ambiguous scope for base 10 and, by extension, for whatever "the per-base
functions" covers. Not a wrong number, but an enumeration whose parts (7 alphabets in §1.1,
6 block isos in §3.2) do not obviously sum to D1's "per-base functions".

**Correction:** In D1 and §3, name the two equality families separately with their counts:
(a) 7 alphabet functions `alphabetFn = digitVal radix` (§1.1); (b) 7 block isos
`blockIso = toNat radix` on a block, or state plainly that base 10's block iso is the
deliberate exception and why.

---

## NITPICK

### N-1 — D0 table lists `b32BlockApply` as "fold … to five bytes" — verify (it is correct, but it is the only fully-specified row)

**Location:** `design.md:12`

```
$ grep -A1 'def b32BlockApply' /Users/user/_/lean-basen/BaseN/Base32.lean
def b32BlockApply (cs : List UInt8) : Option (List UInt8) := …
```

**Verdict:** Correct — 8 base32 chars → 5 bytes is `⌊8·5/8⌋ = 5`. Reproduces. No change
needed; noted because it is the one D0 row whose "why it is not the number" is quantitative
and checks out, unlike `bitBlockApply`/`b64BlockIso` which give only a shape.

---

## Refuted / could not confirm

- **Refuted (claim false):** D0 "no `Nat` codomain other than the `digVal` family" — 8
  counter-examples (M-1). **Refuted:** §0.2 "`Normal.lean` is identical at pin and HEAD" —
  29/9-line diff (M-4). **Refuted (does not reproduce):** "68 commits behind" — 70 at HEAD,
  67 at authoring commit (M-3). **Refuted:** `AGENTS.md` "0/29" — 6/37 (S-2).
- **Confirmed (reproduces):** all seven alphabet functions exist with `Nat → Nat`
  signatures (`design.md:24-25`). `grep -rnE 'radix'` / `'base : Nat'` / `'pow'` are each
  **0** — the _conclusion_ of D0 holds under a correct pattern (M-2 is about the pattern, not
  the conclusion). `490 = 444 + 46` (**490**) reproduces from `Axioms.lean:2742-2744`
  (`expectedPub/expectedGated/expectedAllow`), and `137 = 122 + 15` from `2866-2868`. "12
  `native_decide` uses" reproduces as the gate's _comment-stripped_ count (raw is 18,
  `Axioms.lean:2900-2967` states and verifies 12). "`.lake/packages/codec` is at `14b54fa`"
  reproduces. Toolchains agree (`v4.35.0` both). Delta spec = **3 requirements / 10
  scenarios** (3+4+3), matching "three requirements added" (`proposal.md:104`) and
  `proposal.md`'s three-row Modified-Capabilities list.
- **Could not confirm without a build:** the "`Build completed successfully (25 jobs)`" line
  (tasks.md §0.1). The _gate numbers_ in the same block are confirmable from
  `Axioms.lean`'s `expected*` constants and agree; the **job count 25** is a `lake build`
  output and cannot be re-derived from source without running the build. What would settle
  it: `nix develop --command lake build` in `../lean-basen` and check the final line —
  it is already the plan's own §5.1 baseline, so this is not a new gap, only an
  unverifiable-by-static-audit figure.
- **Could not confirm:** the archived-time provenance of "measured 2026-11-13" — the tree
  itself carries no timestamp proving the date; the `[x]` marks and the `expected*`
  constants are consistent with _some_ green run, but the date is recorded, not re-derivable.
