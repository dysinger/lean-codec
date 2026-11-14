# Second-pass review — the FIXES in `c8f8311`, not the original plan

Scope: `/Users/user/_/lean-codec/openspec/changes/basen-radix/` (design.md, tasks.md,
specs/basen/spec.md, proposal.md) audited against the code they describe in
`/Users/user/_/lean-basen/`. Bash was read-only; no repo file was modified. No Lean file was
compiled (the claims below are all machine-checkable by `grep`/`sed`/Python over source, which
is what each `evidence` row shows).

## Summary counts

| rank    | count |
| ------- | ----- |
| MUST    | 5     |
| SHOULD  | 5     |
| NITPICK | 3     |

Fixes verified **sound**: item 6 (the `valToBit` docstring quote), the `both`-arm mechanism
(item 3), `+7` for `expectedPub`/`expectedGated`, and the `2 ≤ b ≤ 64` bound added to the spec.
Fixes that **introduced a new defect**: items 1, 2 (partly), 4, 5, 7, plus a stale "six" the
fix forgot to sweep.

---

## MUST

### MUST-1 — "seven block-iso entries" is wrong; the fix's own count does not match the list it edits, and three of the ten are silent orphans (tasks.md:266-276)

The user's hypothesis is **confirmed and worse than stated**.

`evidence` — exact enumeration of the allowlist block:

```
$ cd /Users/user/_/lean-basen && python3 … # parse definitionSurfaceAllowlist, 1922-1946
total entries: 15
Iso entries: 10
  1925: BaseN.Base2.bitBlockIso
  1926: BaseN.Base4.quartetBlockIso
  1927: BaseN.Base8.octBlockIso
  1928: BaseN.Base10.digBlockIso
  1929: BaseN.Base16.hexBlockIso
  1930: BaseN.Base16.hexBlockIsoF
  1931: BaseN.Base32.b32BlockIso
  1932: BaseN.Base32.b32TailIso
  1933: BaseN.Base64.b64BlockIso
  1934: BaseN.Base64.b64TailIso
block isos (7 per D6): [bitBlockIso, quartetBlockIso, octBlockIso, digBlockIso, hexBlockIso, b32BlockIso, b64BlockIso]
non-block Iso entries (3): [BaseN.Base16.hexBlockIsoF, BaseN.Base32.b32TailIso, BaseN.Base64.b64TailIso]
```

tasks.md:266 cites the region as `Axioms.lean:1920-1931`, which is _also_ the wrong line range:
the `def` is at **1922**, the ten entries at **1925-1934**, and the whole list closes at
**1946**. The cited `1920-1931` starts before the `def` and ends **three entries early**,
immediately after `b32BlockIso` — i.e. it stops exactly where the four _power-of-two_ block
isos plus `hexBlockIsoF` would have ended had the author been reading the old six-item list.

The three non-block entries are the ones the fix left **silent**, and the plan's own §3.2
generates **no theorem for any of them**:

- `hexBlockIsoF : Iso UInt8 (Normal (List UInt8) foldList)` (`BaseN/Base16.lean:972`) — a
  _normal-form_ value, not a block; §3.2's seven do not include it, so its allowlisted reason
  ("no theorem names it") is still **true** and it must **stay**.
- `b32TailIso : Iso (List UInt8) (List UInt8)` (`BaseN/Base32.lean:1075`) — a tail, which D5
  explicitly excludes from `numeralIso`; §3.2's seven do not include it, so it stays.
- `b64TailIso : Iso (List UInt8) (List UInt8)` (`BaseN/Base64.lean:523`) — same, stays.

**The correct list to remove is exactly the seven:** `Base2.bitBlockIso`,
`Base4.quartetBlockIso`, `Base8.octBlockIso`, `Base10.digBlockIso`, `Base16.hexBlockIso`,
`Base32.b32BlockIso`, `Base64.b64BlockIso` (allowlist lines 1925, 1926, 1927, 1928, 1929,
1931, 1933). **The three to keep** are `hexBlockIsoF`, `b32TailIso`, `b64TailIso` (lines 1930,
1932, 1934), each staying with its current reason.

**Why this is a MUST and not a formatting nit.** "remove the seven block-iso entries" is
satisfied by _three different edits_: remove 7 block isos (correct); remove 7 of the 10 Iso
entries in line order, which would take `bitBlockIso`…`b32BlockIso` and drop `b32BlockIso`'s
successor `b64BlockIso` while deleting `b32TailIso`/`hexBlockIsoF` (wrong, and it would
_un-allowlist_ two defs that still have no theorem — the `silent` arm at Axioms.lean:2852-2855
then fires naming them, so it is caught, but only after the implementer has already made the
edit); or remove "the seven" from a 6-of-10 reading and leave `digBlockIso` stale — the exact
6-of-7 defect D6 claims to have fixed, reintroduced in the task the fix added.

`fix`: replace tasks.md:266-276's "the block isos"/"seven block-iso entries" with the explicit
seven-name list above, and add the counter-list "**keep** `hexBlockIsoF`, `b32TailIso`,
`b64TailIso` — they gain no theorem and their reason stays true", with `Axioms.lean:1922-1946`
as the region. The reason text at `Axioms.lean:1699` already says "10 `Iso`-law-as-field
values", so the task must reconcile 10 → 3, not 10 → "seven removed" with 0 remaining.

### MUST-2 — `valToQuartet`/`valToOct` "have the same shape" as `valToBit` is FALSE (design.md:54, tasks.md:135, spec.md:19-21)

This is the sharpest fix-introduced defect: the fix _added_ the claim while correcting a
different one.

`evidence`:

```
$ grep -n "def valToQuartet" -A1 /Users/user/_/lean-basen/BaseN/Base4.lean
37:def valToQuartet (d : Nat) : Nat := 48 + d
$ grep -n "def valToOct" -A1 /Users/user/_/lean-basen/BaseN/Base8.lean
37:def valToOct (d : Nat) : Nat := 48 + d
$ grep -n "def valToBit" -A1 /Users/user/_/lean-basen/BaseN/Base2.lean
49:def valToBit (b : Nat) : Nat :=
50:  if b = 0 then 48 else 49
```

`48 + d` is **injective**; `if b = 0 then 48 else 49` is not. So the blanket statement is
false of 4 and 8 — only radix 2 has the asymmetric sentinel. It appears three times, and in
`spec.md` it is _normative_ ("SHALL NOT be rewritten"), so a reviewer of the implementation
would be told three encoders are non-injective when two are provably injective.

Consequence the plan misses: because `valToQuartet`/`valToOct` **are** injective, an
`ofNat`-agreement law _is_ provable at 4 and 8 (unlike 2), so "the encode direction at 2/4/8
is NOT unified" over-claims. The safe statement is narrower and still guards the real trap:
only radix 2's `valToBit` carries a deliberate non-injective fallback.

`fix`: in design.md:54 and tasks.md:135 write "**only** `valToBit` (`Base2.lean:49-50`) has
the non-injective sentinel; `valToQuartet` (`Base4.lean:37`) and `valToOct` (`Base8.lean:37`)
are `48 + d` and injective". In spec.md:19-21 restate as "the radix-2 inverse map carries a
deliberately non-injective fallback and SHALL NOT be rewritten; at 4 and 8 the inverse maps
are injective". (Optionally note that `ofNat`-agreement is then _provable_ at 4/8 — a bonus
law, not an obligation.)

### MUST-3 — D6's single `BlockVal` placeholder does not typecheck across the seven blocks; it needs two (or three) statements (design.md:227-232)

`evidence` — the block iso types split exactly two ways:

```
$ grep -n "def bitBlockIso\b\|def b32BlockIso\b\|def b64BlockIso\b\|def digBlockIso\b" BaseN/*.lean
BaseN/Base2.lean:401:def bitBlockIso : Iso (List UInt8) UInt8 :=
BaseN/Base10.lean:250:def digBlockIso : Iso (List UInt8) UInt8 :=
BaseN/Base32.lean:725:def b32BlockIso : Iso (List UInt8) (List UInt8) :=
BaseN/Base64.lean:421:def b64BlockIso : Iso (List UInt8) (List UInt8) :=
```

D6 writes one statement pair with a single placeholder type `BlockVal` in both the
`blockApply cs = some (blockValOf n)` consequent and the `(v : BlockVal)` binder. For base 2
`blockApply : List UInt8 → Option UInt8`, so `blockValOf n : UInt8`; for base 64
`blockApply : List UInt8 → Option (List UInt8)`, so `blockValOf n : List UInt8`. A **single**
`BlockVal` cannot be both, so as written the pair is not a schema — it is unifiable only by
reading `BlockVal` as a metavariable, and a literal transcription fails to elaborate for at
least one base.

The plan is coherent with **two** instantiations, not one: (i) the `UInt8`-valued bases
(`bitBlockIso`, `quartetBlockIso`, `octBlockIso`, `digBlockIso`, `hexBlockIso`) where
`blockValOf n = UInt8.ofNat n` and losslessness needs the block's own `n < 256` guard; (ii) the
list-valued bases (`b32BlockIso`, `b64BlockIso`) where `blockValOf` is the byte-list
reconstruction (and for b64 the re-encode guard, not `n < 256`, is what makes `→` hold).

`fix`: in design.md:227-232 replace the single `BlockVal` schema with two named schemas —
`blockApply8_of_toNat`/`toNat_of_blockApply8` over `Option UInt8` (truncation guard) and
`blockApplyL_of_toNat`/`toNat_of_blockApplyL` over `Option (List UInt8)` (re-encode guard) —
and say which of the seven uses which. At minimum, say explicitly that `BlockVal` is a
_type family_ indexed by the iso, and that there are two instantiations.

### MUST-4 — The `native_decide`/`sorry` posture claim in the fix's own commit message is not a check; the plan never states the greps (tasks.md §4)

Item D of the brief asks for the greps to be stated. The plan's §4 (tasks.md:246-300) asserts
the gate's four arms and the 11 constants but **nowhere** states the two global greps
(`native_decide` reach, `sorry` presence), while the commit message that motivates the change
is silent on whether they were re-measured after the edits. For a change that adds a new
`BaseN/Radix.lean` and ~7+ theorems, the absence of a stated zero-`sorry`/zero-`native_decide`
posture is a missing gate obligation, not prose.

`evidence` (measured now, read-only, `../lean-basen`):

```
$ grep -rn "native_decide" --include=*.lean BaseN/ | wc -l
       0
$ grep -rln "native_decide" --include=*.lean .            # Axioms.lean, Bench.lean (+ .lake/…/codec, not source)
Axioms.lean
Bench.lean
.lake/packages/codec/Axioms.lean

$ grep -rn "\bsorry\b" --include=*.lean BaseN/ Axioms.lean
BaseN/Base64.lean:15:`< 256`.  `[propext, Quot.sound]`-only, zero `sorry`.
BaseN/Base32.lean:13:`< 256`.  `[propext, Quot.sound]`-only, zero `sorry`.
BaseN/Base32.lean:3655:`[propext, Quot.sound]`-only, zero `sorry`:
```

So the posture holds **today**: `native_decide` appears only in `Axioms.lean` (the ban prose
at `:12` and the count-assertion block) and `Bench.lean` (the 12 bench-lane uses asserted at
Axioms.lean:2905), and all three `sorry` hits are docstring _prose_, not terms. That is the
measured baseline the new module must not break — and the reason the greps belong in the task
list rather than in a reviewer's head.

`fix`: add one task under §4 that names the two greps verbatim and requires them to hold for
`BaseN/Radix.lean` and the new theorems before pinning:
`grep -rn 'native_decide' --include=*.lean BaseN/ ../lean-basen/BaseN/Radix.lean` → 0 (the
bench lane is the sole sanctioned site), and `grep -rn '\bsorry\b' --include=*.lean BaseN/
Axioms.lean` must return **only docstring mentions** — today three, all the phrase "zero
`sorry`" at `BaseN/Base64.lean:15`, `BaseN/Base32.lean:13` and `:3655` — so the task must say
"no `sorry` _term_", not "no match", or the third hit reads as a failure forever. (The
benchmark's 12 `native_decide` are already asserted at Axioms.lean:2905 and stay.)

### MUST-5 — The spec's "at radices 2, 4 and 8" is a normative falsehood carried by the fix (spec.md:19-21)

The same MUST-2 falsehood, promoted to a **requirement** in the delta. Because a MODIFIED
requirement replaces the live block wholesale, landing this spec delta writes the false
"2, 4 and 8" claim into `openspec/specs/basen/spec.md` permanently, and `openspec validate`
cannot see it (it checks structure, not truth).

`evidence` — `git show c8f8311 -- specs/basen/spec.md` inserts:

```
+function at their radix. **The encode direction is not unified**: at radices 2, 4 and 8 the
+existing inverse maps carry deliberately non-injective fallbacks and SHALL NOT be
+rewritten.
```

Combined with MUST-2's measurement (`valToQuartet d = 48 + d`, `valToOct d = 48 + d`), the
requirement misstates the code it governs.

`fix`: as MUST-2 but in the spec, and add the reason "only radix 2's `valToBit` is the
non-injective one" so no future reader re-generalises it to 4/8.

---

## SHOULD

### SHOULD-1 — Task 4.3's worked example conflates "7 theorem equalities" with the D6 implication pair; `expectedPub +7`/`expectedGated +7` are right, `expectedMentioned +7`/`expectedDefAllow -7` are right _only if_ the seven defs are truly named, and "one bucket of the footprint +7" is a quadruple-count (tasks.md:293-296)

The user's item 2 asks each delta to be re-derived. Measured, the four deltas split three ways:

1. `expectedPub +7`, `expectedGated +7` — **correct**, _provided_ 3.2 adds exactly 7 new
   public BaseN theorems and they are pinned in `gatedNames`. Note that the existing
   `*_law` theorems (`bitBlockIso_law` etc., already gated at Axioms.lean:714-716 etc.) are
   _different_ theorems; 3.2's new pair is _additional_. So `+7` is right only if you count
   **new** names, not the existing `_law` names. The example's phrase "7 theorem equalities"
   is the _wrong noun_ — D6's statement is an implication pair, and each base may need 2
   theorems, so the true delta could be `+14` not `+7`. This is a MUST-grade ambiguity wearing
   a SHOULD because the example itself says "these are the shape, not the numbers".
2. `expectedMentioned +7`, `expectedDefAllow -7` — **mechanically correct**, because the arm
   computes `mentionedCount := defs.size - definitionSurfaceAllowlist.size` (Axioms.lean:2858),
   i.e. a subtraction, so removing 7 allowlist entries yields `expectedDefAllow -7` and
   `expectedMentioned +7` _automatically_, but **only if** the seven `def`s become genuinely
   mentioned (`mentionedByGated`, Axioms.lean:1893, walks `ti.type.getUsedConstants` of
   `gatedTheorems`). If a 3.2 theorem names `bitBlockApply` instead of `bitBlockIso` — the
   `both`-arm's whole point — the seven are **not** mentioned, and the `silent` arm at
   Axioms.lean:2852 fires naming them. So the example's `-7/+7` presupposes that the theorem
   statements _name the iso values_, which is the one thing the `both` arm exists to verify.
   The worked example should say so.
3. "one bucket of the footprint distribution +7" — **mis-stated**. The footprint split is
   _three_ buckets plus an "other" guard: `statedDistPS` (381) / `statedDistP` (48) /
   `statedDistZ` (15), with `distOther = 0` (Axioms.lean:2817-2828). New law-family theorems
   will land in `distPS` (the `[propext, Quot.sound]` bucket) _individually_, and the
   distribution's sum check is `distPS + distP + distZ == baseNPins` (Axioms.lean:2830). So
   the delta is `statedDistPS +7` **and** `statedGatedNamesCount +7` and
   `statedPrintBlockCount +7` (if a `#print axioms` block is added per theorem) — the example
   names only one bucket. Because the plan's own rule (tasks.md:296) says "do not copy these
   deltas forward", the SHOULD is that the example names _which_ bucket (PS) and notes the
   other two constants move with it.

`fix`: replace tasks.md:293-296 with: "7 **new** block-iso theorems (not the existing
`*_law` ones; each base contributes 1 or 2 per the D6 pair — count against the build) change
`expectedPub`, `expectedGated`, `statedGatedNamesCount`, `statedPrintBlockCount`, and
`statedDistPS` together by exactly the number of new pinned theorems, and move
`expectedDefAllow` by minus the same count **only if** each theorem's statement names its iso
value, else the `both` arm is silent and the `silent` arm names it." Re-derive from `lake
build`, never copy.

### SHOULD-2 — Task 4.2's instruction conflicts with nothing _only because_ the three kept entries are correctly silent; the fix does not say which entries are kept (tasks.md:266-276)

The user's item 3 asks whether a tail iso keeping its allowlist entry _and_ gaining no theorem
is fine. **Measured: yes, fine, and it is what Axioms.lean already enforces.** The `both`
branch (Axioms.lean:2860-2863) filters `defs` where `mentioned.contains n && allow.contains n`;
an iso that is allowlisted and _not_ mentioned is in `silent`'s complement, not `both`, so it
passes. The `stale` branch (Axioms.lean:2849-2853) requires every allowlist entry to still name
a real `def`; `hexBlockIsoF`/`b32TailIso`/`b64TailIso` do, so they pass. So keeping them is
correct — **but only if the fix's own §3.2 does not name them**, and §3.2 names exactly the
seven block isos, not the three. That is the intended split.

The defect is that tasks.md:266-276 says "remove the seven block-iso entries" without saying
which seven _stay_, so a reader applying MUST-1's ambiguity can remove 7 _of the 10 in line
order_ and then the `silent` arm fires on the two deleted tails — the arm "doing its job", but
the implementer has burned a build on the plan's own wording.

`fix`: state the keep-set inline (see MUST-1) and note explicitly that a silent allowlisted
iso passes both the `both` and `stale` arms, citing Axioms.lean:2860 and 2849.

### SHOULD-3 — D6's table row for base 32 is wrong about _where_ the pad check sits, and the citation range does not contain the function it describes (design.md:219)

`evidence`:

```
$ grep -n "def b32BlockDecodeLenient\|def b32BlockApply" BaseN/Base32.lean
366:def b32BlockDecodeLenient (cs : List UInt8) : Option (List UInt8) :=
415:def b32BlockApply (cs : List UInt8) : Option (List UInt8) :=
$ sed -n '366,369p' BaseN/Base32.lean
def b32BlockDecodeLenient (cs : List UInt8) : Option (List UInt8) :=
  match cs with
  | [c0, c1, c2, c3, c4, c5, c6, c7] =>
      if c0.toNat = 61 || c1.toNat = 61 then none
```

D6's base-32 row says "the lenient decoder checks for the pad byte `61` **in its second
digit**" and cites `Base32.lean:413-435`. The check is `c0.toNat = 61 || c1.toNat = 61` at
**line 368** — i.e. in the **first and second** digits, not only the second. The cited range
413-435 starts at `b32BlockApply`'s doc comment, not in `b32BlockDecodeLenient` (366-412), so
the citation points at the wrong function as well as the wrong digit.

`fix`: change design.md's base-32 row to "checks the pad byte `61` in the first two digits"
and the citation to `BaseN/Base32.lean:366-412` (or `:368`).

### SHOULD-4 — tasks.md:22 still says "The six block-iso equalities" — the fix's own headline number is left stale in the file's banner (tasks.md:17,22,201)

`evidence`:

```
$ grep -n "six block-iso\|proved equal\|seven block" openspec/changes/basen-radix/tasks.md
17:> kept and proved equal** (D6).
22:> **The first task to do is 3.2 as a spike.** The six block-iso equalities are the risk
201:## 3. [M] The seven radices, and the block isos proved equal
```

Line 22 says "six" — the exact number the fix corrected to seven in §3.1/§3.2 — and both
lines 17 and 201 still say "proved equal", the phrase D6 (design.md:249) explicitly retracts
("And the equality is not 'proved equal' in the `=` sense — that phrasing invites an
`rfl`-shaped attempt that will not close"). So the fix updated the task bodies but left the
banner and section heading asserting the _pre-fix_ design. This is precisely the "a fix is the
most likely source of the next drift" failure, in the same file, one screen above the fix.

`fix`: tasks.md:17 → "kept and tied to the fold by a theorem (D6)"; :22 → "The seven
block-iso implication pairs are the risk sink"; :201 → "The seven radices, and the block isos
tied to the fold".

### SHOULD-5 — D4's replacement reasons misquote the standards they lean on (design.md:154-156)

Item 5. Measured against the standards as cited, in order:

- "JSON has no empty number token" — **correct** (RFC 8259 number = `[ minus ] int [ frac ]
[ exp ]`, and `int` is a digit, `-` optional). No defect.
- "YAML 1.1's `!!int` is `[-+]?[0-9]+`" — **incorrect as stated**. The YAML 1.1 `!!int` tag
  resolves several forms: base-60 (`190:20:30`), octal (`0o14`/`014`), hex (`0xC`), binary
  (`0b1010`), and the decimal form permits underscores (`1_000`) and a leading `0`. The regex
  `[-+]?[0-9]+` is the _simplification_ of the plain base-10 case only; it also rejects the
  RFC-style `+`, and it misleads by omitting the other radixes that a base-10 numeral layer
  cares about.
- "ISO 8601 requires at least one digit" — **correct in spirit** (a date/time stamp requires
  `YYYY-MM-DD` with no empty fields), and no better statement is needed for the argument.

The YAML misquote is a real defect because this repo treats a misquoted standard as a MUST
elsewhere (the RFC 4648 MAY-vs-MUST case is in `basen-uppercase-prepass`); here it is a
supporting reason, so a SHOULD.

`fix`: weaken the YAML citation to "YAML's `!!int` is not a single decimal regex — it carries
base-60/octal/hex/binary forms and underscores — but every form requires at least one digit",
or drop YAML from the list and keep JSON + ISO 8601, which are the two the argument actually
needs. Do not state a regex the spec does not use.

---

## NITPICK

### NITPICK-1 — Task 4.2's cited line range `Axioms.lean:1920-1931` does not contain the list (tasks.md:266)

`evidence`: the `def definitionSurfaceAllowlist` is at **1922**, the ten entries at
**1925-1934**, `]` at **1946**. The cited `1920-1931` starts above the `def` and stops after
`b32BlockIso` (1931), missing `b32TailIso`, `b64BlockIso`, `b64TailIso` and the seven help/
`Run` entries below. Fix: cite `1922-1946`.

### NITPICK-2 — Task 4.3's "header prose tables they mirror (`:1655-1700`)" off by the table heading (tasks.md:289)

`evidence`: `grep -n "universe, as measured" Axioms.lean` → **1661** (the `###` heading). The
`1655-1700` range includes the heading region but starts 6 lines early; harmless, but a
citation should start at its target. Fix: `:1661-1700`.

### NITPICK-3 — `proposal.md` still says "proved equal" (proposal.md:93,126) while D6 retracts the word (design.md:249)

`evidence`:

```
$ grep -n "proved equal" openspec/changes/basen-radix/proposal.md
93:  and that the block isos are proved equal to the generic fold rather than independent
126:- **Replacing the block isos.** They are kept and proved equal.
```

The proposal is the _first_ artifact a reader hits; it advertises the design D6 says was
"wrong in a way that made task 3.2 unprovable". The fix edited design/tasks/spec but not the
proposal. Fix: change both to "tied to the fold by a canonicity-filtered implication (D6)".

---

## Refuted / could not confirm

- **Refuted — item 6** (the `valToBit` docstring quote). design.md:52-54's quote "Do not 'fix'
  one sentinel to match the other" **is** present verbatim at
  `/Users/user/_/lean-basen/BaseN/Base2.lean:47` (`Do not "fix" one sentinel to match the
other: ...`), and the design's `:49-50` for `valToBit` is exact (`def valToBit` at 49, the
  `if b = 0 then 48 else 49` at 50), and `:40-48` covers the docstring body. The only defect in
  that paragraph is the _sibling_ claim about `valToQuartet`/`valToOct` (MUST-2), not the quote
  itself. **This claim checks out.**
- **Confirmed sound — item 3** (the `both` arm vs a kept tail iso). A tail iso that is
  allowlisted and un-mentioned passes both the `both` branch (Axioms.lean:2860,
  `mentioned.contains n && allow.contains n`) and the `stale` branch (Axioms.lean:2849,
  `!defs.contains n`). So keeping `hexBlockIsoF`/`b32TailIso`/`b64TailIso` is **fine** — but
  tasks.md does not say so (SHOULD-2).
- **Partially confirmed — item 2**. `expectedPub +7` and `expectedGated +7` are right for
  _new_ theorems; `expectedMentioned +7` and `expectedDefAllow -7` are arithmetically forced
  by `mentionedCount := defs.size - allow.size` (Axioms.lean:2858) but _semantically_ depend
  on the theorems naming the iso values. "One bucket of the footprint +7" is wrong: three
  constants (PS + two header-count constants) move (SHOULD-1).
- **Could not confirm — the three non-block Iso entries' §3.2 coverage**. §3.2 (tasks.md:208-217)
  enumerates "each of the seven bases … its block iso"; the seven names are the block isos
  only. No task in the file generates a theorem for `hexBlockIsoF`, `b32TailIso`, or
  `b64TailIso`, so their allowlist entries are correctly kept (MUST-1). This is a measurement
  of the _plan text_, not of a build; I did not run `lake build` (forbidden) so I did not
  observe the `silent`/`both` arms firing — the line numbers and predicate bodies above are
  read from source.
- **Could not confirm — item 7's "exactly seven"** in tasks.md:201/208. `ls BaseN/` shows seven
  `BaseN/*.lean` base modules (Base2/4/8/10/16/32/64) plus Common, so "seven radices" is
  correct. `hexBlockIsoF` **is** an `Iso (UInt8) (Normal …)` (Base16.lean:972), not a block,
  and it does **not** need a §3.2 theorem — but the plan never says why, so a reader can
  reasonably conclude it was dropped like `digBlockIso` was (MUST-1's keep-set sentence fixes
  this).
- **UNVERIFIED — the YAML 1.1 `!!int` regex claim** (design.md:155). I have no copy of the
  YAML 1.1 spec in this repo and did not fetch one; the claim is recall-based. It is written
  as a MUST-adjacent citation and should be weakened or dropped regardless (SHOULD-5).
