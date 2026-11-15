# Audit — do `basen-radix` and the Lean tree describe PAPER.md / README.md truthfully?

Scope: `openspec/changes/basen-radix/{specs/basen/spec.md, design.md, proposal.md, tasks.md}`,
`README.md` (Departures / Strengthenings), `PAPER.md`, and the landed code in
`/Users/user/_/lean-basen` (`11b67b9…bae490a` + `cd1a371`/`4e85200`).

Method: every factual claim below is from a command I ran in this session. Bash was used
read-only; the only writes were `/tmp/probe*.lean` and this report. `lake build` was **not**
re-run for the tree (the gate's own lines were read from a `lake build` executed earlier in
the session and are quoted where relevant); every Lean measurement is
`nix develop --command lake env lean /tmp/probeN.lean`.

## Summary counts

| rank    | n   |
| ------- | --- |
| MUST    | 5   |
| SHOULD  | 7   |
| NITPICK | 5   |

Three of the four questions you asked land, two of them as MUSTs:
**Q3 is confirmed and definitional** (the spec states a falsehood about the shipped `toNat`),
**Q5 is confirmed as a genuine specification gap** (nothing in the spec or the plan states the
`_L` ties' pad-free restriction; the `_8` ties restrict differently and equally unstated), and
**Q1 is confirmed as an unstated precondition** but is a _narrow_ wording defect, not a
soundness one. **Q2 is confirmed** — the paper's sentence is narrower than the use made of it,
and the README's departure list does not mention this change at all.

Two findings are **worse than the questions anticipated** and are the ones I would fix first:
**M-4** (the spec's completeness claim for `×BlockApply` is contradicted by an 8-character
exemplar I ran, and there is no theorem in the tree that constrains 1-/2-byte block results)
and **M-5** (the paper's `element` passage shows the paper _rejects_ the unsound spelling of
the law and _retreats_ to an `Eq`-quotient on a typeclass it takes as a parameter; the plan's
claim that "the paper licenses the quotient, so this adds no departure" is therefore an
over-read of the very sentence it cites).

---

# MUST

## M-1 — the spec asserts `toNat b [] = none`; the shipped function returns `some 0`, definitionally

**Location.** `openspec/changes/basen-radix/specs/basen/spec.md:25-27` (requirement
"A numeral denotes a number"), against `../lean-basen/BaseN/Radix.lean:157-162`.

**Claim as written** (`spec.md:25-27`, verbatim from `awk 'NR>=24 && NR<=28'`):

> The empty sequence SHALL NOT be the canonical spelling of zero at any radix: `ofNat b 0` is
> the base's single zero digit, so `toNat b []` is `none` and `toNat b` of the zero digit is
> `some 0`.

**Truth.** `toNat`'s base case is `some 0`; the spec's _conclusion_ is not merely unproved, it
is definitionally false. `BaseN/Radix.lean:162` is the arm `| [] => some 0`, and
`RadixCodec.lean:1653` already carries the docstring sentence "`toNat b [] = some 0` is a
by-product of the fold's base case". So the code and the spec disagree, and the code's own
docstrings say so three times (`Radix.lean:153`; `RadixCodec.lean:1440`, `:1455`, `:1868`,
`:1900`).

**Command + output.**

```
$ cat /tmp/probe14.lean
#eval (BaseN.Radix.toNat 10 [] : Option Nat)
theorem probe : BaseN.Radix.toNat 10 [] = none := rfl   -- expected to fail
$ nix develop --command lake env lean /tmp/probe14.lean
some 0
/tmp/probe14.lean:9:0: error: Not a definitional equality: the left-hand side
  Radix.toNat 10 []
is not definitionally equal to the right-hand side
  none
```

and `#eval (toNat 2 [] : Option Nat)` → `some 0`.

**Verdict: MUST.** This is the audit's "a spec requirement states a falsehood about the
shipped function" case. OpenSpec's own vocabulary makes it worse than a doc defect: the
requirement text of an ADDED requirement is normative, and after archive it becomes the live
`openspec/specs/basen/spec.md`.

**Exact correction.** Text →

> The empty sequence is **not** the canonical spelling of zero at any radix (`ofNat b 0` is the
> base's single zero digit), but `toNat` is a fold and its base case is `some 0`: **`toNat b
[] = some 0`**. Nothing in this layer treats `[]` as a numeral — `trimFor b [] = none`,
> `isNumeral b [] = false`, and every `Iso` path goes through `trimFor` — so the admission of
> `[]` by the fold is a by-product, not a convention.

Before archiving (see S-7): this text must be corrected in the delta, not after the sync.

---

## M-2 — the spec's completeness claim for the block isomorphisms is _false_ as stated, and no theorem in the tree covers the case it excludes

**Location.** `openspec/changes/basen-radix/specs/basen/spec.md:127-129` and `:35-39`, against
`../lean-basen/BaseN/Base64.lean:230-270`, `Base32.lean:214-232`, `RadixTie.lean:977-987`,
`:1080-1087`.

**Claim as written** (`spec.md:127-129`, from `awk 'NR>=127 && NR<=129'`):

> The rejection law SHALL state the **complete** characterisation, not merely a sufficient
> condition: for bases 8 and 10 a block succeeds **exactly when** its value is at most `255`,
> which makes the rejection law an iff about the block's domain rather than one half of it.

and (`spec.md:35-39`):

> **THEN** it is proved equal to the generic function at that radix, so no base carries an
> independent alphabet definition that could disagree with the generic one.

**Truth (two separate facts, both measured).**

1. The iff _is_ true for bases 8 and 10 — I re-verified it exhaustively rather than trusting
   the docstring, because the last review (`reviews/paper-adherence.md` Q1) found this class
   of claim stated three contradictory ways:

   ```
   $ nix develop --command lake env lean /tmp/probe2.lean
   true    -- base 8: (List.range 8)^3, octBlockApply ds isSome  ==  value ds <= 255
   true    -- base 10: (List.range 10)^3, digBlockApply ds isSome  ==  value ds <= 255
   ```

   So this half of the sentence survives. **But no theorem in the tree states it as an iff.**
   `octBlockApply_overflow` (`RadixTie.lean:514`) and `digBlockApply_overflow` (`:770`) are
   _one direction each_ with three alphabet hypotheses; the converse is
   `octBlockApply_of_toNat` (`:476`) with `n ≤ 255` as a hypothesis. `#print axioms` says all
   three are `[propext, Quot.sound]` — clean, and **none of them is an iff**. The requirement
   says the law "SHALL state the complete characterisation … an iff"; the tree states two
   implications and asserts the iff in a docstring (`RadixTie.lean:767-769`: "So this is a
   complete characterisation"). That is a docstring claim the gate does not enforce, which is
   the exact defect class this repo has closed six times.

2. **The "successful block ⇒ numeral" direction is false for 32/64 outside the full block.**
   `b64BlockUnapply` (`Base64.lean:231-236`) and `b32BlockUnapply` (`Base32.lean:215-231`)
   accept 1–5 bytes and emit a _padded_ character block; `b64BlockApply`/`b32BlockApply` accept
   those back. The `←` ties are stated **only** at the 3-byte and 5-byte vectors
   (`RadixTie.lean:977`, `:1080`) because `=` is outside the fold's alphabet. Measured on the
   canonical 1-byte block:
   ```
   $ nix develop --command lake env lean /tmp/probe3.lean
   some [102]   -- Base64.b64BlockApply [90,103,61,61]      ("Zg==")
   none         -- Radix.toNat 64 [90,103,61,61]
   some [102]   -- Base32.b32BlockApply [77,89,61,61,61,61,61,61]   ("MY======")
   none         -- Radix.toNat 32 [77,89,61,61,61,61,61,61]
   ```
   So for bases 32 and 64 a **block succeeds on input the generic fold cannot read at all**, on
   the ordinary short-tail case, not only on the "`MZ======` rejects a pad byte" case D6 names.
   `spec.md:38-39` therefore reads as a completeness claim ("no base carries an independent
   alphabet definition that could disagree") that is false at 32/64 for the tail arities, and
   nothing in `RadixTie.lean` constrains `b64BlockApply`/`b32BlockApply` on a 1- or 2-element
   result. (It is constrained on _arity_: `b64BlockUnapply` returns `none` off `[..]`,`[..]`,
   `[..]` — but that is an internal invariant, not a theorem stated anywhere I could find:
   `grep -n "theorem .*b64BlockApply" BaseN/RadixTie.lean` yields only the three-vector ties.)

**Verdict: MUST** for (2) — the spec's completeness sentence is false of the shipped block
isos at 32/64, and the gap is a _stated-in-prose-only_ restriction that S-1 shows is not
written anywhere normative. **SHOULD** for (1) — the iff is true but unproved.

**Exact correction.** In `spec.md:38-39`, replace the trailing clause with:

> …so no base carries an independent alphabet definition that could disagree with the generic
> one — **within the alphabet**. Bases 32 and 64 are _not_ an exception to this: their block
> decoders additionally accept the pad byte `=`, which is not a digit, so on a short-tail
> block the block decoder succeeds where the fold returns `none`. That is a property of the
> padding, not of the alphabet, and the tie requirement scopes itself to pad-free blocks.

In `spec.md:127-129`, either (a) state the iff _as a theorem_ —
`(octBlockApply ds).isSome = true ↔ ∃ d0 d1 d2, ds = [d0,d1,d2] ∧ value ≤ 255` — and pin it, or
(b) delete "complete characterisation … an iff" and keep the honest sentence: "the rejection
is a named law in the fold-to-block direction and the converse is the domain hypothesis; the
two together characterise the block's domain, and the docstring at each law says so."

---

## M-3 — the `_L` (bases 32/64) ties cover only the pad-free block; neither the spec nor the plan states that restriction, and `tasks.md` says the opposite

**Location.** `spec.md:105-110` and `:170-174` (vs. `tasks.md:600-640`,
`tasks.md:690-700`), `CHANGELOG.md:28-31`, against `RadixTie.lean:977-987`, `:1080-1087`.

**Claim as written** (`spec.md:105-110`):

> **Both directions SHALL be stated at the block's own arity** — its literal digit vector —
> and not over an arbitrary `List UInt8`. At the literal arity the arity condition is not
> hypotheses to discharge but part of the statement, and an implementation that states it over
> an arbitrary list SHALL add the length condition explicitly.

and the scoping clause the spec offers at `:134-138`:

> The generic fold SHALL NOT be applied across the padded bases' terminal-tail layer: base 32
> and base 64 encode a length class there, and a minimal-width numeral has none. The theorems
> covered by this requirement are over the block layer only.

**Truth.** The requirement is satisfied _literally_ — the ties name literal vectors
(`[d0,…,d7]`, `[d0,d1,d2]`, the 8-character base-32 vector). But **`←` for 32/64 is stated
only at the 5-byte and 3-byte vectors**, so "both directions … at the block's own arity" holds
for **one of that base's arities**. The base-32 block has four arities (1–5 bytes →
8,7,5,4 alphabet characters + padding) and the fold can read only the 5-byte one.

The spec's only nearby scoping sentence is `:134-138`, and it is about the **terminal-tail
layer** — the `B32`/`B64` spine — not about the _block_'s short-arity cases. A reader of the
delta therefore reads "the block isomorphisms [all seven] are tied to the generic fold" and
"both directions at the block's own arity", and has no text telling them that two of the seven
are tied on **one arity out of four**, and that a padded block is _outside the fold's domain_
rather than rejected by it.

`tasks.md` is explicit that the plan knew this — `:600-608`:

> So the tie is **`toNat b cs = some (beVal bs) ↔ blockApply cs = some bs`**, stated at each
> block's literal arity and **on pad-free vectors only**. … it is why the `←` direction is
> stated for the 3-byte (base 64) and 5-byte (base 32) blocks only.

and `CHANGELOG.md:28-31` says it. **The spec delta — the artifact that becomes the live
requirement — does not.** That is the "a fix lands in the ledger but not in the spec" shape.

**Verdict: MUST** (scope gap in a normative artifact, confirmed by the plan and the changelog
both knowing more than the spec says).

**Exact correction.** Add to `spec.md`'s tie requirement, after `:110`:

> For bases 32 and 64 this is necessarily narrowed further: a short-tail block carries the pad
> byte `=`, which is not a digit, so the fold has no value for it and the block-to-fold
> direction is stated only at the **pad-free** arity (5 bytes for base 32, 3 for base 64). A
> padded block is _outside the fold's domain_, not rejected by it; the distinction matters
> because it means no theorem constrains `b32BlockApply`/`b64BlockApply`'s short-tail results,
> and this requirement does not claim one.

---

## M-4 — `design.md` refuses a `[Dn]` on the strength of a misreading of the paper, and the change _is_ an observable-semantics change by README's own definition

**Location.** `openspec/changes/basen-radix/design.md:320-323`; `tasks.md:651-655`;
`README.md:67-69` (the departure definition), `README.md:1010-1017`; `PAPER.md:266-273` and
`:779-791`.

**Claim as written** (`design.md:320-323`):

> `PAPER.md` also licenses the quotient this change already relies on, in the sentence after the
> law — _"we will sometimes interpret this condition modulo equivalence classes"_ — and its own
> worked example (all blank strings in one class) is the `Normal` shape D2 uses. So neither the
> implication pair nor the quotient is a departure from the paper; both are the paper's own
> text. `README.md`'s rule is that every _observable-semantics_ change is filed as a `[Dn]`
> anchor, and this resolution adds none.

and `tasks.md:651-655` repeats it verbatim as a landed conclusion.

**Truth — three separate measurements.**

1. **The quotation is accurate.** `PAPER.md:266-273` reads, from `awk 'NR>=266 && NR<=273'`:
   "We will generally not be very strict with the invariant stated above (if f a returns Just
   b, g b returns Just a, and the other way around). In particular we will sometimes interpret
   this condition modulo equivalence classes. A typical example from our domain is that a
   partial isomorphism maps strings of blanks of arbitrary length to a unit value but maps the
   unit value back to a string of blanks of length one—that is, all strings of blanks of
   arbitrary length are in the same equivalence class." So the sentence exists and says what
   is quoted. **No defect in the quotation.**

2. **But the surrounding text shows the paper doing something the plan does not describe.**
   `PAPER.md:779-791` (`element x`, quoted from `awk 'NR>=783 && NR<=791'`) says the
   isomorphism is "only up to the equivalence class **defined by the Eq instance**", and its
   type is `element :: Eq α ⇒ α → Iso () α` — **the quotient is a typeclass parameter of the
   constructor.** The paper does not say "the law holds modulo `~`" and leave it at that; it
   says the _value_ is not a strict `Iso` and supplies the `Eq` that decides the class. And
   `codec`'s `Normal` quotient is not that: `Normal S norm` fixes a _canonical
   representative_ in the codomain. The two devices are cousins, not the same device — the
   paper's is a quotient on the _type_, `codec`'s is a _subtype of normal forms_. Calling the
   second "the paper's own text" is an over-read: the paper licenses _a_ quotient, not _this_
   quotient, and it licenses it by parameterising `Iso` over an `Eq`, an option `codec`'s
   `Iso` (a plain `structure` with a `∀`-law, `Codec/Iso.lean:27-33`) does not have.

3. **README's own gloss on that sentence is stricter than the plan's.** `README.md:1010-1017`
   (`sed -n 1005,1020p`): "the paper is describing how _it_ reads the invariant, not stating
   that the inverse law _holds modulo_ equivalence classes as a verified fact. The project's
   reading is the second thing, and it is the project's: the loss is the equivalence class, not
   a law that has been weakened in a checkable way." `codec` reads that sentence as a
   **departure from the paper's invariant**, filed as a `codec`-side departure (`[D4]`, the `ignore` anchor, `README.md:183-266`). `basen-radix` reads the
   same sentence as an _allowance_, and concludes no filing is needed. **Two intra-project
   readings of one sentence, both live, contradicting each other.** That alone is a defect.

4. **Against README's operational definition, this change _is_ observable** —
   `README.md:67-69`: "a _departure_ — an observable-semantics change". `toNat`/`ofNat` do not
   exist in `codec` or in the paper; `"  7"` and `"007"` now name `7`; `toNat b []` answers
   `some 0` where `trimFor b []` answers `none` (M-1); a padded base-32 block is `some` to the
   block iso and `none` to the fold (M-3). Those are observations, not obligations.

**Verdict: MUST** — the claim "this resolution adds none" is an over-read of the cited
sentence, it contradicts `README.md`'s own reading of the same sentence, and it leaves
`README.md`'s departure list silent about the largest semantic addition the ecosystem has made
since `[D2]`.

**Exact correction.** (a) In `design.md`, replace "both are the paper's own text … adds none"
with: "the paper licenses a quotient, but by parameterising `Iso` over an `Eq` (`PAPER.md:779`,
`element :: Eq α ⇒ …`), not by the canonical-representative device `Normal` uses; `codec`
already reads the same sentence as a _departure_ (`README.md:1005-1012`). This change is
therefore inside the paper's allowance for the _law_ and outside it for the _device_, and it
owes a `[Dn]` anchor, if only to state that." (b) Add a `[D9]` to `README.md:67-91`:
"**A numeral layer with a canonical-representative quotient and a zero convention** — the
paper has no `Nat` surface; `basen` adds one, and `"007"`/`"  7"`/`"7"` collapse to one value
through `trimFor`, not through the paper's `Eq`-quotient." Under `README.md:60-61` the anchors
are "shared with the code and the design docs", and nothing in `basen` cites a `[D9]` today.

---

## M-5 — `numeralIso`'s law is conditionally proved; the change calls it unconditional and does not say what the condition is

**Location.** `spec.md:49-54`; `tasks.md:37` ("`numeralIso` a full `Iso`, law unconditional on
the quotient"); `../lean-basen/BaseN/RadixCodec.lean:1937`.

**Claim as written** (`spec.md:49-54`):

> This SHALL be an ordinary `Iso` whose inverse law holds **unconditionally on the quotient**;
> the equivalence SHALL live in the codomain (the quotient type), never as a weakened law.

**Truth.** The law really is a `structure` field — `Codec/Iso.lean:27-33`,
`law : ∀ a b, apply a = some b ↔ unapply b = some a`, no hypothesis slot — so "not a weakened
law" is **faithful and proved**. But the `Iso` **value is a function of `IsRadix b`**:

```lean
-- BaseN/RadixCodec.lean:1937
def numeralIso (b : Nat) (hr : IsRadix b) : Iso Nat (Normal (List UInt8) (normF b))
```

`IsRadix` is not "`2 ≤ b`": it is a **7-constructor inductive** (`Radix.lean:524-532`) whose
only inhabitants are 2, 4, 8, 10, 16, 32, 64. So `numeralIso` is a _family of seven_ `Iso`s,
and the sentence "for each radix, a total bijection between `Nat` and the quotient" is true of
seven radices and **unprovable at any other `b`** — even `b = 3`, where `digitVal` is total,
returns `none`, and `ofNat`/`toNat` still typecheck. Compare `proposal.md:47`'s draft
signature `numeralIso : (b : Nat) → 2 ≤ b → …`, which the tree does not have; `proposal.md` was
never corrected, so the artifact a reader hits first still shows the weaker precondition.

**What the spec omits.** Not the fact of the precondition (it is in the signature, and
`design.md:75-77` says "`2 ≤ b` is a hypothesis on everything that uses it, and `numeralIso`
carries it explicitly") — but that `IsRadix` is _strictly stronger than_ `2 ≤ b`, and that
`design.md`'s own sentence is therefore stale.

**Command + output.**

```
$ sed -n 510,532p BaseN/Radix.lean
inductive IsRadix : Nat → Prop
  | b2 : IsRadix 2 | b4 … | b64 : IsRadix 64
$ nix develop --command lake env lean /tmp/probe1.lean
'BaseN.RadixCodec.numeralIso' depends on axioms: [propext, Quot.sound]
```

**Verdict: SHOULD** on the "unconditionally" wording (the law _is_ unconditional — the
defect is that "for each radix" silently means "for each of seven, witnessed", and
`design.md:75-77` says the precondition is `2 ≤ b` when it is `IsRadix`). **MUST** on
`proposal.md:47`, which shows a signature the tree does not have.

**Exact correction.** `spec.md:49` → "for each of the seven radices this package serves
(`IsRadix b`, enumerated in `RadixTie.radixInstances`)". `design.md:75-77` → "`numeralIso`
takes `IsRadix b`, which proves `2 ≤ b` and _in addition_ that `b` is one of the seven; the
weaker `2 ≤ b` is not enough, because `digitVal` at an unlisted radix is total and always
`none`." `proposal.md:47` → the `IsRadix` signature as shipped.

---

# SHOULD

## S-1 — the tie requirement never says what the `_8` bases restrict, so "the strong form holds with no hypothesis" reads as "on every numeral"

**Location.** `spec.md:118-125`.

**Claim.** "Base 2's eight bits, base 4's four quartets and base 16's two nibbles each reach
exactly `255`, so `n ≤ 255` follows from the digit bounds and the **strong form holds with no
hypothesis.**"

**Truth.** True for the `_8` bases, and the reason given is the right one. But "no hypothesis"
is only meaningful _at the fixed arity_, and the requirement's very next paragraph (`:105-110`)
is the one that adds the arity caveat — for the _port_, not for the reader of `:118-125`. The
measured consequence is in M-2: at 32/64 the block succeeds where the fold does not. Fix the
sentence's scope to "…holds with no _domain_ hypothesis (the arity is in the statement)".

## S-2 — `tasks.md` session-table row 3 promises "allowlist **10 → 3**"; the landed allowlist is **18 → 11**

**Location.** `tasks.md:39` vs `Axioms.lean:3927-3929` and `../lean-basen` `5044f95`.

**Claim.** `| **3. ← NEXT** | … | allowlist trimmed **10→3**; header constants re-derived |`

**Truth.** The landed gate prints `161 public definitions covered, 150 mentioned and 11
allowlisted`; the commit `5044f95` says `Allowlist: 18 -> 11`. The `10 → 3` figure came from
the _Iso sub-list_ (10 Iso entries, 7 dropped, 3 kept) — my read of `Axioms.lean:1702-1707`
confirms the decomposition is 3 + 2 + 3 + 3 = 11. So the row states the Iso subset's delta as
the whole allowlist's delta. This is the same padded-range / mismatched-parts defect
`AGENTS.md` records four times.

**Fix.** Row 3 → "allowlist **18 → 11**, of which the `Iso` entries go 10 → 3".

## S-3 — `tasks.md:6`'s anchor measurement `grep -rn 'radix|base : Nat|pow' BaseN/*.lean → nothing` is now false of the tree it motivates

**Location.** `tasks.md:5-6`; `design.md:16-18` (already flags the grep as BRE)…

**Claim.** "including `grep -rn 'radix|base : Nat|pow' BaseN/*.lean` → nothing."

**Truth.** `design.md:16-18` says the BRE form "exits 1 on _any_ tree and proves nothing", i.e.
the plan itself records the command as non-evidence — and then `tasks.md:6`, the START HERE
block, still prints its output as the motivating measurement, unqualified. Two artifacts, one
measurement, opposite verdicts. The measured fact has since also become trivially false: the
tree now has `def digitVal (radix : Nat)` (`Radix.lean:90`).

**Fix.** Replace with the substantive fact and a command that discriminates: "`basen` decodes
to `List UInt8` and never to a number — `grep -c 'Option Nat' BaseN/*.lean` before this change
was 0 except `Base2/4/…`'s `Nat → Nat` digit functions."

## S-4 — the "complete characterisation" of the overflow blocks is asserted in a docstring and pinned by nothing

Already stated in M-2(1). Location `RadixTie.lean:767-769`. **Fix:** state the iff, or weaken
the docstring to "the two laws together characterise the domain", and stop calling it
"complete" where no theorem says so. The gate's footprint arm reads docstrings for axiom
spellings, not for claims like this, so nothing else will catch it.

## S-5 — `spec.md:44`'s out-of-alphabet example, `"G"` in radix 16, names the one byte most likely to be misread

**Location.** `spec.md:43-45`.

**Claim.** "(the digit `"9"` in radix 8, or `"G"` in radix 16)".

**Truth.** Correct as written — I checked: `digitVal 16 71` → `none`. But the adjacent fact the
requirement's own "One digit-value function serves every radix" scenario tacitly relies on is
that the generic alphabet for 16 is **uppercase only**: `digitVal 16 102` (`'f'`) → `none`
while `BaseN.Base16.decodeHexFold` **accepts** lowercase and decodes `"6f"` to `111`:

```
$ nix develop --command lake env lean /tmp/probe11.lean
some [111]   -- decodeHexFold "6f"
some [111]   -- decodeHexFold "6F"
```

So `basen` _does_ carry a second Base16 alphabet, on the `Codec` value, reachable from the
shipped whole-input decoder — and `spec.md:38-39`'s "no base carries an independent alphabet
definition that could disagree with the generic one" is false of it. That is not a defect the
change introduces (it predates it, `Base16.lean:9-18`) but it _is_ a defect in the requirement
as written, and it is exactly what the parked `basen-uppercase-prepass` change exists to
resolve.

**Fix.** Scope the sentence: "no base carries an independent **digit-value** definition that
could disagree — a case-folding _pre-pass_ on a `Codec` value (Base 16's
`decodeHexFold`/`hexBlockIsoF`) is a variation layer above the alphabet and is
`basen-uppercase-prepass`'s subject, not this requirement's."

## S-6 — `proposal.md:93,126` still advertises the design D6 retracted

**Location.** `proposal.md:93` and `:126`, both still say "proved equal".

**Truth.** `design.md:249` explicitly retracts the word ("the equality is not 'proved equal' in
the `=` sense — that phrasing invites an `rfl`-shaped attempt that will not close"), and D6's
correction block (`design.md:253-275`) says the schema was false in three ways. The proposal is
the first artifact a reader opens.

**Fix.** Both instances → "tied to the fold by a canonicity-filtered implication pair (D6)".

## S-7 — `openspec` reports 44/44 complete, and the two MUST text defects are in a delta that will be archived verbatim

**Location.** `nix develop --command openspec list --json` → `"completedTasks": 44,
"totalTasks": 44, "status": "complete"`.

**Truth.** Measured. The status is true of the _task checkboxes_; it says nothing about whether
the requirement text is true of the code (M-1, M-3). Nothing in the flow blocks archiving on
that, and after archive M-1 becomes a live, normatively-stated falsehood in
`openspec/specs/basen/spec.md` (which today has no numeral requirements at all —
`grep -n "^### Requirement" openspec/specs/basen/spec.md` lists 10, none of them this change's).

**Fix.** Before archiving: fix M-1 and M-3 in the delta text, `openspec validate --strict`, and
record the correction in `tasks.md` §7 so the archive shows the pre-sync fix rather than a
post-sync silent amendment.

---

# NITPICK

## N-1 — `design.md:75-77` states the precondition as `2 ≤ b`; the tree uses `IsRadix`

Covered under M-5's correction; listed separately so it is not lost. This is a one-word fix and
it is the sentence a future porter will read as the licence for `numeralIso 3`.

## N-2 — `spec.md:20-22`'s parenthetical "(An earlier draft said "radices 2, 4 and 8", which is false of 4 and 8.)" is the third rewrite of a retracted claim, left in the normative text

Normative requirement text carrying its own revision history is how a reader comes to trust a
sentence that was wrong twice. `spec.md:19-22` currently reads correctly — I verified
`Base4.quartetVal 48..51` → `0..3`, `Base8.octToVal 48..55` → `0..7`, `Base2.valToBit` →
`(48,49,49)` for `(0,1,2)`, i.e. non-injective only at 2 (`/tmp/probe6.lean`). Move the
parenthetical to `design.md`.

## N-3 — `tasks.md:19` says "**Progress: 16/44**" in an artifact whose status line reads 44/44

The banner self-describes the figure as "computed, not remembered: run `openspec list --json`",
and the command now answers 44. A stale computed number in a banner that instructs the reader
to compute it is worse than an absent one.

## N-4 — `tasks.md:369-377` and `AGENTS.md:823` say `toNat b [] = some 0`; that is the correct fact, and the spec it was written to serve says `none` (M-1). The project already knew, three artifacts deep, and the requirement was never reconciled with any of them

Listed as a nit only because M-1 carries the MUST. The measurement trail is the evidence that
this was not an oversight but an unpropagated correction: `tasks.md:376`, `lean-notes.md:1422`,
`RadixCodec.lean:1440`, `:1868`, `:1900`.

## N-5 — `CHANGELOG.md:40-46` asserts "each is … mutation-tested by perturbing the corresponding digit order" for **all** the new laws

`tasks.md:692-697` records seven mutations (one per base's `*_of_toNat`) and their error counts;
it does not record a mutation for any of the 117 `RadixCodec` laws, the seven `*BlockIso_apply`
laws, or the three radix-instance laws. "each is …" is a universal over ~140 laws supported by
seven mutations on twelve of them.

**Fix.** "the seven per-base ties are mutation-tested (seven mutations, error counts in
`tasks.md` §3.3); the remaining laws are pinned by `#guard_msgs`."

---

# Part 2 — README claims not in a `[Dn]`/`[Sn]` section

## P2-1 — "the seven constructors" (`README.md:1057-1058`, `[D6]`) — **no defect found, not re-verified**

`README.md:1057-1058` says `Codec` is "an explicit **tree** (seven constructors)". Out of this change's
blast radius and I did not recount it; the number is `[D6]`-anchored and `codec`-side. Not a
finding. Reported here only so the omission is explicit rather than accidental.

## P2-2 — `README.md`'s Scope section (`:1282-1293`) describes `lean-basen` as shipping "the numeral bases … with their conformance theorems", and now ships a `Nat` numeral layer under the same sentence

No defect: "the numeral bases" is the phrase, and the layer is a numeral layer. Deliberately
not escalated.

## P2-3 — `README.md:1225-1240`'s "three generic primitives" table is unaffected

Verified by reading, not measured. No finding.

---

# Part 3 — the reverse direction: what the tree does that no document mentions

## P3-1 — the fold's empty-list admission is a live `Option`-returning answer, not an internal artefact

`toNat b [] = some 0` is reachable from the public `Radix` module and is _not_ filtered by
anything: `trimFor b [] = none`, `isNumeral b [] = false`, `normF b [] = [48]` (measured,
`/tmp/probe12.lean`). So there are **three** answers to "what is `[]`?" in one module, and the
only artifact that says so is a docstring. `README.md` says nothing.

## P3-2 — `numeralIsoAt` (`RadixTie.lean:1125`) is a public `def` whose only purpose is to read `numeralIso` at an enumerated radix, and it is allowlisted (`Axioms.lean:1974`) as "no new law appears here"

That is _true_, but it means the "seven instances" the spec's first requirement promises
("as **one** definition serving all seven radices") are a **`List Nat` plus a `∀` proof**
(`radixInstances`, `radixInstances_areRadix`), not seven `Iso` values with seven statements.
`spec.md`'s "one definition" is honest; `tasks.md:39`'s "no radix instances" → "seven radix
instances" wording is not — there are three enumeration laws and one `def`, not seven laws.
Nothing in `README.md` or the spec claims otherwise, so this is a NITPICK on `tasks.md`.

## P3-3 — no unadvertised semantic departure found in the _tie_ layer

The seven `_8` ties, the two overflow laws, and the `_L` ties are what the spec describes,
modulo M-2/M-3. `beVal` replacing D6's non-existent `bytesOfNat` is disclosed in
`design.md:334-337` and `CHANGELOG.md:28-31`. No finding.

---

# Part 4 — every footprint claim I encountered, measured

| claim site                                                            | claim                                                                                                                                                  | measured (`#print axioms`)                                                                                                                                           | verdict                                                                                                                                                        |
| --------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------ | -------------------------------------------------------------------------------------------------------------------------------------------------------------------- | -------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `RadixTie.lean` docstrings ("every law `[propext, Quot.sound]`-only") | all of `RadixTie`                                                                                                                                      | `toNat_of_b64BlockApply_three`, `toNat_of_b32BlockApply_five`, `octBlockApply_overflow`, `bitBlockApply_of_toNat` → all `[propext, Quot.sound]`                      | holds (5 probed)                                                                                                                                               |
| `RadixCodec.lean:1937` `numeralIso`                                   | clean                                                                                                                                                  | `[propext, Quot.sound]`                                                                                                                                              | holds                                                                                                                                                          |
| `RadixAlphabets.lean` module docstring                                | "Every law here is `[propext, Quot.sound]`-only"                                                                                                       | not probed individually                                                                                                                                              | UNVERIFIED (7 theorems; probed none)                                                                                                                           |
| `CHANGELOG.md:39`                                                     | "Every law is `[propext, Quot.sound]`-only with zero `Classical.choice`; each is pinned by a `#guard_msgs` block and mutation-tested"                  | footprints: the ones I probed hold; **"each is … mutation-tested" is unsupported** (seven mutations, ~140 laws — see N-5); "zero `Classical.choice`" I did not sweep | SHOULD (N-5)                                                                                                                                                   |
| `tasks.md:921-927`                                                    | "All **117** `RadixCodec` laws … a scan of those 117 footprint lines for `Classical.choice`/`sorryAx` is **0**, as it is for all **601** pinned names" | not swept by me                                                                                                                                                      | UNVERIFIED — the sweep is a `grep -c Classical.choice` over the gate's own `#guard_msgs` output, which is a _stated_ footprint, not an independent measurement |
| `Axioms.lean:1967` / `:1974` / `:1982`                                | `numeralIso` / `numeralIsoAt` / `isNumeral` allowlisted because their law is a proved structure field                                                  | `Codec/Iso.lean:27-33` confirms `law` is a field; `#print axioms numeralIso` → `[propext, Quot.sound]`                                                               | holds                                                                                                                                                          |

**One thing measured about the gate itself, since the plan leans on it:** the current build's
eight lines read `722 = 670 + 52`, `161 = 150 + 11`, `native_decide 12`, `46 claim site(s)`.
The `46 claim sites` is the same number as before this change added ~140 laws — so the
"footprint claims" arm did **not** find any of the new docstrings' "`[propext, Quot.sound]`-only"
sentences to be claim sites. That is either correct (the arm's vocabulary matches only
backticked literals, and the new docstrings use a different spelling) or a recurrence of the
round-nine vocabulary hole. I did not chase it — see "could not confirm" below.

---

# Refuted / could not confirm

- **Refuted — "the `_L` ties are vacuous because the block constraint is false".** I formed this
  hypothesis from M-3 (`toNat 64 "Zg==" = none` while `b64BlockApply "Zg==" = some [102]`) and
  expected `toNat_of_b64BlockApply_three` to be vacuous. It is not: its hypothesis restricts
  `cs`'s _result_ to a 3-element list, and `b64BlockUnapply [b0,b1,b2]` never emits `=`, so the
  tie is meaningfully stated over the full-width arity. It says nothing about the short arities,
  which is M-3's point — but "vacuous" would have been wrong.
- **Refuted — "`digitVal` disagrees with the per-base functions".** `digitVal 16 71` (`'G'`) →
  `none`; `digitVal 16 70` → `some 15`; `Base4.quartetVal`/`Base8.octToVal` are `48 + d` on
  their windows. The decode-direction agreement holds where the spec says it does.
- **Could not confirm — whether the gate's 46 claim sites should have grown.** Settling it
  needs the footprint arm's `footprintClaimPhrases` vocabulary checked against the new
  docstrings' actual spelling (`"-only"` suffix present in `Radix.lean:78`? absent elsewhere?).
  The measurement: `grep -c 'propext, Quot.sound' BaseN/Radix*.lean` versus the arm's
  recognised count. I did not run it.
- **Could not confirm — `design.md:16-18`'s three greps returning zero.** They are asserted in
  the design as measured; I did not re-run them (`grep -rnE 'radix|base : Nat|pow' BaseN/*.lean`
  would now trivially be non-zero).
- **Could not confirm — the "seven mutations, seven bases, error counts 3/3/3/3/3/3=3, 2, 4"
  in `tasks.md:692-697`.** Re-running them means mutating and rebuilding; `lake build` was
  forbidden. The counts are internally consistent and the method is described.
- **Could not confirm — `Axioms.lean:1704-1707`'s 3 + 2 + 3 + 3 = 11 decomposition against the
  list body.** I read the table and the gate's printed `161 = 150 + 11`, not the eleven entry
  lines. The `grep -n 'numeralIso, numeralIsoAt, isNumeral'` confirms the numeral-layer row.
- **Not a finding — the `[Dn]` filing question's hardest case.** One could argue `[D9]` is
  unnecessary because `codec`-the-package does not own `basen`'s semantics. I reject that
  reading on the record: `README.md:60-61` says the anchors are "shared with the code and the
  design docs" and `README.md:1287-1290` lists `lean-basen` under this document's Scope, so a
  porter told to "read this one list and know exactly what to reproduce" is told nothing about
  a `Nat` layer. M-4 stands.
