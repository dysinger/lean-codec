# Proposal

## Why

A second hypercritical audit (2026-11-05, three independent reviewers, read-only,
findings in `/tmp/audit-{a,b,c}-*.md`) went over `lean-codec` and `lean-basen`
after `codec-audit-remediation` closed. It confirms that change did what it
claimed — the axiom gate is real and green, `findByte_spec` is `[propext]`, the
three false docstrings are fixed, the README's `packedCands`/`[S4]`/`[D4]`/
`[D7]` corrections are in. What it found is the layer **underneath** those fixes.

Four defects are of a kind that a green build cannot reveal, and each was
independently re-measured before being written down here:

1. **The axiom gate has a hole, and it is a name-suffix hole.** `isGeneratedAux`
   filters by last identifier component, and `Codec.Nat.eq_irrel`
   (`Codec/Codec.lean:389`) is an **authored theorem with an explanatory
   docstring** that the `eq_irrel` rule silently drops (`grep -c
'Codec.Nat.eq_irrel' Axioms.lean` → `0`). Three `Iso.MeasureDecreases*.dec`
   structure fields are dropped the same way. The gate's own docstring says "None
   is a law a human wrote" — false for those four. Because the mechanism is
   name-based it is **not sound by construction**: any future law ending in
   `dec`, `induct`, `inj`, `injEq`, `eq_def`, `sizeOf_spec`, `congr_simp`, or
   `eq_irrel` is silently un-gated. This is the one class of defect the gate most
   needed to exclude, sitting inside the gate.

2. **`lean-basen` base32 §3.5 is proved for 1 of 4 non-canonical tail shapes, and
   the docstring says the opposite.** `Base32.lean:2653-2655` states that "the
   2/3/4/5-byte tails end on a full 5-bit character and have none [no spare
   bits]". Reading `b32BlockUnapply` four lines above: the 2-byte tail's last
   character is `(v1 % 2) * 16` (**4 spare bits**), the 3-byte's is
   `(v2 % 16) * 2` (**3**), the 4-byte's is `(v3 % 4) * 8` (**3**). Measured:

   | canonical                             | non-canonical | result |
   | ------------------------------------- | ------------- | ------ |
   | `MZTA====` → `some [102,102]`         | `MZTR====`    | `none` |
   | `MZTGM===` → `some [102,102,102]`     | `MZTGN===`    | `none` |
   | `MZTGMZQ=` → `some [102,102,102,102]` | `MZTGMZR=`    | `none` |

   The **behaviour is correct** — only because `b32BlockApply` re-encodes and
   compares (`Base32.lean:415`). But three of the four shapes have **no theorem
   and no bench vector**, so removing that guard breaks them with nothing failing.
   Base64 proves both of its shapes; base32 proves one and asserts the rest in
   prose that is false. A correct behaviour guarded only by an unchecked
   obligation is the worst combination: it looks covered.

3. **`Unambiguous` is not a congruence for `seq`, and the library's framing
   implies it is.** Measured counterexample: with `bIso : Iso UInt8 Bool`
   (`apply a = if a = 0 then some true else none`), `bt := iso bIso byte`,
   `bo := alt bt (pure false)`, `whole := seq bo (pure ())`, the 1-byte input
   `#[0]` decodes to **two distinct values**:
   `[((true, ()), 1), ((false, ()), 0)]`. Each half is unambiguous; the
   composition is not. This is the same failure mode audit B predicted for
   `decodeArray_unambiguous_value`, and it means the "closure lemma" one would
   naturally want (`Unambiguous d₁ → Unambiguous d₂ → Unambiguous (seq d₁ d₂)`) is
   **false** and must not be planned as if true.

4. **`MeasureDecreasesR` has zero suppliers.** `Iso.lean:693` defines the
   right-fold family; `grep` finds no theorem constructing one. So `Iso.foldr`'s
   law, and **every** `chainr1` law (`decodeChainr1_spec`,
   `encodeChainr1_rel`, `_ne_none`, `_of_decode`, `_injective_of_unambiguous`),
   rest on a hypothesis nothing in the tree provides. `codec-audit-remediation`
   closed this for the _left_ fold (`counterMeasureDecreases`) and left the
   mirror; the asymmetry was created by that change, not inherited.

Beyond those four, the audit confirmed the README's departure anchors still carry
**seventeen** defects, of which three are load-bearing: `[D2]` is filed as a
"strengthening" while its own body describes an observable semantics change;
`[S3]` cites `Codec.takeWhile`, **which does not exist** (`#check` → unknown
identifier) and omits `count`/`manyUpTo`/`optional`/`choice` from the core
inventory; and `[D3]` claims `|` is backtracking-union without noting that core
ships a committed-choice decoder (`Codec.decodeOne`) and that
`decode (d | d) s` returns its result **twice**, not once.

## What Changes

- **Make the axiom gate sound rather than name-based.** Replace the suffix
  filter's silence with an explicit, audited partition: every public `thmInfo`
  must be either gated or in a named `generatedAuxAllowlist`, and the build
  fails on a name in neither. Gate `Codec.Nat.eq_irrel`. Record why the three
  `.dec` projections are excluded (they are `Prop` fields, not laws) instead of
  dropping them by accident of their last name component.
- **Close base32's §3.5 gap and its false docstring**, in `lean-basen`: prove the
  2/3/4-byte spare-bit facts and the three named-vector rejections, and replace
  the docstring with the true statement. Add the vectors to the bench.
- **Correct `Unambiguous`'s framing to the true statement.** Do **not** prove a
  `seq` closure lemma — it is false (counterexample above). State the honest
  composition law (`Functional ∧ RelAligned` at `seq`, which is what
  `decodeArray_unique` already needs) and record the counterexample where a
  reader would otherwise assume congruentiality.
- **Add the `MeasureDecreasesR` witness** so `chainr1` is exercised like
  `chainl1`.
- **Fix the three load-bearing README anchors** (`[D2]` filing, `[S3]`'s
  nonexistent symbol and inventory, `[D3]`'s scope and multiplicity), and the
  fourteen smaller ones the audit catalogued.

## Capabilities

### Modified Capabilities

- `codec/axiom-gate`: the gate's coverage requirement currently says only that
  newly added theorems enter the gated set by default. The audit shows the
  mechanism can _drop_ an authored theorem silently, so the requirement must
  state that the gated set is a **complete partition** of the public theorems —
  gated, or explicitly allowlisted as compiler-generated — with no third path.
- `codec/review-remediation`: "A claim of 'proved' names a declaration that
  exists" is currently satisfied by the three names fixed last round; the audit
  found `[S3]` cites `Codec.takeWhile`, which does not resolve. The requirement
  must cover docstrings **and** README anchors, and must forbid a prose claim
  that a behaviour is guaranteed when only its mechanism is checked.

### New Capabilities

- `codec/congruence-honesty`: the statement that which predicate families
  (`Unambiguous`, `Functional`, `RelAligned`, `LengthDet`, `LengthConst`, `huniq`)
  compose under which constructors is a _proved_ fact, not an assumed one — with
  the measured non-congruences recorded, so a downstream author is never told a
  composed codec inherits a leaf's uniqueness.

## Impact

- **`Axioms.lean`** (+ regeneration): the `generatedAuxAllowlist` partition and
  the coverage assertion; `Codec.Nat.eq_irrel` gains a `#guard_msgs` block.
- **`Codec/Sound.lean`**, **`Codec/DecodeOne.lean`**: the congruence statements
  and the recorded counterexamples; the `[S3]`-adjacent "every constructor has a
  witness" sentence corrected for `pure`.
- **`Codec/Iso.lean`**: `counterMeasureDecreasesR`.
- **`../lean-basen`**: `BaseN/Base32.lean` (§3.5 family + docstring),
  `BaseN/Bench.lean` (vectors), `README.md`/`Axioms.lean` (attribution and the
  gate-complete ≠ §3.5-complete note). This repo is pinned to `codec` by
  `flake.lock`, so it needs `nix flake update codec` + `lake update codec` only
  if a statement it consumes changes; nothing in this change touches
  `decodeFull`/`decodeRepeat`.
- **`README.md`**: `[D2]` refiled, `[S3]` inventory and symbol corrected, `[D3]`
  scoped with the multiplicity note, plus the smaller corrections.
