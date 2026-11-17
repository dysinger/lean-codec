# Tasks — `basen-varint-radix`

**Direction.** §1 proves the split is additive before anything is added. §2 adds the
predicate. §3 adds the 128 arm. §4 delivers varint as a run. §5 repairs the live spec.
§6 gates.

**Starting state** (`../lean-basen` @ `a06998b`, gates green):

```
gate        698 = 646 + 52 at 29 jobs; defs 156 = 140 + 16
base 16     54 declarations (after basen-uppercase-prepass)
IsRadix     7 constructors; 4 exhaustive-match sites; isRadix_le64 at 6 sites
digitVal    a 7-arm `if radix = N` chain ending in `else none`
```

Measured, so no one has to re-derive it:

```
Radix.digitVal 128 0x30  ->  none      (falls off the chain)
Radix.digitVal 64  0x30  ->  some 52
```

## 1. Establish that the widening is additive (blocking, before writing anything)

- [ ] 1.1 Count the existing `IsRadix` surface and record it, so "unchanged" is a
      measurement rather than a claim:
      `     grep -rn 'cases hr with' BaseN/ | wc -l          # expect 4
    grep -rn 'isRadix_le64' BaseN/ | wc -l           # expect 6
    `
- [ ] 1.2 Record the baseline gate line verbatim (`lake build`), so the delta after §2–§4
      is arithmetic and not memory.
- [ ] 1.3 Confirm `digitVal 128` is `none` for several bytes, not just one — the arm is
      missing, and a single `#eval` would not distinguish "missing" from "misses this byte".

## 2. `ServesDigits` — the split predicate

- [ ] 2.1 `inductive ServesDigits : Nat → Prop` with `ofRadix : IsRadix r → ServesDigits r`
      and `b128 : ServesDigits 128`. **Two constructors, and it stays two** — a radix joins
      only if `digitVal` has an arm for it.
- [ ] 2.2 `servesDigits_ge2` and `servesDigits_value` (the set is `{2,4,8,10,16,32,64,128}`)
      — the second is what lets a proof discharge "is this 128?" without unfolding.
- [ ] 2.3 **`ServesDigits` must NOT be substitutable for `IsRadix`.** Assert it: a theorem
      `ServesDigits r → IsRadix r` must be _unprovable_, so state the refutation that
      matters — `¬ IsRadix 128` — and let the type do the rest. Do not add a coercion.

## 3. The 128 arm in `digitVal`

- [ ] 3.1 Add `else if radix = 128 then some (c % 128)` to the chain in `Radix.lean`, and
      mirror it in `digitVal_eq`. **The arm is TOTAL over bytes** — pass 1 (V-2/V-3) found
      three incompatible definitions across design/tasks/spec and the total one is the arm
      that composes: a varint run's members are the _high-bit-set_ bytes, so a `c < 128`
      arm would reject the very bytes the run is made of.
      `digitVal_eq` ends `:= rfl`, so omitting the mirror is a **compile error**, not silent
      drift — corrected after pass 1 (V-6).
- [ ] 3.2 `digitVal_128` — the arm as its own equation, so callers never unfold the chain.
- [ ] 3.3 **Do not add `digitVal_byteOfDigit_128`.** The positional round-trip lemma does
      not exist at 128 and inventing one would be the false eighth arm the design rejects.
      If a proof seems to need it, the proof is using a positional law where a
      terminator-delimited one belongs.
- [ ] 3.4 Confirm §1.1's counts are unchanged (**4** `cases hr with`, **6** `isRadix_le64`)
      — the split's whole claim. Verified at authoring time (pass 1 R-4) and to be
      re-verified after the arm lands.
- [ ] 3.5 **Compile `digitVal_byteOfDigit_zero` first** — `RadixCodec.lean:939` unfurls at a
      _variable_ `b` before `cases hr with`, so it is the one site where an appended arm has
      to reduce per-arm rather than at a literal. Pass 1 could not confirm it compiles
      (read-only); it is the cheapest early signal that the arm is additive.

## 4. `BaseN/Varint.lean` — the run

- [ ] 4.1 **Evaluate first, prove second.** `#eval` the fold on the boundary vectors before
      any theorem: `[0x01] = 1`, `[0x81,0x01] = 129`, `[0x80,0x80,0x01] = 16384`,
      `[0xFF,0xFF,0xFF,0x7F] = max`. Write the numbers in this file.
- [ ] 4.2 `varintRun` — the maximal high-bit-set prefix plus its terminator, expressed with
      the existing run layer, not a hand-rolled `List` recursion.
- [ ] 4.3 `varintValue` — the shifting fold, least-significant group first. **Not `toNat`
      at any radix**; state why in the module docstring (design D3).
- [ ] 4.4 `varint_roundtrip` — `encode (decode s) = s` on canonical runs.
- [ ] 4.5 A rejection law: a run with **no** terminator (every byte high-bit set, input
      exhausted) is `none`, not a partial value.
- [ ] 4.6 A theorem recording the **non**-identity, with the witness that actually
      distinguishes them: **`[0x80,0x80,0x01]`** — LEB128's canonical 16384, where
      `toNat 128` over the same groups `[0,0,1]` gives **1**. Pass 1 (V-1) found the two
      witnesses this task originally implied (`[0x81,0x01]`, `[0x81,0x81,0x01]`) both
      **agree**, because the folds agree whenever the group list is palindromic. Do not use
      an all-equal-group vector: it will prove equality.

## 5. Repair the live spec (sibling audit A-1 … A-4)

The delta already carries the repaired text; these tasks are the verification.

- [ ] 5.1 Requirement 7's repaired block states the `MAY`, keeps the roundtrip obligation,
      and cites only declarations that exist. **Verify the citations mechanically** — the
      audit's sweep is ~20 lines of Python and found five dangling names; run it before and
      after.
- [ ] 5.2 Requirement 7 keeps **all five** scenario names (archive refuses a rename — measured
      while authoring: `openspec validate` reported "omits scenario(s) the current spec still
      has" for three renamed ones).
- [ ] 5.3 Requirement 11 keeps all three scenario names and gains exactly one.
- [ ] 5.4 The header string must match the live spec **exactly**, including
      `(RFC 4648 §8)` on requirement 7 — a `MODIFIED` block is matched by header text.

## 6. Gates, bench, prose

- [ ] 6.1 Regenerate `basen`'s `Axioms.lean`; every new law pinned; the `expected*`
      constants and the header paragraph re-derived from the gate's own output.
- [ ] 6.2 `lake build`, `lake build bench`, `nix build '.#bench'`, formatting gate.
- [ ] 6.3 `CHANGELOG`: the split, the non-goal (`numeralIso 128` does not exist and should
      not), and the corrected requirement 7.
- [ ] 6.4 `README`: if it describes `IsRadix` as "the seven radices this package serves",
      state the two predicates.

## 7. Recorded, not in this change

- **`Int`-valued numerals.** `-0` remains a design question.
- **`numeralIso 128`.** Deliberately not built (design D3): a varint is not a
  fixed-width numeral, so the bijection would be onto the wrong object.
- **An open `2 ≤ r` predicate.** Rejected in design D1: every existing positional proof
  would have to be re-stated over a variable radix, which the dispatch chain cannot support.
- **Varint's performance story.** It is a run triple with its own benchmark; this change
  lands the layer.

## 8. Decided during review (not an open question)

**The requirement-7 repair rides in this change.** Pass 2 (W-5) found that this section still
called it an open question after `design.md` had decided it — the fix had landed in one of two
files. The decision: this change already opens a `MODIFIED` block on requirement 7's
neighbour, and one change owning both edits is the simplest way to keep `AGENTS.md`'s
archive-ordering rule. §5's tasks are therefore in scope, not optional. If the owner prefers a
separate change, drop the first `MODIFIED` block **and** the 5 → 5 scenario assertion with it.

## 9. Review obligations found by the two reviewer passes

- [ ] 9.1 **`trimFor`/`normF`/`isBlank`/`isZeroDigit` take a bare `Nat` radix**, so radix 128
      is _not_ type-excluded from them (pass 2 W-3). Nothing in this change constructs a
      `ServesDigits 128` there, but the constraint is the code's discipline, not the type's.
      Add a docstring note at `trimFor` saying radix 128 must not be passed, or a theorem
      stating the normaliser's preconditions name `IsRadix` rather than `Nat`.
- [ ] 9.2 The "run layer" is **two** layers — the derived `takeWhile p` run and
      `relRepeat`/`decodeRepeat`/`encodeRepeat` — and **no `Run`-then-terminator composition
      exists** (pass 2 W-9). Tasks 4.2's "express with the existing run layer" is
      aspirational until that composition is written. Budget for it; do not assume it.
