# Tasks — `basen-nat-iso`

**Direction.** Work top-down. §1 settles the type; nothing else can be proved before
it is, because an `Iso` over raw `Bytes n` is _false_ (`"001"` is a valid `Bytes 3`
that no `Nat` maps to).

## The shape, stated once

**A number is isomorphic to its canonical numeral; every lax spelling is a name for
that same image, resolved by a normaliser before the isomorphism is consulted.**

```
1  ↔  "1"                     the Iso: Nat ↔ normal-form digit bytes
"01"    ─natTrim→ "1"         leading zeros are information-free variation
"    1" ─natTrim→ "1"         as is leading whitespace
"1"     ─natTrim→ "1"         the canonical spelling is already a fixed point
```

Leading zeros and leading whitespace are **the same phenomenon**: syntactically
permitted, semantically inert. Neither is a second image of `1`, and neither is an
error. Only input naming nothing (`""`, `"1a"`) is rejected.

**The variation set is per base, and octal/hex may differ from decimal.** A `0x` /
`0o` / `0b` prefix names a _radix_, not padding within a numeral, and in the
C-family idiom a leading zero changes the base of a literal (`017` is octal). So:
decimal absorbs leading blanks and leading zeros; each other base decides its own
policy, and no base's policy is applied to another by default. **This change scopes to
decimal**; the other bases get their own change, and §6 records why.

This is `Codec/Normal.lean`'s thesis verbatim — "a bijection with the quotient of the
concrete syntax by the information-free variation" — and it already supplies
`Normal`, `Normalizer`, `fill`, `fill_surj`, `fill_fixed` and `decodeNormal`. The
`Iso` therefore stays an **ordinary total bijection** with an unconditional law; the
equivalence lives in the codomain, never in the law.

**Measured state of the tree this change starts from** (`./lean-basen` @ `5222529`,
`./lean-codec`; both `lake build` green):

```
encodeDig [0x01]        → 3 digit bytes   ("001")
encodeDig []            → 0 digit bytes   ("")
decodeRepeat  "001"     → [[], [1]]                  (two answers)
decodeFull    "01"      → none                       (2 is not a multiple of 3)
grep -rn 'Nat → List UInt8|List UInt8 → Nat' BaseN/ → (no hits)
```

**There is no `Nat`/`Int`-valued codec anywhere in either repo.**

## 1. Settle the type

- [ ] 1.1 Confirm the codomain is the `Normal` quotient:
      `Iso Nat (Normal (List UInt8) natTrim)`. Raw `Bytes n` is not an option
      (`"001"` names no distinct value). Record the measurement that forces it.
- [ ] 1.2 Write the **three-spelling witness first**: `decodeNat "1"`,
      `decodeNat "01"` and `decodeNat "   1"` are all `some 1`, while
      `encodeNat 1 = "1"`. Mutate it — a `natTrim` that stops trimming must fail the
      build. This is the foundation, not a test.
- [ ] 1.3 Decide `Nat`-only vs `Integer`. If `Integer`, `-0` and `-01` are the same
      information-free variation and belong in the same witness set.
- [ ] 1.4 Record the **per-base** variation policy. Decimal absorbs leading blanks
      and leading zeros. Whether octal/hex absorb a `0x`/`0o`/`0b` prefix, reject it,
      or require it is a **separate decision per base** and SHALL NOT be inherited
      from decimal — a prefix names a radix, and in C-family notation `017` is
      octal, so applying the decimal rule to base 16 would be wrong in a way a
      caller could observe. This change fixes decimal only; the others are §6.

## 2. The canonical numeral and the Iso

- [ ] 2.1 `natTrim : List UInt8 → List UInt8` — the normaliser: drop leading
      whitespace, then leading `0`s, leaving at least one digit (`"0"` stays
      `"0"`; the all-blank / empty run becomes `"0"`). Prove `Normalizer`
      (`natTrim (natTrim s) = natTrim s`).
- [ ] 2.2 Prove the fixed points are exactly the canonical numerals: no leading
      blank, no redundant leading zero, non-empty, all decimal digits. This is the
      property `natOfDigits` relies on, and it is where `""` and `"  "` are settled.
- [ ] 2.3 `natDigits : Nat → Normal (List UInt8) natTrim` — minimal decimal digits,
      `0 ↦ "0"`, `1 ↦ "1"`, no padding.
- [ ] 2.4 `natOfDigits : Normal (List UInt8) natTrim → Nat` — **total** on the
      quotient (a normal form is canonical by 2.2), so no `Option` and no rejection
      branch.
- [ ] 2.5 `Iso.ofTotal natDigits natOfDigits` with the two round-trip equations;
      `#print axioms` clean for each. The second equation is stated over the
      quotient — over raw `List UInt8` it would be false at `"01"`, which is why
      §1 exists.

## 3. The user-facing decoder

- [ ] 3.1 `decodeNat : Bytes n → Option Nat` is the **normalising** entry point:
      `decodeNat s = (natOfDigits ∘ fill natTrim) s.toList`, so every spelling of a
      numeral decodes to it. There is no separate "lenient" API — the normalising
      one _is_ the API, and the strict `Iso` is the object whose law is quoted.
- [ ] 3.2 Prove `decodeNat` agrees with the strict `Iso` on canonical input
      (`decodeNormal_of_fixed` is the reusable step), and that it rejects exactly the
      inputs that name nothing.
- [ ] 3.3 Record the normaliser's limit honestly: a spelling that differs in _length_
      from its canonical form is not expressible by a trimmer, so `decodeNat` is a
      trimmer, not "accepts anything".

## 4. Gate, bench, prose

- [ ] 4.1 Regenerate `basen`'s `Axioms.lean`; every new law pinned, header numbers
      moved with the `expected*` constants.
- [ ] 4.2 Bench vectors: `"0"`, `"1"`, `"9"`, `"10"`, `"01"`, `"   1"`, `""`,
      `"1a"` — each value-checked. The first six must decode; the last two must not.
- [ ] 4.3 `basen` README: replace the "scope is digit encodings, not numeric ones"
      note with what now exists, and state the normalisation rule with whitespace and
      leading zeros named as one phenomenon.

## 5. Gates

- [ ] 5.1 `lean-basen`: `lake build` (every gate line), `lake build bench`,
      `nix build '.#bench'`.
- [ ] 5.2 `nix fmt`, then commit per task family, individual files, printing
      `git diff --cached --name-only`.
- [ ] 5.3 Bump `lean-basen`'s `codec` pin only if `codec` changed.

## 6. Recorded, deliberately not in this change

- **`Integer`**, if §1.3 scopes to `Nat` first — a follow-on with its own `-0` and
  `-01` witnesses.
- **The other six bases, and their own normalisation policies.** Same _shape_ as
  decimal, but **not** the same variation set: a `0x`/`0o`/`0b` prefix names a radix
  rather than padding a numeral, and the C-family `0`-prefix idiom makes a leading
  zero change the base of a literal. Each base's policy is its own decision, and
  decimal's must not be copied by default. They follow once decimal is proved.
- **`varint`/LEB128.** Overlong forms are the same information-free variation but a
  different wire format; separate change.
