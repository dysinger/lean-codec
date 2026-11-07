# Proposal — `basen-nat-iso`

## Why

**`basen` has no numeric codec.** Every base is a `Codec (List UInt8)` over
fixed-width digit blocks, so a caller who wants a number gets a byte list and does the
arithmetic themselves. The byte array is a legitimate _intermediate_, but it is not
the deliverable: a user asking for base-10 decoding wants a `Nat`, and today there is
nothing to call.

Measured on the current tree (`/tmp` probes against `BaseN.Base10`):

```
encodeDig [0x01]        → 3 digit bytes   ("001")   -- zero-padded to a block
encodeDig []            → 0 digit bytes   (""   )   -- zero has no digit
decodeRepeat  "001"     → [[], [1]]                 -- two answers
decodeFull    "01"      → none                      -- 2 is not a multiple of 3
```

Composing `Nat → List UInt8 → bytes` therefore inherits three defects: zero-padding
baked into the _encoder_, an empty encoding for zero, and a
length-must-be-a-multiple-of-three rule. None of those is a numeral.

`../fstar-codec` records the same class as `[D12]`/`[D13]`, where `varint` and
`digits_to_int` are ⛔ **false** over their decoder (`"01"` accepted while
`enc 1 = "1"` makes the inverse law false, not unproved), and `[W9]` records that the
lenient layer was never built. This change is the Lean answer to both — and Lean
already has the right machinery, so it is a reuse rather than an invention.

## What changes

Add a `Nat`-valued decimal codec to `basen`.

**The shape: a number is isomorphic to its canonical numeral, and every lax spelling
is a name for that same image.**

```
1  ↔  "1"                    the Iso: Nat ↔ canonical digit bytes
"01"    ─natTrim→ "1"        leading zeros are information-free variation
"    1" ─natTrim→ "1"        as is leading whitespace
"1"     ─natTrim→ "1"        the canonical spelling is already fixed
```

Leading zeros and leading whitespace are **one phenomenon**, not two: both are
syntactically permitted and semantically inert, so neither is a second image of `1`
and neither is an error. The number is isomorphic to `"1"`; `"01"` and `"   1"` are
lax names for it, resolved _before_ the isomorphism is consulted.

**But the variation set is per base, and octal and hex may act differently.** A
`0x` / `0o` / `0b` prefix names a _radix_ rather than padding a numeral, and in the
C-family idiom a leading zero changes the base of a literal (`017` is octal, 15).
So this change fixes the **decimal** policy — absorb leading blanks and leading
zeros — and records that each other base decides its own; no base inherits decimal's
rule. The other six are a follow-on change, not a copy-paste.

| layer                     | type                                           | status                   |
| ------------------------- | ---------------------------------------------- | ------------------------ |
| bytes ↔ byte list         | `Codec (List UInt8)` (`digElem`, `decodeFull`) | **exists and is proved** |
| `Nat` ↔ canonical numeral | `Iso Nat (Normal (List UInt8) natTrim)`        | this change              |
| any spelling → canonical  | `natTrim` + `fill`, then defer                 | this change              |

`Codec/Normal.lean` already supplies this — `Normal`, `Normalizer`, `fill`,
`fill_surj`, `fill_fixed`, `decodeNormal` — and its own docstring states the thesis:
_"the honest object is not a relaxed law, it is a bijection with the quotient of the
concrete syntax by the information-free variation."_ A redundant leading zero is
precisely information-free variation, so the `Iso` stays an **ordinary total
bijection** with an unconditional law. The equivalence lives in the **codomain**;
nothing is weakened.

`decodeNat` is the normalising entry point, so a user gets `some 1` from `"1"`,
`"01"` and `"   1"` alike. Only input naming nothing (`""`, `"1a"`) is rejected.

## Decisions this change must make, and cannot defer

1. **`Nat` only, or `Integer` too?** `-0` and `-01` are the same information-free
   variation one level up. Scoping `Nat` first keeps them out of this change.
   **Recommendation: `Nat` first.**
2. **Minimal digits.** `enc 1 = "1"`, `enc 0 = "0"`. Not zero-padded, not empty.
3. **What the normaliser absorbs.** Leading whitespace, leading zeros, and the
   all-blank run. What it does _not_ absorb: anything that changes the value
   (`"1a"`), and spellings differing in _length_ from their canonical form — a
   trimmer is not "accepts anything".
4. **Where the equivalence lives.** In the codomain — the quotient — not in the law.
   `fill_surj` is the theorem that makes every lax spelling reach a canonical form.

## Non-goals

- Changing any existing base's byte-level law. `digElem`'s `roundtrip`,
  `decodeFull_B10_char`, `encode_injective` and `decodeFull_canonical` stay as they
  are; the `Nat` layer is _above_ them.
- Changing the `codec` core. `Iso.ofTotal` and the `Normal` layer already exist.
- Touching the other six bases until the decimal shape is settled and proved, and in
  particular **not** applying decimal's leading-zero rule to octal or hex, whose
  prefix conventions make a leading zero mean something else.

## Risk

**The one way this fails:** stating the `Iso` over raw `Bytes n` or raw
`List UInt8` instead of the quotient. Then `"001"` and `"01"` have no image and the
`law` field is false — the exact defect this change exists to avoid. The first task is
therefore to settle the codomain and prove the three-spelling witness **before** any
other proof is attempted, and to mutate that witness to confirm it fires.
