# Design — `basen-radix`

## D0 — The gap, measured

`basen` decodes text to `List UInt8` and never to a number. The evidence, from
`../lean-basen`:

| what exists     | signature                          | why it is not the number                |
| --------------- | ---------------------------------- | --------------------------------------- |
| `digVal`        | `Nat → Nat`                        | one digit byte to one digit _value_     |
| `bitBlockApply` | `List UInt8 → Option UInt8`        | folds **within one block**, to one byte |
| `b32BlockApply` | `List UInt8 → Option (List UInt8)` | folds within one block, to five bytes   |
| `bitBlockIso`   | `Iso (List UInt8) UInt8`           | the left side is digit _characters_     |
| `b64BlockIso`   | `Iso (List UInt8) (List UInt8)`    | same                                    |

`grep -rn 'radix|base : Nat|pow' BaseN/*.lean` → **nothing.** There is no radix parameter
anywhere, and no function whose codomain is `Nat` other than the single-digit `digVal`
family.

So:

- `"300"` → `[3,0,0]` → three bytes. The number `300` never exists.
- `"01100001"` → eight bytes of `'0'`/`'1'` carrying one byte.
- Seven alphabets (`bitVal`, `quartetVal`, `octToVal`, `hexToNibble`, `b32ToVal`,
  `b64ToVal`, `digVal`) are seven copies of one derivation, each `Nat → Nat` with a
  radix-bounded validity predicate.

**That is the layer this change adds: one rung, radix-parameterised, codomain `Nat`.**

## D1 — Why one generic layer and not seven

The seven alphabets differ only in the byte-to-value map. Everything else — the fold, the
canonical digits, the quotient, the law — is identical across radices.

**Decision: one `digitVal` parameterised by radix, one fold, one inverse.** The per-base
functions become proved-equal specialisations. The alternative (seven independent
`Nat` layers) is seven times the proofs and seven chances to disagree.

The generic `digitVal` must be total in its radix argument in the sense that an
out-of-range radix is a _caller_ error, not a silent misbehaviour; `2 ≤ b` is a hypothesis
on everything that uses it, and `numeralIso` carries it explicitly rather than assuming.

## D2 — The codomain is the quotient, and that is the whole point

`basen-nat-iso` §Risk identified this for base 10 and it generalises unchanged:

> stating the `Iso` over raw `Bytes n` or raw `List UInt8` instead of the quotient means
> `"001"` and `"01"` have no image and the `law` field is false.

`"007"` and `"7"` are two spellings of one number. Under a raw-syntax `Iso` they are two
distinct inputs with no common image, so `apply`/`unapply` cannot be inverse — the law is
**false**, not unproved.

**Decision: `numeralIso : (b : Nat) → 2 ≤ b → Iso Nat (Normal (List UInt8) (trimFor b))`.**
The equivalence lives in the **codomain**. `codec`'s `Normal` layer already supplies the
machinery (`Normal`, `Normalizer`, `fill`, `fill_surj`, `fill_fixed`, `decodeNormal`), and
its own docstring states the thesis this change relies on: _"the honest object is not a
relaxed law, it is a bijection with the quotient of the concrete syntax by the
information-free variation."_

`toNat`/`ofNat` are then **total functions** on the quotient representative and its value,
not partial relations — the partiality is all in `decodeNormal`, outside the `Iso`.

## D3 — What is information-free variation, per radix

| variation                             | absorbed?         | reason                                 |
| ------------------------------------- | ----------------- | -------------------------------------- |
| leading zeros (`007`)                 | **yes**           | changes no value                       |
| leading whitespace (`  7`)            | **yes**           | the stated decimal policy, generalised |
| trailing whitespace                   | **no**            | not claimed; a format's business       |
| wrong-alphabet digit (`9` in radix 8) | **no** — rejected | would change or destroy the value      |
| trailing data (`7x`)                  | **no** — rejected |                                        |
| `0x`/`0o`/`0b` prefix                 | **no**            | a prefix names a _radix_, not padding  |

**The prefix row is the one that needs care and is stated explicitly.** In the C-family
idiom a leading zero can change the radix (`017` is octal). This change's numeral layer is
_explicitly radix-parameterised_, so a radix-prefix is not its concern — a caller that
wants prefix-driven radix selection does that **before** calling in. Absorbing a leading
zero is therefore safe here specifically because the radix was already given.

`basen-uppercase-prepass` records the same family of caution for Base16 case folding.
That change is separate and untouched; the two do not overlap, because case folding
concerns the _alphabet_ and this concerns _padding_.

## D4 — Zero, and the empty sequence

Three candidate spellings for zero:

1. the empty sequence `""`,
2. the radix's single zero digit (`"0"`, or `"0000"` in base 2),
3. a fixed-width padded form.

**Decision: (2).** `ofNat b 0` yields the single zero digit and nothing else. The empty
sequence is **not** the canonical spelling of zero at any radix, because (a) `basen-nat-iso`
measured the existing encoder producing an empty encoding for zero as a _defect_, and
(b) an empty canonical numeral makes `""` ambiguous between "zero" and "nothing was
written". The quotient absorbs `"00"` as a name for `"0"`, which is the useful direction.

The requirement states this once rather than per base, so no base can quietly differ.

## D5 — The padded bases: what composes and what does not

Base 32/64 carry padding **inside** the value type:

```lean
inductive B64 where
  | nil
  | full (b0 b1 b2 : UInt8) (rest : B64)
  | tail1 (b0 : UInt8)
  | tail2 (b0 b1 : UInt8)
```

`tail1`/`tail2` exist because 1–2 bytes cannot fill a 3-byte block; that is what `=`
encodes. A **numeral has no such notion** — 300 is 300 whether you needed two digits or
twenty — so there is no "padded numeral" and no tail layer to fold through.

**Decision: `numeralIso` does not touch the block/tail spine.** It folds the digit sequence
directly. Reading a padded base-64 encoding as a number is a _separate_ composition over
the block layer, which this change does not claim and its requirement says so explicitly
(D5's third scenario).

This is the constraint most likely to be violated by a careless implementation — reaching
for `b64BlockIso` because it is right there — which is why it is a named requirement rather
than a note.

## D6 — The block isos are kept and proved equal

The six power-of-two block isos are special cases of the generic fold. Two options:

1. **Replace** them with derivations — deletes six independent proofs, but breaks any
   downstream signature and makes the fast path a computation rather than a literal.
2. **Keep** them and prove `blockIso = toNat restricted to the block`.

**Decision: (2)**, following `Codec.decodeWhole_eq`'s precedent — the fast surface is kept
and _proved equal to the specification_, rather than the specification being reimplemented
in terms of it. Nothing downstream breaks; the duplication stops being _independent_ code,
which is what made it a risk.

The equality must be mutation-tested by perturbing a block iso's digit order. An equality
that holds vacuously is not a check.

## D7 — What this enables, and what it deliberately does not do

Once `toNat`/`ofNat` exist, **varint is radix 128 with a continuation bit** — a fold with a
different terminator and no alphabet at all. That is a _different_ requirement (a run
triple over bytes, benchmarked) and this change stops before it, so the numeral layer can
land and be measured on its own.

`Int` is likewise deferred: `-0x10` and `-010` are the same variation one level up, and
`-0` raises sign canonicalisation, which is a design question this change should not answer
in passing.

## D8 — Archive ordering and the parked changes

This change adds three requirements to `basen`. Two other changes also add to `basen`:

| change                    | status                        | overlap                                                                                           |
| ------------------------- | ----------------------------- | ------------------------------------------------------------------------------------------------- |
| `basen-nat-iso`           | **superseded by this change** | its three ADDED requirements are the base-10 slice of this one's; retire it rather than land both |
| `basen-uppercase-prepass` | parked                        | different requirements (case folding vs padding); no overlap                                      |

**`basen-nat-iso` is retired, not merged.** Its analysis is carried forward in D2/D4 above
and its `Nat`-first scoping is adopted. Landing both would put two `Nat` codecs in one
package with two quotient stories.

**`basen-uppercase-prepass` is untouched** and stays parked on the owner's library-division
decision. This change does not make that decision.
