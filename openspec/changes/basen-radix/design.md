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

Three greps, each returning **zero**, and each written with `-E` so the alternation is a
regex rather than a literal (a first draft wrote `grep -rn 'radix|base : Nat|pow'`, which is
BRE — `|` is literal there, so it exits 1 on _any_ tree and proves nothing):

```
grep -rnE 'radix'       BaseN/*.lean | wc -l   # 0
grep -rnE 'base : Nat'  BaseN/*.lean | wc -l   # 0
grep -rnE 'pow'         BaseN/*.lean | wc -l   # 0
```

**The bounded claim, because the unbounded one is false:** no function folds a digit _list_ to
a `Nat` (`grep -rnE 'def (toNat|ofNat|numeral)' BaseN/*.lean` → none; every digit-list fold
lands in `Option UInt8` or `Option (List UInt8)`). There **are** fourteen other `Nat → Nat`
helpers — the seven alphabets below plus their seven inverse encoders
(`valToBit`, `valToQuartet`, `valToOct`, `valToDig`, `valToB32`, `valToB64`, `nibbleToHex`)
and the per-bit selector `bitAt` — so "no `Nat`-codomain function other than `digVal`" would
have been wrong, and it does not weaken the point: none of them takes a list.

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

**The decode direction is what gets unified; the encode direction splits at radix 2 only —
and an earlier draft got that wrong.** It said "at radices 2, 4 and 8 the encoders carry
deliberately non-injective fallbacks". Measured, only radix 2 does:

| radix | inverse map                                                   | injective? |
| ----- | ------------------------------------------------------------- | ---------- |
| 2     | `valToBit b := if b = 0 then 48 else 49` (`Base2.lean:49-50`) | **no**     |
| 4     | `valToQuartet d := 48 + d` (`Base4.lean:37`)                  | **yes**    |
| 8     | `valToOct d := 48 + d` (`Base8.lean:37`)                      | **yes**    |

`Base2.lean:40-48` explains the sentinel pair and says "that is sound only because every _use_
supplies a proof `b <= 1`", and explicitly "Do not 'fix' one sentinel to match the other". So:

- the **seven digit-value functions** (`bitVal`, `quartetVal`, `octToVal`, `hexToNibble`,
  `b32ToVal`, `b64ToVal`, `digVal`) SHALL be proved equal to `digitVal` at their radix: 7
  equalities, and that is the decode direction;
- **only radix 2's `valToBit` SHALL NOT be rewritten.** At 4 and 8 the inverse maps are
  injective, so an `ofNat`-agreement law is _provable_ there and is a bonus, not an
  obligation. This change supplies `ofNat` as its own encoder regardless and does not claim
  `valTo*` are copies of it.

**Decision: one `digitVal` parameterised by radix, one fold, one inverse.** The per-base
functions become proved-equal specialisations. The alternative (seven independent
`Nat` layers) is seven times the proofs and seven chances to disagree.

The generic `digitVal` must be total in its radix argument in the sense that an
out-of-range radix is a _caller_ error, not a silent misbehaviour; `2 ≤ b` is a hypothesis
on everything that uses it, and `numeralIso` carries it explicitly rather than assuming.

## D2 — The codomain is the quotient, and that is the whole point

**The argument, and why it survives the deletion of `basen-nat-iso`.** That change (now
retired, `tasks.md` §6.1) stated this for base 10; the reasoning is self-contained, so it is
re-derived here rather than cited to a file that no longer exists — which would be the
"pointer whose method does not reach its target" defect:

> stating the `Iso` over raw `Bytes n` or raw `List UInt8` instead of the quotient means
> `"001"` and `"01"` have no image and the `law` field is false.

Directly, without the citation: `Iso.law` (`Codec/Iso.lean`) is
`apply a = some b <-> unapply b = some a`. On a raw-syntax codomain, `"007"` and `"7"` are
distinct left-hand values that must map to the one number `7`, so `unapply 7` cannot be
`some` of both and the `->` direction fails. No reordering of the proof fixes that; the
object is wrong.

`"007"` and `"7"` are two spellings of one number. Under a raw-syntax `Iso` they are two
distinct inputs with no common image, so `apply`/`unapply` cannot be inverse — the law is
**false**, not unproved.

**Decision: `numeralIso : (b : Nat) → 2 ≤ b → Iso Nat (Normal (List UInt8) (trimFor b))`.**
The equivalence lives in the **codomain**. `codec`'s `Normal` layer already supplies the
machinery (`Normal`, `Normalizer`, `fill`, `fill_surj`, `fill_fixed`, `decodeNormal`), and
its own docstring states the thesis this change relies on: _"the honest object is not a
relaxed law, it is a bijection with the quotient of the concrete syntax by the
information-free variation."_

`ofNat` is **total** (`Nat -> List UInt8`, every number has a numeral). `toNat` is **not**:
it is `Option`-valued, total on the numeral subset of the quotient and `none` elsewhere —
which is exactly why it can be `Iso.apply` and why the law is an `iff` rather than an
equality. An earlier draft called the pair "total functions", which is false of `toNat` and
would mislead anyone writing the `Iso`.

**One consequence to state, because "unconditionally" is easy to over-read.** The `Iso`'s
inverse law holds unconditionally **on the quotient**. A _spelling_ reaches a number via
`trim` first, and `trim`'s totality and idempotence are a **separate** obligation
(task 2.1) — not part of the `Iso`. `decodeNormal`'s own docstring (`Codec/Normal.lean`) is
at pains to say it must never be presented as a codec value, for this reason.

## D3 — What is information-free variation, per radix

| variation                             | absorbed?         | reason                                    |
| ------------------------------------- | ----------------- | ----------------------------------------- |
| leading zeros (`007`)                 | **yes**           | changes no value                          |
| leading whitespace (`  7`)            | **yes**           | the stated decimal policy, generalised    |
| trailing whitespace (`"7 "`)          | **no** — rejected | a trailing blank is not part of a numeral |
| wrong-alphabet digit (`9` in radix 8) | **no** — rejected | would change or destroy the value         |
| trailing data (`7x`)                  | **no** — rejected |                                           |
| `0x`/`0o`/`0b` prefix                 | **no**            | a prefix names a _radix_, not padding     |

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

**Decision: (2).** `ofNat b 0` yields the base's single zero digit and nothing else.

**The justification was rewritten after review, because the first version's two reasons were
both defective:**

- It cited "`basen-nat-iso` measured the existing encoder producing an empty encoding for zero
  as a defect" — **unverifiable**, because that change was deleted (`tasks.md` §6.1) and, more
  fundamentally, **no whole-number encoder exists in the tree**, which is this change's own
  premise. There is nothing that could have emitted an empty encoding for zero.
- It argued `""` is "ambiguous between zero and nothing was written" — true of the **raw
  syntax**, **false of the quotient**, where `""` and `"0"` would be the same class. That is
  the same status `"007"` has, so the argument does not distinguish the candidates.

**The real reasons, which do distinguish them:**

1. **A zero-length numeral is not a numeral in any framed format.** JSON's number grammar
   requires at least one digit (RFC 8259 §6); ISO 8601 requires at least one digit in every
   field; YAML's `!!int` is not a single decimal regex — it carries base-60, octal, hex and
   binary forms — but every one of them requires at least one digit. An empty numeral is
   indistinguishable from "field absent", which is a property of the _wire_, not of the
   quotient. (An earlier draft stated a YAML regex the YAML spec does not use; weakened.)
2. **It is the only choice that makes `trim` idempotent and `ofNat` minimal simultaneously.**
   If the canonical zero were `""`, then `ofNat b 0 = []`, and `trim` would have to map every
   zero-spelling — including the single zero digit — to `[]`, leaving `trim` unable to
   distinguish a zero numeral from a malformed empty input.

**The zero digit is per-base data, not a uniform constant.** `ofNat b 0` is
`[toByte (valToDigit b 0)]`, i.e. whatever character that base's own alphabet maps to `0`.
Measured, that is `0x30` (`'0'`) at all seven radices today — so the _result_ is uniform while
the _definition_ is per-base. The requirement states the rule once; it does not claim the
definition is radix-independent.

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
encodes.

**The claim here was narrowed after review.** The first draft said "a numeral has no such
notion" — but padding and numerals are not strangers: a fixed-width base64url numeral is a
real object (JOSE/JWK `n`, WebAuthn credential ids), and in that setting a padded encoding _is_
naturally read as a number. The defensible claim is narrower:

> **padding inside `B32`/`B64` encodes a _length class_, not a value-irrelevant variation**, so
> it cannot be a `Normal` quotient and `numeralIso` must not go through it. `numeralIso` is
> **minimal-width**; a fixed-width base64 numeral is a legitimate but _different_ object, which
> this change does not build.

That keeps the tail spine out of scope for the right reason — it carries a length, which a
minimal-width numeral does not — rather than for a false one.

**Decision: `numeralIso` does not touch the block/tail spine.** It folds the digit sequence
directly. Reading a padded base-64 encoding as a number is a _separate_ composition over
the block layer, which this change does not claim and its requirement says so explicitly
(D5's third scenario).

This is the constraint most likely to be violated by a careless implementation — reaching
for `b64BlockIso` because it is right there — which is why it is a named requirement rather
than a note.

## D6 — The block isos are canonicity-filtered restrictions, not "special cases"

**This section was rewritten after review, and the first version was wrong in a way that made
task 3.2 unprovable.** Recorded because the wrong version is the intuitive one.

The first draft said the block isos "are **special cases** of the generic fold: a block of
`k` radix-`b` digits _is_ `toNat b` on that block", and therefore `blockIso = toNat`
restricted. **Measured, that is false**, for three separate reasons:

| base     | what the block `apply` actually does beyond folding                                                | evidence                                     |
| -------- | -------------------------------------------------------------------------------------------------- | -------------------------------------------- |
| 64       | `b64BlockDecodeLenient` **then** re-encode-and-compare, so `apply` accepts only _canonical_ blocks | `BaseN/Base64.lean:265-270`                  |
| 32       | the lenient decoder **rejects the pad byte `61` in the first two digits**                          | `BaseN/Base32.lean:366-412` (test at `:368`) |
| 10       | `digBlockApply` returns `none` when `n > 255` — a 3-digit decimal block denotes up to 999          | `BaseN/Base10.lean:121-128`                  |
| 2/4/8/16 | the fold lands in `UInt8` via `UInt8.ofNat`, which **truncates mod 256**                           | `BaseN/Base2.lean:129-175`                   |

So `b64BlockApply` is **not** `toNat 64` restricted to four digits — on most digit strings
`toNat 64` yields a value while `b64BlockApply` yields `none`. The correct statement is a
**canonicity-filtered restriction**, a pair of implications:

**And there are TWO schemas, not one**, because the seven blocks split by codomain. A single
`BlockVal` placeholder does not typecheck across both:

| bases           | block `apply` type                 | schema |
| --------------- | ---------------------------------- | ------ |
| 2, 4, 8, 10, 16 | `List UInt8 → Option UInt8`        | `_8`   |
| 32, 64          | `List UInt8 → Option (List UInt8)` | `_L`   |

```lean
-- schema _8 (bitBlockIso, quartetBlockIso, octBlockIso, digBlockIso, hexBlockIso)
theorem blockApply8_of_toNat (cs : List UInt8) (n : Nat) :
    toNat radix cs = some n -> blockApply cs = some (UInt8.ofNat n)
theorem toNat_of_blockApply8 (cs : List UInt8) (v : UInt8) :
    blockApply cs = some v -> toNat radix cs = some v.toNat

-- schema _L (b32BlockIso, b64BlockIso)
theorem blockApplyL_of_toNat (cs : List UInt8) (n : Nat) :
    toNat radix cs = some n -> blockApply cs = some (bytesOfNat n)
theorem toNat_of_blockApplyL (cs : List UInt8) (v : List UInt8) :
    blockApply cs = some v -> toNat radix cs = some (natOfBytes v)
```

For `_8`, the transport is a **truncating** `UInt8.ofNat` whose losslessness _is part of the
theorem_ (`n < 256` comes from the block's own guard). For `_L`, the guard that makes `→` hold
is base 64's re-encode-and-compare, not a range bound.

**Decision: keep the block isos and prove the filtered-restriction theorems**, following
`Codec.decodeWhole_eq`'s precedent in spirit — the fast surface is kept and tied to the
specification by a theorem rather than reimplemented. "Nothing downstream breaks" is replaced
by the accurate statement: **no existing _statement_ changes**, and each block iso gains a
constraining theorem, which is the point.

**There are seven block isos, not six.** `digBlockIso` (`BaseN/Base10.lean:250`) is base 10's,
the same shape — three decimal digits folded to a byte value, guarded by `n <= 255`. It is
excluded from the _power-of-two_ grouping only because its block is three decimal digits
rather than `k` bits. The first draft enumerated six and never mentioned base 10: an
unexplained 6-of-7 list, the "completeness claim that fails silently" shape. **It SHALL get a
theorem too**, in its own group, so the enumeration is 7-of-7.

**And the equality is not "proved equal" in the `=` sense** — that phrasing invites an
`rfl`-shaped attempt that will not close. The theorem is the implication pair above.
Mutation-test by perturbing a block iso's digit order; the implication then fails.

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
