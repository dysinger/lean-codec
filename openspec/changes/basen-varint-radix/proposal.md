# Proposal — `basen-varint-radix`

## Why

`basen-radix` (archived 2026-11-15) added a radix-generic numeral layer —
`digitVal` / `toNat` / `ofNat` over `Nat`, plus `numeralIso` per radix over the `Normal`
quotient — for seven radices, and its `tasks.md` §7.1 named `varint` as **"enabled by this
layer but not delivered"**:

> "Once `ofNat`/`toNat` exist, varint is radix 128 with a continuation bit — a fold with a
> different terminator, not a new alphabet."

That claim is half right, and the half that is wrong is the load-bearing half. **Measured
today, in `../lean-basen`:**

```
Radix.digitVal 128 0x30      ->  none      -- '0' is not a digit of any served radix
Radix.digitVal 64  0x30      ->  some 52
Radix.toNat    128 [0x01,0x02] ->  none
```

`digitVal` is a **seven-arm dispatch chain on literal radix values**, terminated by
`else none` (`BaseN/Radix.lean:90-113`). Radix 128 falls off the end and returns `none`
for _every_ byte. So "varint is radix 128" is not something the layer can express: there is
no path from `Nat`-width to a wide radix without an eighth arm, and an eighth arm is not a
one-line addition — see "What widening actually costs" below.

`IsRadix` is likewise a **closed `inductive`** with exactly seven constructors
(`BaseN/Radix.lean:524-531`):

```lean
inductive IsRadix : Nat → Prop
  | b2 | b4 | b8 | b10 | b16 | b32 | b64
```

with an exhaustive-match surface of **four sites** (`Radix.lean:540`,
`RadixCodec.lean:214`, `:536`, `:943`) and a bound `isRadix_le64` used at **six** sites.
Every one of those four sites is a _positional-radix_ proof — `digitVal_byteOfDigit` proves
that the radix's own digit emitter round-trips through its own alphabet, which is a
statement about a fixed-width positional alphabet. **None of them is true of 128**, and
adding `| b128` to the inductive would force every one of them to invent a case that is
either vacuous or false.

So this change exists to settle a question the previous change left implicit, and it is
**structural, not syntactic**: what does it mean for this package to "serve" a radix, and
does the numeral layer's contract cover a _terminator-delimited_ numeral or only a
_positional_ one?

## What changes

**Split the one predicate into two, by what each actually means.**

Today `IsRadix r` means "the numeral layer's digit-value function knows this radix's
alphabet". That is a statement about **recognising digits**, and it silently also has to
carry a second, stronger claim that four proofs depend on: _this radix is positional, with
a fixed-width alphabet whose emitters round-trip_. The two are conflated, and that
conflation is precisely what blocks radix 128.

```lean
-- today
inductive IsRadix : Nat → Prop          -- 7 constructors, both meanings at once

-- after
inductive IsRadix : Nat → Prop          -- UNCHANGED: the positional seven
  | b2 | b4 | b8 | b10 | b16 | b32 | b64

inductive ServesDigits : Nat → Prop     -- the alphabet claim alone
  | ofRadix  : IsRadix r → ServesDigits r
  | b128     : ServesDigits 128
```

`ServesDigits` is the predicate `digitVal`, `byteOfDigit` and the `Normal`-quotient
machinery take. `IsRadix` stays exactly as it is, so **the four exhaustive-match sites and
the six `isRadix_le64` uses are untouched** — the widening is additive and provably
does not perturb the positional layer.

Varint is then **a run with a terminator**, exactly as `codec`'s spec already prescribes
(_"Runs are derived, not constructors"_ — _"it is `takeWhile highBitSet` + an `iso`
folding the 7-bit groups"_), and **not** a radix at all. The two additions compose:

| layer              | what it says                                                 | where               |
| ------------------ | ------------------------------------------------------------ | ------------------- |
| `ServesDigits 128` | `digitVal 128` understands `0x80–0xFF` as 7-bit groups       | `BaseN/Radix.lean`  |
| a varint run       | a maximal high-bit-set run, then a terminator byte           | `BaseN/Varint.lean` |
| the fold           | `toNat 128` over the 8-bit characters, continuation stripped | reused              |

## The design fork, stated as the change's central question

Two shapes were considered. **The proposal argues for the second and the design (`design.md`)
must record the reasoning, because the first is the intuitive one.**

**Shape A — widen `IsRadix` with `| b128`.** One predicate, one numeral layer, everything
composes: `numeralIso 128` comes for free. Cost: `IsRadix` stops meaning "RFC 4648 base"
and starts meaning "any numeral system this package supports"; the four exhaustive matches
each need an eighth arm; and `isRadix_le64` becomes false, so its six uses need a
re-derivation — and at least two of them (`byteOfDigitNat_lt`'s `d < radix → byte < 256`
and `byteOfDigitNat_ne_32`) are **outright false at 128**: with `d` up to 127 the emitted
byte argument exceeds 127, and the "is this byte a blank" inequality has to be re-proved
for a window that spans it.

**Shape B — split the predicate (this proposal).** `IsRadix` keeps seven constructors and
its meaning; a second predicate carries the alphabet claim, which is the only thing
`digitVal` actually needs. Varint is a run, not a radix. Cost: two predicates to keep
straight, and `ServesDigits` must be _proved_ to imply everything the shared machinery
uses — that proof is the change's real content, and D2 of `design.md` is where it lands.

**Why B, in one sentence:** `IsRadix`'s four exhaustive matches are _positional_ proofs
(an emitter round-tripping through a fixed-width alphabet), and a radix that is
terminator-delimited has no fixed width — so the honest statement is that varint is not a
positional radix, and the type should say so rather than growing a case that forces four
correct proofs to acquire four dishonest arms.

## Capabilities

### Modified Capabilities

- `basen`: one requirement **added** — that a _terminator-delimited_ numeral is served by
  the package as a run, distinguished from a positional radix — and one requirement
  **modified** — the numeral layer's "serves these radices" statement is narrowed to what it
  actually establishes (digit recognition), with the positional claim stated separately.

## Impact

- **`../lean-basen/BaseN/Radix.lean`** — `ServesDigits` added; `digitVal`'s signature
  changes from `Nat → UInt8 → Option Nat` to take `ServesDigits`, **or** keeps `Nat` and
  the predicate is used only where the wide case matters (see `design.md` D1 — this is a
  signature decision with a real trade-off, deliberately left to the design pass).
- **`../lean-basen/BaseN/Varint.lean`** — new: the run value, the fold, the roundtrip.
- **`../lean-basen/Axioms.lean`** — new laws pinned; the gate fails until they are.
- **No existing declaration's statement changes** is the target, and is **the thing this
  change is most likely to be wrong about** — the `digitVal` signature question above may
  make it false. Stated here so the design pass has to answer it rather than discover it.

## Non-goals

- **Delivering varint's optimisation work.** It is a run triple over bytes with its own
  benchmark; this change lands the layer, not the performance story.
- **`Int`-valued numerals.** Still deferred; `-0` remains a design question in its own right.
- **Changing any of the seven RFC 4648 bases.** Their laws are untouched by construction if
  Shape B holds, and that is the property to verify, not assume.
- **A general "arbitrary radix" layer.** `ServesDigits` is an explicit inductive with a
  closed set of constructors, not a `2 ≤ r` side condition. An open predicate would need
  every existing proof to be re-stated over a variable radix, which `Radix.lean`'s
  dispatch chain cannot support.
