# Proposal — `basen-radix`

## Why

**`basen` cannot convert a numeral to its value.** Every base decodes text to `List UInt8`
— a sequence of _digit characters_ — and never to a number. Measured on the current
tree (`../lean-basen`):

```
digVal ('7')            → 7            -- ONE digit byte to ONE digit value
bitBlockApply "01100001" → 0x61        -- eight digit bytes to ONE byte, within a block
b32BlockApply 8 digits   → 5 bytes     -- eight digit bytes to FIVE bytes
```

There is no function anywhere in `BaseN/` that folds a **list** of digit bytes into the
number they denote. `grep -rn 'radix|base : Nat|pow' BaseN/*.lean` returns nothing: every
base hard-codes its own way of packing digits _within one block_, and the value never
exists as a `Nat`.

Two consequences, both live today:

1. **Text-to-number is the caller's problem.** A consumer who wants `300` from `"300"`, or
   `0x61` from `"01100001"`, must write the fold themselves — and the fold is the part
   with the interesting laws (canonicity, injectivity, no leading zeros).
2. **`List UInt8` is not a number.** Eight bytes of `'0'`/`'1'` to carry one byte is the
   wire cost of a _numeral_, not of a value. Anyone who reads a `basen` value as "the
   number" is reading a spelling; the arithmetic is not there.

This is the gap `basen-nat-iso` found for base 10 alone. It is not a decimal problem — it
is the same missing rung for **all seven** radices, and the seven hand-rolled alphabets
(`bitVal`, `quartetVal`, `octToVal`, `hexToNibble`, `b32ToVal`, `b64ToVal`, `digVal`)
are seven copies of one derivation.

## What changes

Add a **radix-generic numeral layer** to `basen`. Three functions serve all seven bases:

```lean
digitVal : (radix : Nat) → UInt8 → Option Nat   -- one digit byte to its digit value
toNat    : (radix : Nat) → List UInt8 → Option Nat  -- fold: acc := acc * radix + d
ofNat    : (radix : Nat) → Nat → List UInt8     -- canonical digits, minimal, no padding
```

and one `Iso` per radix, over the quotient of the information-free variation:

```lean
numeralIso : (b : Nat) → 2 ≤ b → Iso Nat (Normal (List UInt8) (trimFor b))
```

A numeral is a _spelling_; the number is the image. `"007"`, `"  7"` and `"7"` are three
names for the same image, and the quotient is what makes the `Iso` an **ordinary total
bijection** rather than a relaxed law — `codec`'s `Normal` layer already supplies exactly
this (`Normal`, `Normalizer`, `fill`, `fill_surj`, `fill_fixed`, `decodeNormal`), so the
equivalence lives in the **codomain** and nothing is weakened.

**The design constraint that shapes the whole change: `numeralIso` sits ABOVE the padded
bases' tail layer, and does not reuse it.** Base 32/64 have padding-dependent value types
(`B64.tail1`/`B64.tail2` carry 1–2 bytes; that is why `=` exists). A numeral has no such
notion — 300 is 300 whether you needed two digits or twenty — so `numeralIso` folds the
digit sequence directly and never constructs a `B32`/`B64` spine. Reading a padded
encoding as a number is a **separate** composition, and this change does not claim it.

| layer                      | type                                  | status                   |
| -------------------------- | ------------------------------------- | ------------------------ |
| digit byte → digit value   | `digitVal : Nat → UInt8 → Option Nat` | **this change**          |
| digit list → the number    | `toNat` / `ofNat`                     | **this change**          |
| number ↔ canonical numeral | `numeralIso` over `Normal`            | **this change**          |
| digits ↔ bytes (blocks)    | the seven block `Iso`s                | **exists and is proved** |
| padded value type          | `B32` / `B64` spines                  | **exists; untouched**    |

### The block `Iso`s are tied to the fold, not replaced

There are **seven** block isos, not six — base 10's `digBlockIso` was silently dropped in an
earlier draft, which is the "unexplained 6-of-7 list" shape. They are **canonicity-filtered
restrictions** of the generic fold, **not special cases of it**: base 64 re-encodes and
compares (`Base64.lean:265-270`), base 10 rejects `n > 255` (`Base10.lean:121-128`), base 32
rejects a pad byte (`Base32.lean:368`), and the `UInt8`-valued bases truncate through
`UInt8.ofNat`. So the theorem is an **implication pair**, in two schemas by codomain — see
`design.md` D6. The block isos are kept as **fast paths** and each gains a constraining
theorem, which is the point; **no existing declaration's statement changes**.

## Capabilities

### New Capabilities

None.

### Modified Capabilities

- `basen`: three new requirements — that a numeral denotes a number (the generic
  `digitVal`/`toNat`/`ofNat` triple, one definition for all seven radices); that a number
  is its canonical numeral modulo information-free variation (the `numeralIso` over the
  `Normal` quotient, with leading zeros and leading whitespace as _names_, not errors);
  and that the block isos are tied to the generic fold by a canonicity-filtered implication
  (they are guards over the fold, not equal to it — see `design.md` D6).

## Impact

- **`../lean-basen/BaseN/`** — a new `Radix.lean` carrying the three functions and the
  `numeralIso`; each `BaseN/BaseN.lean` gains a proved-equality theorem tying its block
  iso to the generic fold. **No existing declaration's statement changes**; the per-base
  alphabets (`bitVal` etc.) become proved-equal specialisations of `digitVal`.
- **`../lean-basen/Axioms.lean`** — the new laws must be pinned; the gate fails the build
  until they are, which is its job.
- **`openspec/specs/basen/spec.md`** — three requirements added via this change's delta.
- **`basen-nat-iso` — SUPERSEDED by this change and retired here.** That change is the
  base-10-only slice of exactly this layer: same quotient argument, same "a number is
  isomorphic to its canonical numeral", same leading-zero policy. Doing it once for seven
  radices is strictly better than doing base 10 and then generalising. Its analysis is
  sound and is **carried forward**, not discarded — in particular its `Nat`-first scoping
  and its "the equivalence lives in the codomain" decision.
- **`basen-uppercase-prepass` — NOT touched.** It is a separate concern (case folding in
  Base16) and its delta adds different requirements. It stays parked on the owner's
  library-division decision, which this change does not make.
- **`varint` is enabled, not delivered.** Once `ofNat`/`toNat` exist, varint is radix 128
  with a continuation bit — a fold with a different terminator, not a new alphabet. This
  change deliberately stops before it so the numeral layer can land and be measured first.

## Non-goals

- **`Int`.** `-0x10` and `-010` are the same information-free variation one level up, and
  they raise sign canonicalisation (`-0`), which is a real design question. `Nat` first.
- **Reading a padded encoding as a number.** Base 32/64 carry padding _inside_ the value
  type; folding a padded string to a `Nat` is a composition this change does not claim.
- **Changing any existing base's byte-level law.** `roundtrip`, `decodeFull_canonical`,
  `encode_injective` and the rejection laws stay as they are.
- **Replacing the block isos.** They are kept and tied to the fold by a theorem.

## Risk

**The one way this fails:** stating `numeralIso` over raw `List UInt8` or raw `Bytes n`
instead of the quotient. Then `"007"` and `"7"` have no common image and the `law` field is
false — precisely the defect `basen-nat-iso` §Risk identified for base 10, here generalised.
The first task is therefore to settle the codomain and prove the three-spelling witness
**before** any other proof, and to mutate that witness to confirm it fires.

**The second way:** letting the generic fold silently disagree with a base's existing block
iso. The proved-equality theorems are what prevent it, and they must be mutation-tested by
perturbing each block iso's digit order.
