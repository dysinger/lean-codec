# Proposal — `basen-nat-iso`

## Why

**`basen` has no numeric codec.** Every base is a `Codec (List UInt8)` over
fixed-width digit blocks, so a caller who wants a number gets a byte list and does
the arithmetic themselves. The byte array is a legitimate _intermediate_, but it is
not the deliverable: a user asking for base-10 decoding wants a `Nat` (or an
`Integer`), and today there is nothing to call.

Measured on the current tree (`/tmp` probes against `BaseN.Base10`):

```
encodeDig [0x01]        → 3 digit bytes   ("001")   -- zero-padded to a block
encodeDig []            → 0 digit bytes   (""   )   -- zero has no digit
decodeRepeat  "001"     → [[], [1]]                 -- two answers
decodeRepeat  "000001"  → [[], [0], [0,1]]          -- three answers
decodeFull    "001"     → some [1]                  -- unique at full consumption
decodeFull    "01"      → none                      -- 2 is not a multiple of 3
```

Two of those are defects for a numeral and one is a constraint:

- the encoder **emits** leading zeros (`"001"`), so zero-padding is baked into the
  _encoder_ rather than merely tolerated by a decoder;
- `Nat 0` encodes to the **empty** byte list, so zero has no numeral at all;
- the byte layer's rule is _length must be a multiple of three_, so `"1"` and `"01"`
  are not spellings of one — they are rejected at different stages.

Composing `Nat → List UInt8 → bytes` therefore cannot yield a numeral `Iso`: it
inherits all three.

`../fstar-codec` records the same class as `[D12]`/`[D13]` and reports `varint` and
`digits_to_int` as ⛔ **false** over their library's decoder — `"01"` accepted while
`enc 1 = "1"` makes `Iso.law` a false proposition, not an unproved one. It also
records that the lenient layer was **not built** (`[W9]`). This change is the Lean
answer to both.

## What changes

Add a `Nat`-valued decimal codec to `basen`, and the lenient layer that lets a
caller accept lax spellings without weakening the law.

**The layering is three steps, each already or newly proved separately:**

| layer                                  | type                                           | status                   |
| -------------------------------------- | ---------------------------------------------- | ------------------------ |
| bytes ↔ byte list                      | `Codec (List UInt8)` (`digElem`, `decodeFull`) | **exists and is proved** |
| bytes ↔ `Nat` (strict, minimal digits) | new `Codec Nat`                                | this change              |
| lax input → canonical input            | `Normal`-style layer **outside** the `Iso`     | this change              |

The middle layer is `Iso.ofTotal`-shaped only if the byte type carries canonicity;
`Bytes n` does not (`"001"` is a valid `Bytes 3` no `Nat` maps to), so the strict
`Iso` is `Nat ↔ (canonical non-empty digit bytes)` and the laxity lives in the third
layer, never in `Iso.law`.

## Decisions this change must make, and cannot defer

1. **`Nat` only, or `Integer` too?** Sign changes the wire format (a leading `-`),
   and `-0` is a second spelling of `0` — the same defect one level up. Scoping
   `Nat` first keeps `-0` out of the first change; `Integer` is a follow-on with its
   own witness. **Recommendation: `Nat` first.**
2. **Minimal digits.** `enc 1 = "1"`, `enc 0 = "0"`. Not zero-padded, not empty.
   This is the only choice under which the user's expectation and the RFC bases'
   block structure can coexist.
3. **What the strict decoder rejects.** `"01"` (leading zero), `""` (no digit), and
   any non-digit. Rejection — not silent trimming — is what makes `law_bwd` _true_.
4. **Where leniency lives.** A separately-proved `Normal` layer composed outside the
   `Iso`, following base16's `decodeHexFold` precedent (`foldList` outside the
   strict `Iso`) rather than a second `Codec Nat`. Two codecs with one name is the
   contradiction `[D12]` warns about.

## Non-goals

- Changing any existing base's byte-level law. `digElem`'s `roundtrip`,
  `decodeFull_B10_char`, `encode_injective` and `decodeFull_canonical` stay as they
  are; the `Nat` layer is _above_ them or beside them, not a rewrite of them.
- Changing the `codec` core. `Iso.ofTotal` and the `Normal` layer already exist
  (`Codec/Normal.lean`); nothing new is needed there.
- Touching the other six bases until the decimal shape is settled and proved.

## Risk

**The one way this fails:** if the strict `Iso` is stated over `Bytes n` instead of a
canonical-digit type, `"001"` has no image and the `law` field is false — the exact
defect this change exists to avoid. The first task is therefore to decide the
codomain type and prove the `"01"`-rejection witness **before** any other proof is
attempted, and to mutate that witness to confirm it fires.
