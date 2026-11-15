# Proposal — `basen-uppercase-prepass`

## Why

`BaseN/Base16.lean` carries a **24-theorem case-folding tier** (24 of the file's 67
theorems, ~27%) to accept both hex cases. It is built as a `Codec.Normal` quotient —
`foldByte`, `foldList`, `foldNormalizer`, `hexBlockIsoF`, `fill_foldList`, and the
`decodeHexFold_*` family — but the observable contract is one sentence:

> uppercase the input, then decode.

Two things are wrong with it, and the first is a **factual error**:

**1. The RFC does not require it.** `Base16.lean:14` and `:641` say _"RFC 4648 §8
requires a Base16 decoder to accept both cases"_. §8 actually says:

> "Base 16 encoding **does not require** case insensitivity; however, Base 16
> decoders **MAY** accept lowercase letters."

`MAY`, not `MUST`. Nothing in the repository sources the RFC, so this was never
checked against the text. Lowercase acceptance is an **optional convenience**, not a
conformance obligation — and `../fstar-basen` makes no such claim at all (it has one
lowercase test vector and no case tier: 216 lines for base16 vs 1191 here).

**2. The tier is a parallel implementation of machinery that already exists.**
`Codec/Normal.lean` already provides `Normal`, `Normalizer`, `fill`, and — the
governing theorem — `decodeNormal_encode`:

```
decodeNormal_encode : Normalizer S norm → Iso α (Normal S norm) → α → S → …
  -- if the encoder emits a normal form, the normalising decoder reproduces the value
```

for **any** `S`, `norm`, `α`. `Base16`'s tier does not use it, and does not even use
the `Normal` `Iso` it builds: `decodeHexFold s := Run.decodeFull hexRun
(foldByteBytes s)` goes through `hexRun`, and `hexBlockIsoF` has **no caller**
outside the tier's own lemmas. The 24 theorems re-derive what one instantiation
supplies.

The same operation recurs across the ecosystem and is about to recur again: uppercasing
hex, stripping leading zeros, dropping optional whitespace are all **one** thing — a
total idempotent pre-pass `S → S` that removes information-free variation, after which
the strict decoder is a genuine `Iso`. `Codec/Normal.lean`'s own header already says
so. This change makes `basen` an instance of that mechanism instead of a
re-implementation of it.

## What changes

**Uppercase the input, then decode with the existing strict decoder.** That is the
whole behaviour. The `Iso` is from _normalised text_ to the value; the pre-pass is the
entry ramp to it, never part of it.

```
decodeHex s  := decodeFull hexElem hexConsumesByte (upperBytes s)
decodeB32 s  := decodeFullB32 (upperBytes s)
```

Three `Normalizer` instances replace one bespoke tier, and each is ~3 lines
(idempotence of a pointwise `UInt8 → UInt8` map).

## Scope: base16 and base32, **not base64** — and this is measured

Whether uppercasing is sound depends **entirely** on whether the alphabet contains
lowercase symbols:

| base | symbols | lowercase in the alphabet?                   | uppercasing is                                      |
| ---- | ------- | -------------------------------------------- | --------------------------------------------------- |
| 16   | 16      | no — `a`–`f` are lax spellings of `A`–`F`    | **safe, and the point**                             |
| 32   | 32      | no — `b32ToVal` has no `97`–`122` branch     | **safe** (and today it rejects lowercase: measured) |
| 64   | 64      | **yes** — `b64ToVal` maps `97`–`122` → 26–51 | **UNSOUND — would corrupt data**                    |

Measured today:

```
Base32.decodeFullB32 "MY======"  → some …          (uppercase accepted)
Base32.decodeFullB32 "my======"  → none            (lowercase rejected)
Base64.decodeFullB64 "TWFu"      → some "Man"
Base64.decodeFullB64 "twfu"      → some (different value: t=45 ≠ T=19)
```

So base64 must keep its alphabet exactly as it is: its lowercase letters are **data**,
not casefoldable spelling. Base64 uses all 64 symbols and cannot afford
case-insensitivity, which is why no other base64 implementation offers it. **Base64 is
excluded from this change**, and the spec says why so that a later reader cannot
"helpfully" add it.

## Non-goals

- **Changing base 2/4/8/10.** Their alphabets are `0`/`1`, `0-3`, `0-7`, `0-9` —
  no letters, so no case to fold. They are untouched.
- **Base64.** See above; its alphabet has no spare room for case.
- **Changing any existing law.** `roundtrip`, `decodeFull_canonical`,
  `decode_encode_inverse`, `encode_injective`, `decodeFull_B16_char` and their
  base32/base64 twins stay exactly as they are — the pre-pass composes _outside_ them.
- **The numeric codec.** A separate change; `basen` is "base-N byte encodings".

## Risk, and the two things that must be mutation-tested

**The failure this change can introduce is silent corruption**, not a type error: a
pre-pass applied to a base where case is data turns one valid input into a different
valid value. The two defences, both required before anything is deleted:

1. **The base64 exclusion test.** A theorem or `#eval` showing that
   `upperBytes` on a base64 payload changes the decoded value — so the exclusion is a
   measured fact, not a comment.
2. **A mutation of each base's pre-pass.** Disable `upperBytes` for base16 and require
   the lowercase test vector to fail the build; same for base32.

If either mutation passes, the change has not been made.

## What this deletes

`Base16`'s 24-theorem tier reduces to roughly: one `upperByte`/`upperBytes` definition,
one idempotence proof, one "lowercase decodes" theorem, and the base32 twin. Expected
net: **~24 theorems out, ~8 in**, and `hexBlockIsoF`/`fill_foldList`/`hexBlockApply_foldList`
/`foldNormalizer` (a `Normal` demonstration with no caller) go away entirely.
