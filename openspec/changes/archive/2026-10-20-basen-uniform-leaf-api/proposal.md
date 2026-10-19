# Proposal

## Why

The goal is **`Codec` pervades the stack**: JSON, base64, varint, UTF-8, and any
AST are all decoded/encoded by the _same two operations_,
`Codec.decode`/`Codec.encode`, over a `Codec α` value — "only the codec changes."
Today that is false: `basen`'s bases are bespoke `List UInt8 → List UInt8` /
`Option (List UInt8)` functions that never touch `Codec`, so decoding base64 is a
_different call shape_ from decoding JSON.

The core `Codec` is one primitive short: it cannot express "a byte satisfying a
predicate" (`satisfy`), so a base16 digit, a base32/64 alphabet byte, a varint
continuation byte, or a UTF-8 code-unit cannot be a `Codec`. Adding that single
primitive makes every byte-class expressible, and the existing combinators
(`seq`, `alt`, `count`, `manyUpTo`, `iso`) plus the repetition layer
(`decodeRepeat`/`encodeRepeat`) do the rest.

## What Changes

1. **Core: add one constructor `satisfy : (UInt8 → Bool) → Codec UInt8`** — the
   byte-token-with-guard. `Rel (satisfy p) b s = (p b = true ∧ s = single b)`;
   `decode` consumes one byte iff `p b`, else `[]`; `encode` emits one byte iff
   `p b`, else `none`. Nothing else is added to core, now or later.

2. **A derived run combinator over `satisfy`** (not a constructor) — `takeWhile p`
   / `many (satisfy p)`, realized via the existing `decodeRepeat`/`encodeRepeat`.
   This expresses variable-length tokens: alphabet runs, varint (`takeWhile
highBitSet` + a fold `iso`), UTF-8 (a run of code-unit bytes + a decoder
   `iso`). It is how "you can't tell a symbol from one byte" is resolved — by a
   run, not a single-byte lookahead.

3. **`basen` bases become `Codec` values.** `base16/base32/base64/… :
Codec (List UInt8)` composed from `satisfy`/`count`/`many`/`iso`/`alt`; the
   seven bespoke `encode`/`decode` and their duplicated `Nat↔UInt8` lifts are
   deleted, and each base's roundtrip is the _inherited_ `Codec.roundtrip`.

## Capabilities

### New Capabilities

- `codec`: the `satisfy` byte-predicate primitive plus a derived run combinator,
  making byte-alphabet formats and variable-length tokens expressible as `Codec`.
- `basen`: each base is a `Codec (List UInt8)` value with the uniform
  `Codec.decode`/`Codec.encode`, not a bespoke function.

## Impact

- **Core**: one constructor + its `Rel`/`decode`/`encode`/`decodeFast`/law cases,
  `[propext, Quot.sound]`-only, zero `sorry`.
- **`basen`**: seven bases rewritten as `Codec` values; bespoke decoders removed;
  the 5.1 terminal-padding fix preserved.
- **Consumers**: `Bench.lean` calls `Codec.decode base16Codec …` etc.
- **No result-type change**: `decode : … → List (α × Suffix n)` and `encode : … →
Option (Σ n, Bytes n)` stay the paper's shapes (`[D2]`/`[D3]`).

## Non-Goals (explicit, permanent)

- No BE/LE, fixed-width, `varint`, `text`, tagged-`sum`, or lookahead constructors
  in core — those are downstream-package compositions (`count k byte` + an
  endianness `iso`), never core primitives.
- No change to `decode`/`encode` result shapes; no error-position type yet.
- Note: a base16 **single hex digit** is a valid value (`decode (satisfy isHex)`),
  not just pairs — "hex can be one digit" is respected by not forcing even
  length in the primitive.
