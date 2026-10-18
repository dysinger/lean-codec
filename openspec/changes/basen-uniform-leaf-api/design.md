# Design

## Context

See `proposal.md` — Why. `Codec` must pervade the stack: every format is a
`Codec α` value decoded/encoded by the single `Codec.decode`/`Codec.encode`.
The one missing leaf is `satisfy` (a guarded byte); everything else is existing
combinators + the repetition layer.

## Goals / Non-Goals

**Goals:**

- One core addition: `satisfy : (UInt8 → Bool) → Codec UInt8`.
- A derived run combinator (`takeWhile p`) over `satisfy`, via `decodeRepeat`/
  `encodeRepeat`.
- `basen` bases as `Codec (List UInt8)` values inheriting the uniform operations.

**Non-Goals:**

- No BE/LE/fixed-width/varint/text/tagged-sum/lookahead in core (downstream only).
- No result-shape change (`List`/`Option` stay). No error-position type yet.

## Decisions

### D1 — `satisfy` is `UInt8`-bound and the only new constructor

```lean
| satisfy : (UInt8 → Bool) → Codec UInt8
```

- `Rel (satisfy p) b s = (p b = true ∧ s = single b)`.
- `decode (satisfy p) s`: first byte `b` with `p b` → `[(b, Suffix.drop 1 s)]`,
  else `[]`.
- `encode (satisfy p) b`: `some ⟨1, single b⟩` if `p b`, else `none`.

It is `UInt8`-bound because the substrate is `Bytes n := Fin n → UInt8`; it is the
byte-token-with-guard. A single digit (e.g. one hex nibble) is a valid `satisfy`
decode — no even-length forcing at the primitive level.

### D2 — Runs are derived, not constructors

Variable-length tokens are `takeWhile p` / `many (satisfy p)`, realized by the
existing `decodeRepeat`/`encodeRepeat` over `satisfy`. This is what makes varint
(`takeWhile highBitSet` + a fold `iso`), UTF-8 (a code-unit byte run + a decoder
`iso`), and alphabet strings expressible. No new constructor for "run"; the
repetition layer already exists for exactly this.

### D3 — `basen` bases are `Codec` values

`base16 : Codec (List UInt8)`, `base32 : Codec (List UInt8)`, `base64 :
Codec (List UInt8)`, and base2/4/8/10 likewise, composed from `satisfy`/`count`/
`many`/`iso`/`alt`. The `Nat`-level digit math stays (as `iso`s), but the bespoke
`UInt8` `encode`/`decode` and the duplicated lifts are deleted; roundtrip is the
inherited `Codec.roundtrip`.

### D4 — Terminal padding (5.1) is preserved

base32/64's `=`-must-be-terminal rule lives in the block `iso`/`alt` structure
(the pad branch requires the run to be empty afterward). The existing 5.1
`rest = []` guards are kept in the block decoders.

### D5 — Result shapes unchanged

`decode : Codec α → Bytes n → List (α × Suffix n)` and `encode : Codec α → α →
Option (Σ n, Bytes n)` keep their paper shapes (`[D2]`/`[D3]`). "Only the codec
changes" is about _codec values_ and the two uniform operations, not a result
rewrite. No error-position type is added now.

## Risks / Trade-offs

- **[`satisfy` in the AST adds proof surface to every law]** — `Rel`/`decode`/
  `decodeFast`/`encode`/`decode_spec`/`bidir`/`roundtrip` each gain a `satisfy`
  case; this is the real, bounded work, done `[propext, Quot.sound]`-only.
- **[Run combinator is a derived, well-founded definition]** — it reuses
  `decodeRepeat`/`encodeRepeat` (already proven); no new recursion theory.
- **[base16 "one digit" vs "pairs"]** — `satisfy` decodes one nibble; the _pair_
  grouping is a `count 2`/`iso` above it. This keeps the primitive total and
  honors single-digit hex.

## Migration Plan

1. Core: add `satisfy`; extend `Rel`, `decode`, `decodeFast`, `encode`, and
   `Sound` laws; gate `lake build` + `#print axioms`.
2. Add `takeWhile`/`many (satisfy p)` as a derived combinator via
   `decodeRepeat`/`encodeRepeat`.
3. Remake the seven `basen` bases as `Codec (List UInt8)` values; delete bespoke
   `encode`/`decode`; preserve 5.1.
4. Update `Bench.lean` to `Codec.decode baseXCodec …`; gate zero `sorry`/
   warnings, `[propext, Quot.sound]`, `nix flake check` green; commit + push.

## Open Questions

None — resolved: one `satisfy` primitive, runs derived, result shapes unchanged,
no BE/LE/varint/fixed-width in core.
