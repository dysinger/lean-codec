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

## Decision (2026-10-18) — a whole-list base is a `Codec (List UInt8)` _value_, so

`many` must become an AST constructor (most correct reading)

The design's D2/D3 assumed "`base16 : Codec (List UInt8)`" could be composed from
`satisfy`/`count`/`many`/`iso`/`alt` **without** a new core constructor. That is
**false**: the only `Codec (List α)` producers are `count n p` (exactly `n`) and
`manyUpTo n p` (at most `n`) — both _bounded_ — and unbounded `many` lives only in
the `decodeRepeat`/`encodeRepeat`/`relRepeat` triple (via a `ConsumesByte` witness),
**not** the AST. Because `decode : Codec α → Bytes n → List (α × Suffix n)` is a
_total function_ (not the paper's relation), a plain `many` node is non-total for an
empty-matching step. So tasks 3.x/4.x as written are **unrealizable without
restoring `many` to the AST**. The most correct reading of the spec ("each base is
a `Codec (List UInt8)` value, roundtrip inherited from `Codec.roundtrip`") requires:

### New core constructor `many` (adds scope beyond "one `satisfy`")

```lean
| many {α : Type} : (p : Codec α) → Productive p → Codec (List α)
```

`Productive p := ∀ x n s, Rel p x s → n ≠ 0` is already defined in `Codec.lean`
(no import cycle). The `many` cases reuse the existing repetition machinery:

- `Rel (many p h) xs n s := relRepeat (Rel p) xs n s` (clean, `relRepeat` in `Codec.lean`).
- `encode (many p h) xs := encodeRepeat p xs` (clean, `encodeRepeat` needs no witness).
- `decode (many p h) s := <productive repetition decoder>`.

### The one real obstacle: `Productive` (in `Codec.lean`) vs `ConsumesByte`

(in `Decode.lean`) — the `decode` case

`decodeRepeat p h'` demands `h' : ConsumesByte p := ∀ x n s t, (x,t) ∈ decode p s →
t.remaining < n`. The bridge `Productive p ↔ ConsumesByte p`
(`productive_iff_consumesByte`) needs `decode_spec` + `bidir` (**`Sound.lean`**),
which postdate `decode` — a genuine import cycle if `decode`'s `many` case calls
`decodeRepeat`. Resolution (pick **A1**):

- **A1 (preferred)** — define a `Productive`-indexed repetition decoder
  `decodeMany (p) (h : Productive p) n s` in `Decode.lean` whose well-founded step is
  guarded by a _local_ "productive steps shorten" lemma proved with
  `decode_genuine_suffix` (already in `Decode.lean`, proved _before_ `Sound`, `[propext,
Quot.sound]`-only), not by `decode_spec`. Then `decode (many p h) s := decodeMany p h n s`,
  and the `many` case of `decode_spec` closes by the _already-proved_ `decodeRepeat_spec`
  (via `productive_iff_consumesByte`, now available in `Sound.lean`).
- A2 (rejected) — move `ConsumesByte`/`decodeRepeat` into `Codec.lean`: impossible,
  `ConsumesByte` mentions `decode`.

### Every `induction d` law must become `Codec.rec` (type-changing constructor)

`many : Codec α → Codec (List α)` changes the value type, so the following (all
currently `induction d`) must be converted to `Codec.rec` with a type-indexed
motive `(α : Type) → Codec α → …`, then gain a `many` case:

- `encode_rel`, `decode_spec` (+ derived `bidir`, `decode_encode`, `roundtrip`),
  `decodeFast_eq`, `decode_genuine_suffix_pointwise` (and anything else matching
  `induction d`). The `many` cases are **free**: they `rw` through
  `decodeRepeat_spec`/`encodeRepeat_rel`/`relRepeat_cons`/`relRepeat_nil`.

### Order of implementation (next session)

1. Add `many` + `Rel`/`encode`/`encode` cases; define `decodeMany`; thread
   `decode`/`decodeFast` cases.
2. Convert the `induction d` laws to `Codec.rec`; add `many` cases closed by the
   repetition lemmas. `#print axioms Codec.roundtrip` ⇒ `[propext, Quot.sound]`.
3. Rewrite the seven bases as `Codec (List UInt8)` values (`count`/`many`/`iso`/`alt`
   over `satisfy`), deleting the bespoke `encode`/`decode`; roundtrip = `Codec.roundtrip`.
4. Facade + bench + `nix flake check`.

This is a **proof-critical core re-derivation** (not a downstream composition), so it
should carry its own fresh review, exactly like the `single-carrier-bytes` re-derivation
it extends.
