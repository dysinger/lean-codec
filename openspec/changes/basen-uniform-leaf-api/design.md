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

## Decision (2026-10-18, superseded 2026-10-19) — `many` does **not** become a

constructor; the variable-width run primitive is `takeWhile` (`satisfy_many0`)

The earlier "Decision (2026-10-18)" concluded that `base16 : Codec (List UInt8)`
requires restoring `many` to the AST. That reading was **wrong**, on the authority
of both the paper and the F* reference:

- **The paper (`PAPER.md` §3.4)** never makes `many` a syntax-description
  constructor. The elementary descriptions are exactly `token` and `pure`; `many`
  is a _derived recursive combinator_ over the existing combinators —
  `many p = nil $ pure () | cons $ p ∗ many p` — parallel in structure to
  `parseMany`/`printMany`. Its denotation is the least fixpoint, which is exactly
  what `relRepeat` already captures in `Codec.lean`.
- _*The F* reference (`fstar-codec`)_* has no `many` combinator at all. The
  variable-width run is a _specialized leaf_ over a byte predicate,
  `satisfy_many0 f` / `satisfy_many1 f` (aliased `many0`/`many1`): a `let rec`
  `satisfy_run_scan f bs` that scans a maximal leading run of the _finite_ input
  byte list, consuming one byte per step. No `Productive`/`ConsumesByte` witness
  is needed, because the recursion is over the finite input buffer, not over an
  arbitrary `p`'s denotation. `fstar-basen` encodes base16/32/64 with `count`
  (fixed blocks) + `satisfy_many` (alphabet runs) + hand-rolled block/pad decoders.

Restoring `many` to the Lean AST is not merely unnecessary — it is
**type-theoretically impossible** in Lean: the `many` constructor would need a
`Productive p` field, and `Productive p := ∀ x n s, Rel p x s → n ≠ 0` forms the
definition-order cycle `Codec.many → Productive → Rel → Codec`. Lean rejects
mixed `inductive`/`def` `mutual` blocks, and `Rel : … → Prop` is universe-`Prop`
while `Codec α` is `Sort 1`, so `mutual inductive Codec + Rel` is rejected too.

### Correct resolution: `takeWhile` is the run primitive; `many` stays out of the AST

The Lean core **already has the correct primitive**. `takeWhile p` in
`Combinators.lean` is the `satisfy_many0` analogue, already productive by
construction and `[propext, Quot.sound]`-clean:

```lean
relTakeWhile p   = relRepeat (Rel (satisfy p))
decodeTakeWhile p = decodeRepeat (satisfy p) (satisfyConsumesByte p)
encodeTakeWhile p = encodeRepeat (satisfy p)
```

It is a `rel`/`decode`/`encode` **triple** (like `sepBy`/`chainl1`), not a
`Codec` node. So the bases are composed exactly as the paper and F* do:

- **fixed-width blocks** → `count n (satisfy p)` (a genuine `Codec (List UInt8)` value),
- **variable-width alphabet runs** → `takeWhile p` (the productive run triple),
- **block→byte grouping / digit math** → `iso` (with the `Nat`-level lifts), and
- **padding / disjoint alternatives** → `alt`, with terminal-`=` (5.1) preserved by
  the pad branch requiring an empty run afterward.

Each base therefore is either a genuine `Codec (List UInt8)` value where it is
bounded (`count`), or a run triple where it is unbounded (`takeWhile`), in both
cases inheriting the **already-proved** `decodeRepeat_spec`/`encodeRepeat_rel`/
`relRepeat_*` laws rather than a fresh `Codec.roundtrip` induction.

### Non-change to core

No new constructor is added. `satisfy` (already committed, `77c1c54`) is the only
core addition; `takeWhile` (also committed) is the only derived run. The laws stay
`induction d` (no `Codec.rec` conversion, since no type-changing constructor exists).
`#print axioms Codec.roundtrip` remains `[propext, Quot.sound]`.
