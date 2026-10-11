# Proposal

## Why

Rendel & Ostermann's *Invertible Syntax Descriptions* (§3.4, §4.1) defines the
parser as a nondeterministic list monad with `many` a *derived* combinator.
This library re-bases that on bytes and proves the two directions agree with the
denotational relation `Rel`.

The core is proven (unconditional laws, `[propext, Quot.sound]`, zero `sorry`).
The one non-total construct is `many` (currently `partial def`): its *meaning*
(`Rel`) is total and proven; its *execution* into a strict `List` is not, because
`many (pure ())` has infinitely many results.

A prior attempt "solved" this with a fuel counter plus a `Productive`
precondition — and it is **wrong**: it fabricates results for empty-matching
`many` (`decode (many (pure ())) []` returned `([()], [])`) and hides the
wrongness behind a classical gate. That is not constructive purity.

This change replaces it with the correct constructive realization: `decode`'s
repetition case is **well-founded recursion on the consumed byte string** — the
paper's own productive guard — with no fuel, no `Productive`, no new constructor.
The totality boundary (empty-matching `many` is genuinely infinite) is stated as
a *theorem*, not patched with a wrong result.

## What Changes

- `decode`'s repetition/many case: well-founded recursion on `s.length`
  (productive; each `cons` consumes ≥1 byte), total and correct for productive
  `many`.
- A **proved totality theorem**: `decode (many p) s` terminates exactly when `p`
  is productive (each `Rel p x s₁` has `s₁ ≠ []`).
- `Rel` **unchanged**; laws restated/re-proved, unconditional, zero `sorry`.
- `many`/`some`/`sepBy`/`chainl1`/`chainr1` stay derived; no `Codec.many`
  constructor, no `Productive` predicate.

## Capabilities

### Fixed Capabilities

- `codec`: the repetition decoder is made correct and productive (was: a wrong
  fuel-bounded approximation). The denotational `Rel` and its laws are preserved.

## Impact

- `Codec/Decode.lean` (repetition case), `Codec/Sound.lean` (totality theorem +
  restated laws), `Codec/Combinators.lean` (docstrings). `Codec/Codec.lean`,
  `Codec/Encode.lean`, `Codec/Iso.lean` unchanged.
- No mathlib, no `Std`, no `ByteArray`, no `Classical.choice`; `#print axioms`
  still `[propext, Quot.sound]`.
