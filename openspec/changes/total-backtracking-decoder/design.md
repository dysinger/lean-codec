# Design

## Context

`PAPER.md` §4.1: the parser is `String → [(α, String)]`; §3.4: `many p = nil $
pure () | cons $ p * many p` is a *derived* combinator; §4.4: unlimited
backtracking costs exponential time/space and is the paper's own open problem.
The library is stdlib-only (`Init`), no `Std`, no mathlib.

Today `decode : Codec α → List UInt8 → List (α × List UInt8)` is total and
proven for every description except unbounded `many` (a `partial def`). Its
*meaning* (`Rel`) is total and proven. This change removes the false "fuel +
Productive" prior attempt and replaces it with the correct constructive
realization.

## The fact this change is grounded in (constructive, not invented)

`decode (many p) s` is productive iff `p` *consumes at least one byte* per
application. When it does, every recursive `cons` step runs on a strictly
shorter remaining string, so a **well-founded recursion on `s.length`** is the
*constructive guard* — exactly the paper's `many`, with no fuel counter, no
`Productive` predicate, no `Codec.many` constructor.

When `p` can match the empty string (`p = pure ()`), `many p` has **infinitely
many** results for the same input (`[], [], …`), so no finite total `List` can
enumerate them. That is a fact about the paper's semantics, not a defect to
paper over: `decode` is *partial exactly there*, and we state it as a theorem,
not a precondition.

## Decision — decode is well-founded on the consumed string (no fuel, no gate)

- **D1** `decode : Codec α → List UInt8 → List (α × List UInt8)` stays a list
  (strict), but its **repetition** case is a well-founded recursion on
  `s.length`, productive because each `cons` consumes ≥1 byte. This makes
  `decode (many byte) [1,2,3]` total and correct, enumerating exactly
  `[], [1], [1,2], [1,2,3]`.
- **D2** For the genuinely-infinite case (`many (pure ())`), `decode` is
  `partial` — and **only** there. We do **not** return a wrong finite list and
  do **not** bolt on a `Productive` hypothesis. The totality boundary is a
  *theorem*: "`decode (many p) s` terminates iff `p` is productive," proved, not
  assumed.
- **D3** `Rel` is **unchanged**: it is the least `nil`/`cons` fixpoint, total and
  constructive for every `p` (including empty-matching); the laws are restated
  and re-proved unconditionally over `Rel`, exactly as today.
- **D4** `many`/`some`/`sepBy`/`chainl1`/`chainr1` stay **derived** combinators;
  no `Codec.many` constructor.

## The one genuine, reviewable fork

If the reviewer requires `decode (many (pure ())) []` to be a *total* value,
that is impossible for a strict `List` carrier (infinite results). The only
total resolution is to change the carrier to a lazy/coinductive stream, which in
stdlib-only Lean 4 requires hand-encoding (predicate-only `coinductive`), and
whose `alt`-append over an infinite branch is itself not a computable `Nat`
index. This change therefore **keeps the strict-`List` carrier and makes the
totality boundary explicit**; upgrading to a lazy carrier is a separate,
opt-in change (future work, alongside §4.4 efficiency).

## Goals / Non-Goals

**Goals**

- `decode` well-founded on `s.length` for repetition; total for productive
  `many`; the productive-totality theorem proved.
- `many` and friends are total `def`s in their *denotational* reading; the
  `partial` keyword is confined (if present) to the executor for the
  provably-infinite empty-matching case.
- Laws unconditional, `[propext, Quot.sound]`, zero `sorry`, zero warnings.

**Non-Goals**

- No fuel counter, no `Productive`/`AllProductive`, no `Codec.many` constructor,
  no `Std`, no lazy-carrier migration (that is the explicit future work).
- No efficiency work (§4.4).

## Risks / Trade-offs

- **[Termination theorem is the hard lemma]** → "productive ⇒ `decode (many p)`
  terminates" requires a measure on the remaining string and a proof that each
  `Rel p x s₁` step shrinks it. Mitigation: proven by induction on `s.length`
  with the `p`-consumes-a-byte hypothesis stated explicitly as an *argument*,
  not a global predicate.
- **[Empty-matching `many` is partial]** → accepted and stated; no wrong results
  are produced. Mitigation: a gate `grep 'partial def' Codec/` is *expected* to
  be non-empty for exactly this one def, and is documented as such.
- **[`alt` over an infinite branch]** → unchanged from today (structural list
  append is fine because branches are finite except the `many` case, which is
  handled by the well-founded recursion, not by generic append).
