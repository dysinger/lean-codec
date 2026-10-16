# Design

## Context

See `proposal.md` for the motivation. This library re-bases Rendel & Ostermann's
_syntax descriptions_ onto a byte core and makes their invertibility a machine
proof. The authoritative reference is `PAPER.md`.

## Goals / Non-Goals

**Goals:**

- A three-layer core: `Iso` (with the inverse law as a field), `Codec` (the
  description interface, an inductive AST), `Rel` (the denotational relation over
  `List UInt8`).
- Byte-exact roundtrip, encode→decode direction **unconditional**
  (`encode d x = some s → (x, []) ∈ decode d s`), with the strict `Iso` law holding
  _unconditionally_ (no "modulo equivalence classes" escape hatch) — for **every**
  description, including `alt` and repetition. The decode→encode converse is
  byte-exact only for `Functional` descriptions (see `README.md` `[D4]`/
  `Codec.Sound.encode_of_decode`).
- The paper's nondeterministic (backtracking) list decoder:
  `decode : Codec α → List UInt8 → List (α × List UInt8)`, with `|` as union;
  and partial encoding (`α → Option (List UInt8)`).

**Non-Goals:**

- No leaf codecs in core (no `u8`/endianness/`varint`/`bytes n`/`utf8`/`text`).
- No cursor, no committed-choice narrowing, no peeking/backtracking _cut_.
- No mathlib; stdlib only.
- Efficiency is deferred (the paper's §4.4 open problem): the proof-of-concept
  backtracking decoder is exponential in the worst case; an efficient DP
  re-implementation of the _same_ semantics is future work, not a change to the
  semantics.

## Decisions

- **`Iso.law` is a field.** The paper §7.5 asks how to encode the invariant
  dependently; we answer: it is a field, so an `Iso` cannot exist without its
  proof. (Alternative rejected: keeping it as unchecked prose.)
- **Lossless capture replaces `ignore`.** The paper's `ignore`/`skipSpace` discard
  bytes and force the "modulo equivalence classes" weakening. We drop `ignore`
  entirely and express skippable bytes as repetition over a `subset p byte` step
  (`relRepeat`/`decodeRepeat`/`encodeRepeat`), which captures and re-emits them.
  This is what makes the roundtrip byte-exact and the `Iso.law` unconditional.
  (Alternative rejected: a "coarse law" relaxation.)
- **The decoder is the paper's nondeterministic list decoder (backtracking union).**
  `decode (d₁ | d₂) s = decode d₁ s ++ decode d₂ s`, matching `Rel (d₁ | d₂) = Rel d₁ ∨ Rel d₂` by construction. This makes the bidirectional law
  (`decode_spec`) and roundtrip hold **unconditionally** — no `NoAlt` gate, no
  prefix-disjointness. (A past committed-choice deviation and its
  `NonNull`/`PrefixDisjoint`/`Disjoint` machinery were deleted; see `[D5]` in
  `README.md`.)
- **`Codec` is an inductive description AST**, a deliberate departure from the
  paper's §3.4 typeclass. The typeclass reading (one `Codec` per use site, two
  _instances_ for parsing/printing) would make the description implicit, so
  `Rel : Codec α → α → …`, `decode : Codec α → List UInt8 → …`, and
  `encode : Codec α → α → …` could not be ordinary functions _of_ a description
  value, and structural induction over a single description would not typecheck.
  The free-alternative / free-applicative encoding makes `Codec` an explicit value
  the interpreters consume. (Alternative rejected: the paper's typeclass, and a
  `structure`; both hide the description from structural recursion.)
- **`encode` is partial, `decode` is relation-valued.** `encode` returns `Option`
  (out-of-domain is silent and expected, e.g. trying the next `|` branch);
  `decode` returns the **full list** of `(value, remaining)` results (backtracking,
  as in the paper §4.1) rather than a single result or an error.
- **Unbounded repetition is semantic, not a finite `Codec`.** `many` (§3.4) is an
  _infinite_ description, which a strict language cannot represent as an AST node;
  a former `partial def many` was irreducibly opaque at the `Rel` level (a
  `partial def` yields no equational lemma). Its semantics is split into
  `relRepeat (Rel p)` (denotation), `decodeRepeat p h` (decoder, well-founded on
  `s.length`, `h : ConsumesByte p`), and `encodeRepeat p` (encoder, structural on
  the value). The `many`-shaped list combinators (`sepBy`, `chainl1`/`chainr1`) are
  re-derived over these three, each with `_spec`/`_rel` laws.
- **`iterate` (paper §5.3) is omitted.** Its forward/backward fixpoints need not
  coincide (`apply a = some b ↔ unapply b = some a` does not force
  `apply a = none ↔ unapply a = none`), so there is no field law without a
  per-element precondition. `foldl`/`foldr` (proved directly) are what `chainl1`/
  `chainr1` need.

## Risks / Trade-offs

- [Backtracking is exponential in the worst case] → Mitigation: the semantics is
  exactly the paper's (§4.1/§4.4); efficiency is the paper's own named open
  problem, deferred to a separate DP re-implementation of the _same_ denotation
  (not a change to the semantics).
- \[`ByteArray` ops may resist `simp`\] → Mitigation: model the provable core as
  `Bytes` (a reducible `abbrev` for `List UInt8`); reserve `Buffer` (a packed
  `ByteArray`-backed newtype in `Codec.Buffer`) for the executable transport
  transported on afterwards (proof ergonomics only).
