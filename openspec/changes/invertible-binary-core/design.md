# Design

## Context

See `proposal.md` for the motivation. This library re-bases Rendel & Ostermann's
*syntax descriptions* onto a byte core and makes their invertibility a machine
proof. The authoritative reference is `PAPER.md`.

## Goals / Non-Goals

**Goals:**

- A three-layer core: `Iso` (with the inverse law as a field), `Codec` (the
  description interface, an inductive AST), `Rel` (the denotational relation over
  `List UInt8`).
- Byte-exact `decode (encode x) = x`, with the strict `Iso` law holding
  *unconditionally* (no "modulo equivalence classes" escape hatch) — over the
  `alt`-free (`NoAlt`) fragment; over `alt` it is deferred (see below).
- Deterministic, positional decoding (`Except DecodeError (α × List UInt8)`) and
  partial encoding (`α → Option (List UInt8)`).

**Non-Goals:**

- No leaf codecs in core (no `u8`/endianness/`varint`/`bytes n`/`utf8`/`text`).
- No cursor, no backtracking, no peeking.
- No mathlib; stdlib only.

## Decisions

- **`Iso.law` is a field.** The paper §7.5 asks how to encode the invariant
  dependently; we answer: it is a field, so an `Iso` cannot exist without its
  proof. (Alternative rejected: keeping it as unchecked prose.)
- **Lossless capture replaces `ignore`.** The paper's `ignore`/`skipSpace` discard
  bytes and force the "modulo equivalence classes" weakening. We drop `ignore`
  entirely and express skippable bytes as `many (subset p byte)`, which captures
  and re-emits them. This is what makes the roundtrip byte-exact and the
  `Iso.law` unconditional. (Alternative rejected: a "coarse law" relaxation.)
- **Return-the-rest decoding (no cursor).** `decode` returns `(α × remaining)` to
  match the paper's `String → [(α, String)]` style, with the failure position
  derived structurally (`whole.size − remaining.size`). (Alternative rejected: an
  explicit `Nat` cursor, which is neither the paper's nor fstar-codec's design and
  adds no capability.)
- **Determinism with a `NoAlt` gate.** A single result (not the paper's list),
  sound-and-complete **unconditionally on the `alt`-free (`NoAlt`) fragment**;
  `|` is committed choice. Soundness of committed `|` itself is **deferred**: it
  requires a prefix-disjointness condition on the branches (see Risks), which
  shares its core with the deferred coinductive `iterate`/`foldl` combinators.
  Backtracking and peeking are out of scope.
- **`Codec` is an inductive description AST**, a deliberate departure from the
  paper's §3.4 typeclass. The typeclass reading (one `Codec` per use site, two
  *instances* for parsing/printing) would make the description implicit, so
  `Rel : Codec α → α → …`, `decode : Codec α → ByteArray → …`, and
  `encode : Codec α → α → …` could not be ordinary functions *of* a description
  value, and structural induction over a single description would not typecheck.
  The free-alternative / free-applicative encoding makes `Codec` an explicit
  value the interpreters consume. (Alternative rejected: the paper's typeclass,
  and a `structure`; both hide the description from structural recursion.)
- **`encode` partial, `decode` error-returning.** `encode` returns `Option`
  (out-of-domain is silent and expected, e.g. trying the next `|` branch);
  `decode` returns `Except DecodeError` (malformed input is informative, with a
  position).

## Risks / Trade-offs

- [Determinism narrows the paper's relation to a function] → Mitigation: the
  `NoAlt` gate is stated explicitly and the roundtrip is proved unconditionally
  on that fragment; the `alt` case is named as deferred, not hidden.
- \[Committed `|` changes observable semantics\] → Mitigation: out of scope for the
  current roundtrip guarantee; the prefix-disjointness condition that would
  restore soundness is recorded as future work (same coinductive core as
  `iterate`/`foldl`), not silently asserted.
- \[`ByteArray` ops may resist `simp`\] → Mitigation: model the provable core as
  `List UInt8`; reserve `ByteArray` for the executable wrapper transported on
  afterwards (proof ergonomics only).
