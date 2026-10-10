# Design

## Context

See `proposal.md` for the motivation. This library re-bases Rendel & Ostermann's
*syntax descriptions* onto a byte core and makes their invertibility a machine
proof. The authoritative reference is `docs/rendel10invertible.md`.

## Goals / Non-Goals

**Goals:**

- A three-layer core: `Iso` (with the inverse law as a field), `Codec` (the
  description typeclass), `Rel` (the denotational relation over `ByteArray`).
- Byte-exact `decode (encode x) = x`, with the strict `Iso` law holding
  *unconditionally* (no "modulo equivalence classes" escape hatch).
- Deterministic, positional decoding (`Except DecodeError (α × ByteArray)`) and
  partial encoding (`α → Option ByteArray`).

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
- **Determinism with an `Unambiguous` gate.** A single result (not the paper's
  list), sound-and-complete only on the `Unambiguous` domain; `|` is committed
  choice. Backtracking and peeking are out of scope.
- **`Codec` is a typeclass**, matching the paper's §3.4 "class of syntax
  descriptions" and its `IsoFunctor`/`ProductFunctor`/`Alternative` superclasses;
  the two interpreters are instances. (Alternative rejected: a `structure`.)
- **`encode` partial, `decode` error-returning.** `encode` returns `Option`
  (out-of-domain is silent and expected, e.g. trying the next `|` branch);
  `decode` returns `Except DecodeError` (malformed input is informative, with a
  position).

## Risks / Trade-offs

- [Determinism narrows the paper's relation to a function] → Mitigation: the
  `Unambiguous` precondition is stated explicitly and proved per demo, not
  hidden.
- \[Committed `|` changes observable semantics\] → Mitigation: documented as a
  deliberate departure (§4.4's predictive-`|` observation), not a forced
  consequence.
- \[`ByteArray` ops may resist `simp`\] → Mitigation: prefer direct `simp`; fall
  back to a `List UInt8` model + transport lemma (proof-ergonomics only).
