# Tasks

## 1. Feasibility spike

- [ ] 1.1 Confirm the paper (`docs/rendel10invertible.md`) is the spec; adopt `Iso` (§3.1/§5.1), the `Codec` interface (§3.4), `Rel` (§4.3), derived combinators (§6.1), `foldl`/`iterate` (§5.2/5.3); re-base to bytes (`byte : Codec UInt8`, `Rel` over `ByteArray`).
- [ ] 1.2 Confirm binary + speed + high-level-Lean feasibility: `ByteArray`/`UInt8/16/32/64`/`Array`/`List`/`Nat.div/mod` are stdlib; no mathlib (`Equiv`/`PEquiv` are mathlib, NOT reused).
- [ ] 1.3 Record that the `Iso` inverse law holds unconditionally (no `ignore`, so no "modulo equivalence classes" — resolved by design).
- [ ] 1.4 Record that `Codec` is a typeclass (matches the paper §3.4; two interpreters are instances).
- [ ] 1.5 Record the `ByteArray` proof strategy preference: direct `simp`; fallback to a `List UInt8` model + transport lemma (proof ergonomics only).
- [ ] 1.6 Benchmark a multi-MB `ByteArray` roundtrip; acceptance = linear time, no per-byte boxing (confirms the return-the-rest design).

## 2. Iso (partial isomorphisms, the category)

- [ ] 2.1 `Iso α β` with `apply`/`unapply` + the inverse `law` field.
- [ ] 2.2 `Category Iso` (`∘`, `id`) with the composition law proved.
- [ ] 2.3 Product bifunctor `×`, `associate`, `commute`, `unit`.
- [ ] 2.4 `element`, `subset`, `inverse` (carry `[DecidableEq α]`/`[Decidable p]`).
- [ ] 2.5 `foldl`/`iterate` (paper §5.2/5.3), `foldl : Iso (α×β) α → Iso (α, List β) α`.

## 3. Codec (description interface, over bytes)

- [ ] 3.1 The interface: `$`, `*`, `|`/`empty`, `pure`, `byte : Codec UInt8`.
- [ ] 3.2 Declare `Rel : Codec α → α → ByteArray → Prop` (so `Unambiguous` has no forward reference; theorems live in §5).

## 4. Two interpretations (decode / encode)

- [ ] 4.1 Deterministic decoder `decode : Codec α → ByteArray → Except DecodeError (α × ByteArray)` (returns value + remaining bytes; no cursor; no backtracking; no peeking).
- [ ] 4.2 Builder encoder `encode : Codec α → α → Option ByteArray` (partial; rejects out-of-domain).
- [ ] 4.3 `Unambiguous` discipline (per-demo proof obligation, not library-decidable): `∀ s, at most one x with Rel d x s`; deterministic decoder is sound-and-complete on that domain; `|` is committed choice.

## 5. Rel (denotational semantics) + roundtrip theorems

- [ ] 5.1 `Rel` over whole byte sequences (remaining-bytes is private to `decode`).
- [ ] 5.2 Bidirectional law: `Unambiguous d → (Rel d x s ↔ decode d s = .ok (x, empty))`.
- [ ] 5.3 Roundtrip: `(encode d x) = some s → decode d s = .ok (x, empty)`.
- [ ] 5.4 Prove the laws by `simp`/`rfl`/induction — no solver.

## 6. Derived combinators (generic, byte-agnostic)

- [ ] 6.1 `many`, `*>`, `<*`, `between`, `chainl1` (uses §2.5 `foldl`/`iterate`).

## 7. Benchmark, extraction, docs

- [ ] 7.1 Extract the interpreter hot path to C/LLVM; confirm `Prop` proofs erase.
- [ ] 7.2 Benchmark `decode`/`encode` on a synthetic `byte`/`many` description — linear time, no per-byte boxing; record the number.
- [ ] 7.3 Confirm `get!`/remaining-bytes (not `getElem`-with-proof) actually runs post-extraction.
- [ ] 7.4 `README.md`: guarantee, `Iso`/`Codec`/`Rel` model, pure-framework scope, combinator table, usage.
- [ ] 7.5 Zero-`sorry` + `#print axioms` = stdlib only (`propext`, `Classical.choice`, `Quot.sound`).
- [ ] 7.6 Document the deliberate departures (byte core, return-the-rest decode, deterministic single result, committed `|`, lossless capture) and why; note `lean-binary`/`lean-text` as downstream consumers.
