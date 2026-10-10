# Tasks

## 1. Feasibility spike

- [x] 1.1 Confirm the paper (`PAPER.md`) is the spec; adopt `Iso` (§3.1/§5.1), the `Codec` interface (§3.4), `Rel` (§4.3), derived combinators (§6.1), `foldl`/`iterate` (§5.2/5.3); re-base to bytes (`byte : Codec UInt8`, `Rel` over `List UInt8`).
- [x] 1.2 Confirm binary + speed + high-level-Lean feasibility: `List UInt8`/`UInt8/16/32/64`/`Array`/`List`/`Nat.div/mod` are stdlib; no mathlib (`Equiv`/`PEquiv` are mathlib, NOT reused).
- [x] 1.3 Record that the `Iso` inverse law holds unconditionally (no `ignore`, so no "modulo equivalence classes" — resolved by design).
- [x] 1.4 Record that `Codec` is an inductive description AST (free-alternative / free-applicative), *not* the paper's §3.4 typeclass — a deliberate departure so that `Rel`/`decode`/`encode` are ordinary functions over one description value (the typeclass reading would make the description implicit and block structural induction).
- [x] 1.5 Record the `List UInt8` proof-model strategy: the provable core is `List UInt8`; `ByteArray` ops don't reduce under `simp`, so it becomes a transport target later (proof ergonomics only).
- [ ] 1.6 Benchmark a multi-MB roundtrip (on `List UInt8` now, `ByteArray` after the §7 wrapper); acceptance = linear time, no per-byte boxing (confirms the return-the-rest design).

## 2. Iso (partial isomorphisms, the category)

- [x] 2.1 `Iso α β` with `apply`/`unapply` + the inverse `law` field.
- [x] 2.2 `Category Iso` (`∘`, `id`) with the composition law proved.
- [x] 2.3 Product bifunctor `×`, `associate`, `commute`, `unit`.
- [x] 2.4 `element`, `subset`, `inverse` (carry `[DecidableEq α]`/`[Decidable p]`).
- [x] 2.5 `foldl`/`iterate` (paper §5.2/5.3), `foldl : Iso (α × β) α → Iso (α, List β) α` — `foldl` done and proved (`Iso.MeasureDecreases` + well-founded recursion); `iterate` deliberately omitted (forward/backward fixpoints need not coincide, so no field law without a per-element precondition).

## 3. Codec (description interface, over bytes)

- [x] 3.1 The interface: `$`, `*`, `|`/`empty`, `pure`, `byte : Codec UInt8`.
- [x] 3.2 Declare `Rel : Codec α → α → List UInt8 → Prop` (so `Unambiguous` has no forward reference; theorems live in §5).

## 4. Two interpretations (decode / encode)

- [x] 4.1 Deterministic decoder `decode : Codec α → List UInt8 → Except DecodeError (α × List UInt8)` (returns value + remaining bytes; no cursor; no backtracking; no peeking).
- [x] 4.2 Builder encoder `encode : Codec α → α → Option (List UInt8)` (partial; rejects out-of-domain).
- [x] 4.3 `NoAlt` discipline (the roundtrip is proved unconditionally on the `alt`-free fragment); deterministic decoder is sound-and-complete on that domain; `|` is committed choice. `Unambiguous` (per-demo obligation) is not decidable by the library.

## 5. Rel (denotational semantics) + roundtrip theorems

- [x] 5.1 `Rel` over whole byte sequences (remaining-bytes is private to `decode`).
- [x] 5.2 Bidirectional law: `NoAlt d → (Rel d x s ↔ decode d s = .ok (x, []))` (as `decode_spec`/`bidir`; the `alt` case → prefix-disjointness, §8).
- [x] 5.3 Roundtrip: `NoAlt d → (encode d x = some s → decode d s = .ok (x, []))`.
- [x] 5.4 Prove the laws by `simp`/`rfl`/induction — no solver.

## 6. Derived combinators (generic, byte-agnostic)

- [x] 6.1 `many`, `*>`, `<*`, `between`; `chainl1` built on §2.5 `Iso.foldl`.
- [ ] 6.2 `chainr1` (dual of `chainl1`), `some`/`many1`, `sepBy`/`sepBy1`,
  `optional`/`maybe`/`choice` — see §8 (gated on prefix-disjointness).

## 7. Benchmark, extraction, docs

- [ ] 7.1 Extract the interpreter hot path to C/LLVM; confirm `Prop` proofs erase.
- [ ] 7.2 Benchmark `decode`/`encode` on a synthetic `byte`/`many` description — linear time, no per-byte boxing; record the number.
- [ ] 7.3 Confirm `get!`/remaining-bytes (not `getElem`-with-proof) actually runs post-extraction.
- [ ] 7.4 `README.md`: guarantee, `Iso`/`Codec`/`Rel` model, pure-framework scope, combinator table, usage.
- [x] 7.5 Zero-`sorry` + `#print axioms` = stdlib only (`propext`, `Classical.choice`, `Quot.sound`).
- [x] 7.6 Document the deliberate departures (byte core, return-the-rest decode, deterministic single result, committed `|`, lossless capture) and why; note `lean-binary`/`lean-text` as downstream consumers.

## 8. `alt` prefix-disjointness (the blocking soundness condition)

- [ ] 8.1 Define a **structural non-emptiness predicate** `NonNull : Codec α → Prop`
  (like `NoAlt`): `NonNull byte = True`, `NonNull (pure _) = False`,
  `NonNull (d₁ * d₂) = NonNull d₁ ∨ NonNull d₂`, `NonNull (iso _ d) = NonNull d`,
  `NonNull empty = True`, `NonNull (alt d₁ d₂) = NonNull d₁ ∧ NonNull d₂`.
- [ ] 8.2 Prove the **prefix-disjointness lemma**: if `NonNull d₁`, then no string
  accepted by `d₁` is a (proper) prefix of a string accepted by `d₂` (and the
  relevant dual). This is the relation-level, cursor-free, LL(1)-style condition —
  constructive and closed by induction, no `Classical.choice`, no coinduction.
- [ ] 8.3 Extend `decode_spec`/`roundtrip`/`bidir` from `NoAlt` to descriptions
  satisfying prefix-disjointness at each `alt` (decide: compositional predicate vs.
  per-description proof obligation — see README departure #5 sub-questions).
- [ ] 8.4 Implement `some`/`many1`, `sepBy`/`sepBy1`, `optional`/`maybe`/`choice`,
  and `chainr1` — each **proven** under the `NonNull` (or equivalent) precondition;
  multi-operator `chainl1`/`chainr1` (`+ | *`) sound under the same condition.

The **decision recorded** (do not reopen): stay cursor-free — **no backtracking,
no peeking**. Prefix-disjointness is a *denotational* `Prop` over `Rel`, provable
by well-founded induction (the same style that already proved `foldl`), and is
strictly preferable to an operational cursor/lookahead state machine. The cost is
that genuinely-ambiguous formats (e.g. `if | if_then_else`) must be left-factored
by hand — the standard LL(1) restriction, surfaced as a type-level witness.
