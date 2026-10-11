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
- [x] 3.2 Declare `Rel : Codec α → α → List UInt8 → Prop` (with no forward
  reference; the two interpreters and laws live in §4/§5).

## 4. Two interpretations (decode / encode)

- [x] 4.1 **Nondeterministic (backtracking) decoder**
  `decode : Codec α → List UInt8 → List (α × List UInt8)` (returns *all*
  value+remaining pairs). `|` is list concatenation `decode d₁ s ++ decode d₂ s` —
  exactly the paper's unified parser (§4.1), no cursor/peeking/narrowing.
- [x] 4.2 Builder encoder `encode : Codec α → α → Option (List UInt8)` (partial; rejects out-of-domain).
- [x] 4.3 ~~`NoAlt`/committed-choice discipline~~ **removed.** The roundtrip and
  bidirectional laws now hold *unconditionally* for every description (see §5);
  there is no `alt` gate.

## 5. Rel (denotational semantics) + roundtrip theorems

- [x] 5.1 `Rel` over whole byte sequences (remaining-bytes is private to `decode`).
- [x] 5.2 Bidirectional law, **unconditional**: `(x, r) ∈ decode d s ↔
  ∃ s₀, s = s₀ ++ r ∧ Rel d x s₀` (`decode_spec`); whole-string case `bidir`:
  `Rel d x s ↔ (x, []) ∈ decode d s`.
- [x] 5.3 Roundtrip, **unconditional**: `encode d x = some s → (x, []) ∈ decode d s`;
  strong invariant `decode_encode`: `encode d x = some s → (x, r) ∈ decode d (s ++ r)`.
- [x] 5.4 Prove the laws by `simp`/`rfl`/induction — no solver.

## 6. Derived combinators (generic, byte-agnostic)

- [x] 6.1 `many`, `*>`, `<*`, `between`; `chainl1` built on §2.5 `Iso.foldl`.
- [x] 6.2 `chainr1` (dual of `chainl1`), `some`/`many1`, `sepBy`/`sepBy1`,
  `optional`/`maybe`/`choice` — now *unblocked* (no prefix-disjointness gate): these
  are ordinary definitions over the backtracking `|`, and their soundness falls out
  of the unconditional laws in §5. Implement them (§6.1 style). Caveat: `many` is a
  `partial` description (an infinite AST), so it is *provable* but not `#eval`-able
  in its current recursive form; making it evaluable is part of this work.

## 7. Benchmark, extraction, docs

- [ ] 7.1 Extract the interpreter hot path to C/LLVM; confirm `Prop` proofs erase.
- [ ] 7.2 Benchmark `decode`/`encode` on a synthetic `byte`/`many` description — linear time, no per-byte boxing; record the number.
- [ ] 7.3 Confirm `get!`/remaining-bytes (not `getElem`-with-proof) actually runs post-extraction.
- [ ] 7.4 `README.md`: guarantee, `Iso`/`Codec`/`Rel` model, pure-framework scope, combinator table, usage.
- [x] 7.5 Zero-`sorry` + `#print axioms` = stdlib only (`propext`, `Classical.choice`, `Quot.sound`).
- [x] 7.6 Document the deliberate departures (byte core, backtracking-union
  `|`, lossless capture) and why; note `lean-binary`/`lean-text` as downstream
  consumers.

## 8. ~~`alt` prefix-disjointness~~ — superseded by Path A (backtracking union)

This entire section is **obsolete** and the once-blocking work in it
(`NonNull`, `PrefixDisjoint`, `Disjoint`, `Unambiguous`, the prefix trichotomy,
and the `Disjoint`-gated laws) has been **deleted**. The reason it was needed at
all was the committed-`|` narrowing (departure #2/#3: deterministic
single-result decoder). Restoring the paper's *backtracking-union* `|`
(`decode (d₁ | d₂) s = decode d₁ s ++ decode d₂ s`, §4.1) makes `Rel (d₁ | d₂) =
Rel d₁ ∨ Rel d₂` and `decode` agree **by construction**, so the bidirectional and
roundtrip laws became unconditional again and no prefix condition is required —
and no prefix condition *can* work for repetition anyway (`[]` is a proper prefix
of every non-empty string, so `nil | cons` in `many` is never prefix-disjoint).

- [x] 8.1–8.3 Obsolete; the `NonNull`/`Disjoint`/`PrefixDisjoint` machinery is
  removed (file `Codec/NonNull.lean` deleted; `Codec/Sound.lean` rewritten to
  unconditional laws).
- [x] 8.4 Repetition/sum combinators (`some`/`many1`, `sepBy`/`sepBy1`,
  `optional`/`maybe`/`choice`, `chainr1`) are now **unblocked** — see §6.2.

**Final recorded decision (replaces the old “no backtracking” note):** the decoder
is the paper's **nondeterministic (backtracking) list decoder**, `|` is union,
and the laws hold unconditionally. Efficiency (the paper's own §4.4 concern about
exponential/space-leak under unlimited backtracking) is **future work** — a
separate spike to re-implement the *same* semantics efficiently, not a change to
the semantics. The type-level/denotational core (`Iso`, `Rel`, `foldl`, the laws)
is unchanged and reused.

## 9. Total repetition + re-derived list combinators (the `many` fork resolved)

**Status:** the repetition core landed via `openspec/changes/total-backtracking-decoder/`
(**complete**): `relRepeat` (least-fixpoint denotation, `Codec/Codec.lean`), `decodeRepeat`
(productive decoder, well-founded on `s.length`, `Codec/Decode.lean`), and the laws
(`productive_iff_consumesByte`, `decodeRepeat_spec`, `relRepeat_unbounded_of_empty`,
`not_productive_pure`, `Codec/Sound.lean`). `Rel` unchanged; laws unconditional.

**Next session — resolve the residual `many` opacity inside this change:**

- [ ] 9.1 Remove `partial def many` (its `Rel (many p)` is irreducibly opaque —
  `partial def` yields no equation/unfold); `many`'s denotation is `relRepeat`, its
  decoder `decodeRepeat`.
- [ ] 9.2 Re-derive `some`/`many1`, `sepBy`/`sepBy1` over `relRepeat`; re-prove
  `Rel_some` etc. against `relRepeat` (no opaque `Rel (many p)`).
- [ ] 9.3 Re-express `chainl1`/`chainr1` operand lists via `decodeRepeat` (fold via
  the existing `Iso.foldl`/`Iso.foldr`, unchanged).
- [ ] 9.4 Add the list-combinator `_spec` decoder laws over `relRepeat`, unconditional
  (productivity only as the `h` argument).
- [ ] 9.5 Gate: `lake build` clean, zero `sorry`/warnings; `#print axioms` = `[propext,
  Quot.sound]`; update `README.md` + `AGENTS.md`.
