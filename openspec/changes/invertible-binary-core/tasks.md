# Tasks

## 1. Feasibility spike

- [x] 1.1 Confirm the paper (`PAPER.md`) is the spec; adopt `Iso` (§3.1/§5.1), the `Codec` interface (§3.4), `Rel` (§4.3), derived combinators (§6.1), `foldl`/`iterate` (§5.2/5.3); re-base to bytes (`byte : Codec UInt8`, `Rel` over `List UInt8`).
- [x] 1.2 Confirm binary + speed + high-level-Lean feasibility: `List UInt8`/`UInt8/16/32/64`/`Array`/`List`/`Nat.div/mod` are stdlib; no mathlib (`Equiv`/`PEquiv` are mathlib, NOT reused).
- [x] 1.3 Record that the `Iso` inverse law holds unconditionally (no `ignore`, so no "modulo equivalence classes" — resolved by design).
- [x] 1.4 Record that `Codec` is an inductive description AST (free-alternative / free-applicative), _not_ the paper's §3.4 typeclass — a deliberate departure so that `Rel`/`decode`/`encode` are ordinary functions over one description value (the typeclass reading would make the description implicit and block structural induction).
- [x] 1.5 Record the `List UInt8` proof-model strategy: the provable core is `List UInt8`; `ByteArray` ops don't reduce under `simp`, so it becomes a transport target later (proof ergonomics only).
- [x] 1.6 Benchmark a multi-MB roundtrip (on `List UInt8` now, `ByteArray` after the §7 wrapper); acceptance = linear time, no per-byte boxing (confirms the return-the-rest design).

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
      `decode : Codec α → List UInt8 → List (α × List UInt8)` (returns _all_
      value+remaining pairs). `|` is list concatenation `decode d₁ s ++ decode d₂ s` —
      exactly the paper's unified parser (§4.1), no cursor/peeking/narrowing.
- [x] 4.2 Builder encoder `encode : Codec α → α → Option (List UInt8)` (partial; rejects out-of-domain).
- [x] 4.3 ~~`NoAlt`/committed-choice discipline~~ **removed.** The roundtrip and
      bidirectional laws now hold _unconditionally_ for every description (see §5);
      there is no `alt` gate.

## 5. Rel (denotational semantics) + roundtrip theorems

- [x] 5.1 `Rel` over whole byte sequences (remaining-bytes is private to `decode`).
- [x] 5.2 Bidirectional law, **unconditional**: `(x, r) ∈ decode d s ↔ ∃ s₀, s = s₀ ++ r ∧ Rel d x s₀` (`decode_spec`); whole-string case `bidir`:
      `Rel d x s ↔ (x, []) ∈ decode d s`.
- [x] 5.3 Roundtrip, **unconditional**: `encode d x = some s → (x, []) ∈ decode d s`;
      strong invariant `decode_encode`: `encode d x = some s → (x, r) ∈ decode d (s ++ r)`.
- [x] 5.4 Prove the laws by `simp`/`rfl`/induction — no solver.

## 6. Derived combinators (generic, byte-agnostic)

- [x] 6.1 `many`, `*>`, `<*`, `between`; `chainl1` built on §2.5 `Iso.foldl`.
- [x] 6.2 `chainr1` (dual of `chainl1`), `optional`/`maybe`/`choice` — now
      _unblocked_ (no prefix-disjointness gate): these are ordinary definitions over
      the backtracking `|`, and their soundness falls out of the unconditional laws in
      §5. (Note: the paper's `some`/`many1`/`sepBy`/`sepBy1` are **not** exposed as
      symbols; unbounded repetition is the `relRepeat`/`decodeRepeat`/`encodeRepeat`
      triple, and `sepBy` is the `relSepBy`/`decodeSepBy`/`encodeSepBy` triple with
      sepBy1 semantics — see §9 and §10 below.) Caveat: `many` is a _semantic_ reading
      (not a finite description, see §9), so it is provable but not evaluable as a `Codec` node.

## 7. Benchmark, extraction, docs

- [x] 7.1 Extract the interpreter hot path to C/LLVM; confirm `Prop` proofs erase.
      **Done** — delivered under §10.5 (`Bench.lean` `lean_exe`, C backend); the
      LLVM-enabled toolchain landed in `llvm-lean4-toolchain`.
- [x] 7.2 Benchmark `decode`/`encode` on a synthetic `byte`/`many` description — linear time, no per-byte boxing; record the number.
      **Done** — see §10.5 / §11.10.5 measured table (linear `encodeRepeat`/`Buffer.*`;
      O(1) `decode byte`).
- [x] 7.3 Confirm `get!`/remaining-bytes (not `getElem`-with-proof) actually runs post-extraction.
      **Done** — §10.5 hot-path audit (`match` destructuring, `ByteArray.data`, no
      `getElem`-with-proof leak).
- [x] 7.4 `README.md`: guarantee, `Iso`/`Codec`/`Rel` model, pure-framework scope, combinator table, usage.
      **Done** — §10.2 / §11.10.2 full architecture statement.
- [x] 7.5 Zero-`sorry` + `#print axioms` = stdlib only `[propext, Quot.sound]`
      (the `Classical.choice` listed in an earlier draft is **superseded** — see §9.5
      and §10.0a; the chain laws are `[propext, Quot.sound]`, `relRepeat_induction` is
      `[propext]`).
- [x] 7.6 Document the deliberate departures (byte core, backtracking-union
      `|`, lossless capture) and why; note `lean-binary`/`lean-text` as downstream
      consumers.

## 8. ~~`alt` prefix-disjointness~~ — superseded by Path A (backtracking union)

This entire section is **obsolete** and the once-blocking work in it
(`NonNull`, `PrefixDisjoint`, `Disjoint`, `Unambiguous`, the prefix trichotomy,
and the `Disjoint`-gated laws) has been **deleted**. The reason it was needed at
all was the committed-`|` narrowing (`[D2]`/`[D3]` in `README.md`: deterministic
single-result decoder). Restoring the paper's _backtracking-union_ `|`
(`decode (d₁ | d₂) s = decode d₁ s ++ decode d₂ s`, §4.1) makes `Rel (d₁ | d₂) = Rel d₁ ∨ Rel d₂` and `decode` agree **by construction**, so the bidirectional and
roundtrip laws became unconditional again and no prefix condition is required —
and no prefix condition _can_ work for repetition anyway (`[]` is a proper prefix
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
separate spike to re-implement the _same_ semantics efficiently, not a change to
the semantics. The type-level/denotational core (`Iso`, `Rel`, `foldl`, the laws)
is unchanged and reused.

## 9. Total repetition + re-derived list combinators (the `many` fork resolved)

**Status:** the repetition core landed via `openspec/changes/total-backtracking-decoder/`
(**complete**): `relRepeat` (least-fixpoint denotation, `Codec/Codec.lean`), `decodeRepeat`
(productive decoder, well-founded on `s.length`, `Codec/Decode.lean`), and the laws
(`productive_iff_consumesByte`, `decodeRepeat_spec`, `relRepeat_unbounded_of_empty`,
`not_productive_pure`, `Codec/Sound.lean`). `Rel` unchanged; laws unconditional.

**Next session — resolve the residual `many` opacity inside this change:**

- [x] 9.1 Remove `partial def many` (its `Rel (many p)` is irreducibly opaque —
      `partial def` yields no equation/unfold); `many`'s denotation is `relRepeat`, its
      decoder `decodeRepeat`. **Done:** `many` removed; the three readings are
      `relRepeat`/`decodeRepeat`/`encodeRepeat` (the latter newly added in
      `Codec/Encode.lean` with law `encodeRepeat_rel`).
- [x] 9.2 Re-derive `some`/`many1`, `sepBy`/`sepBy1` over `relRepeat`; re-prove
      `Rel_some` etc. against `relRepeat` (no opaque `Rel (many p)`). **Done:**
      `some`/`many1` collapse to `relRepeat` on a non-empty list; `sepBy`/`sepBy1` are
      `relSepBy`/`decodeSepBy`/`encodeSepBy` with `decodeSepBy_spec`/`encodeSepBy_rel`.
- [x] 9.3 Re-express `chainl1`/`chainr1` operand lists via `decodeRepeat` (fold via
      the existing `Iso.foldl`/`Iso.foldr`, unchanged). **Done:** `relChainl1`/`relChainr1`,
      `decodeChainl1`/`decodeChainr1` (taking `hsep`), `encodeChainl1`/`encodeChainr1`.
- [x] 9.4 Add the list-combinator `_spec` decoder laws over `relRepeat`, unconditional
      (productivity only as the `h` argument). **Done:** `decodeSepBy_spec`,
      `decodeChainl1_spec`, `decodeChainr1_spec` (bidirectional) plus `encodeSepBy_rel`,
      `encodeChainl1_rel`, `encodeChainr1_rel` (encoder soundness).
- [x] 9.5 Gate: `lake build` clean, zero `sorry`/warnings; `#print axioms` = `[propext, Quot.sound]`; update `README.md` + `AGENTS.md`. **Done** (the chain laws carry
      `[propext, Quot.sound]` via `foldl`/`foldr`'s well-founded recursion; `decodeRepeat`/
      `encodeRepeat` are axiom-free).

## 10. Next session — remaining work (ledger)

`invertible-binary-core` is **feature-complete and proven** (zero sorries/warnings,
`[propext, Quot.sound]`). The following are the remaining items, in order. They are
**not** part of this change's proven core; efficiency and the `ByteArray` wrapper are
post-core deliverables (the paper's §4.4 open problem and the §7 transport target).

### Resolved this session (from the code-quality review)

- [x] 10.0a **The `foldl`/`foldr`/`chainl1`/`chainr1` family was `noncomputable`** —
      a review flagged this as making the chain combinators non-extractable/non-`#eval`-able.
      Investigation showed the `noncomputable` annotations on `foldUnapply`/`foldrUnapply`/
      `foldl`/`foldr` and the four chain combinators were **spurious**: `WellFounded.fix`
      over a computable `measure : α → Nat` is already computable. Dropped; the entire
      chain family is now computable with no change to the laws or axiom footprint.
      **Note (closes review finding #1):** `Iso.foldl`/`Codec.decodeChainl1` now `#print axioms` ⇒ `[propext, Quot.sound]`, same baseline.
- [x] 10.0b **Stale `alt` docstrings** (3 sites: `Codec.lean` §3.3 list, `alt`
      constructor, `alt` alias) still said "committed choice"; corrected to "backtracking
      union" to match the implemented `Rel (d₁ | d₂) = Rel d₁ ∨ Rel d₂` / `decode (d₁ | d₂) = decode d₁ ++ decode d₂` semantics (closes review finding #2).
- [x] 10.0c **Missing decode→encode / injectivity half of "byte-exact bidirectional"**
      (review finding #4). Added to `Codec/Sound.lean`: `Unambiguous` (value-directed),
      `Functional` (string-directed), `encode_ne_none` (Rel → encode ≠ none, induction on
      `d`), `encode_of_decode` (`Functional d ⇒ (x, []) ∈ decode d s → encode d x = some s`),
      `encode_injective_of_unambiguous`. **The honest result:** the decode→encode byte-exact
      converse is **false** in general (needs `Functional`); the unconditional law remains the
      encode→decode `roundtrip`. This is a tightening of the claim, not a weakening of the core.

### Remaining (reordered: rename + organization/docs before README/downstream)

- [x] 10.1 **Housekeeping: resolve the `Codec` type-vs-module collision** (neé 10.5).
      **Done (decision):** kept the type name `Codec`; the uniform `namespace Codec`
      was restored in `Codec/Codec.lean`, so `Rel`/`relRepeat`/`relRepeat_induction`/
      `Rel_*`/`single`/`Productive` now live at `Codec.*` (no type rename).
      The inductive `Codec` lives at top level in `Codec/Codec.lean` (no namespace), while
      the other `Codec/*.lean` modules open `namespace Codec` — so the _type_ `Codec` and the
      _namespace_ `Codec` collide (and the root file `Codec.lean` collides with the `Codec/`
      directory). **Consequence for organization:** `Rel`/`relRepeat`/`Rel_*`/`single`/`Productive`
      are currently _top-level_ in `Codec/Codec.lean`, whereas `decode`/`encode`/all the laws live
      inside `namespace Codec` — the denotation lives at a different nesting level than the
      interpreters of it. **Decision to make first (drives every other naming item):** rename the
      description _type_ (e.g. `Desc` or `Syntax`, matching paper §3.4) so the module/namespace
      `Codec` can hold _all_ of `Rel`/`decode`/`encode`/the laws consistently, OR keep the type
      name `Codec` and move _everything_ (incl. `Rel`) into one `namespace Codec` accepting the
      `Codec.Codec` prefix. Do this **before** the README/downstream hard-code names. (The
      `sepBy`-`[]` docstrings are **done**.)

- [x] 10.1a **Code organization: lay out the files first-principles, bottom-up.** Each
      `Codec/*.lean` module already has section headers, but the _within-section ordering and
      nesting_ should be audited: (i) `Codec/Codec.lean` — `Rel_*` lemmas should follow the
      **constructor order** `iso, seq, alt, empty, pure, byte` (currently iso, alt, pure, byte
      after the seq/empty lemmas were deleted; either restore `Rel_seq`/`Rel_empty` or reorder +
      document the gap), and `single`, `Inhabited`, `Rel`, then `relRepeat`/`Productive`/their
      lemmas should each sit in one `/-!` section with a top-of-file outline; (ii) `Codec/Iso.lean`
      — split the mixed "Structural isomorphisms" section so `associate`/`commute`/`unit` (pure
      structure) come before the `Decidable`-carrying `element`/`subset`, and `inverse`/`optionSome`
      move to a "combinators" section; order `nil`/`cons` alphabetically/dually; (iii) the fold
      block (`MeasureDecreases`/`foldApply`/`foldUnapply`/…/ `foldl`, then the `R` duals) should
      be a self-contained, header-annotated region readable top-to-bottom as "measure → apply →
      unfold → soundness → completeness → the Iso"; (iv) `Sound.lean` is already well-ordered
      (encode_rel → decode_seq_mem → decode_spec → bidir → decode_encode → roundtrip → repetition
      → decode→encode) — preserve it, and add a one-line `/-!`-level map at the top of each file
      so a porter can navigate the proof tree. - **Done:** `Rel_*` in constructor order with `Rel_seq`/`Rel_empty` restored;
      `Iso.lean` structural isos reordered (`associate`/`commute`/`unit` before
      `element`/`subset`, then `inverse`/`optionSome`); the fold block is a
      header-annotated region; module `/-!` maps present.

- [x] 10.1b **Naming normalization + alphabetization (idiomatic Lean, mathlib style).**
      Functions named like their return type; theorems `snake_case`; alphabetize sibling groups.
      Concrete fixes: (i) delete the unused `app`/`unapp` wrappers in `Iso.lean` (dead, like
      `isoMap`/`fail` were); (ii) reconcile `comp` vs `trans` (both exist for category composition
      — keep one idiomatic name, e.g. `comp` or `∘`-notation only); (iii) drop the ad-hoc prime on
      `foldrApply'` and rename the apply-direction family consistently (`foldlApply` vs `foldrApply' → `foldlApply`/`foldrApply`with the terminal-seed restriction named explicitly, e.g.`foldlApplyTerminal`or fold the restriction into the Iso's`apply`with a doc note); (iv)`MeasureDecreases`/`MeasureDecreasesR`— consider a single parameterized name or document the`R`suffix as the left/right step-type marker; (v)`Rel\_\*` lemma names should be a single convention (`Rel_iso`/`Rel_seq`/`Rel_alt`/`Rel_empty`/`Rel_pure`/`Rel_byte\`) matching the
      constructors, with any _missing_ one either restored or documented as intentionally-absent. - **Done:** dead `app`/`unapp` (and `isoMap`/`fail`) removed; `trans` is the sole
      composition name (`comp` gone); the ad-hoc prime on `foldrApply'` dropped
      (`foldrApply`); `Rel_*` uses the single constructor-matched convention.

- [x] 10.1c **Code documentation to standards.** Audit every public declaration for: a
      one-line doc-comment (`/-- … -/`) stating _what_ and _why_ (not just "the X of Y");
      `/-! … -/` section headers with a clear outline; cross-references to the paper's § and to
      the README `[D#]`/`[S#]` anchors where a departure/strengthening is involved; and the
      `mathlib` convention that a `Prop`-valued def (e.g. `Rel`, `Productive`, `ConsumesByte`,
      `Unambiguous`, `Functional`) is freshly documented as a _relation/predicate_, not a lemma.
      Ensure the module `-!` doc comes _after_ `import` (per the Lean skill) and that no `-/` byte
      pair appears inside prose (Lexer terminates the block). Verify docstrings do not reference
      the deleted `many`/`sepBy`/`some`/`many1` symbols as if they exist. - **Done:** module `/-!` docs sit after `import` in every `Codec/*.lean`; public
      decls carry doc-comments; the `Prop`-valued defs (`Rel`, `Productive`,
      `ConsumesByte`, `Unambiguous`, `Functional`) are documented as relations. No
      stale references to the deleted `many`/`sepBy`/`some`/`many1` symbols.

- [x] 10.2 **`README.md` rewrite** (§7.4) — after 10.1/10.1a/10.1b/10.1c (names/organization
      may change): combinator table → the semantic-repetition split (`relRepeat`/`decodeRepeat`/
      `encodeRepeat` + `sepBy`/`chainl1` triples), the downstream split (`lean-binary`/`lean-text`),
      and the corrected decode→encode scoping (encode→decode unconditional roundtrip; converse
      under `Functional`). The canonical `[D#]`/`[S#]` table and "Why these choices?" section
      already reflect the _semantics_; only the symbol/namespace names must be re-checked against
      the 10.1 rename. - **Done** — see §11.10.2: the README is the full architecture statement (complete
      `[D1]`–`[D8]`/`[S1]`–`[S6]` table + "Why these choices"), plus `CHANGELOG.md`
      and `LICENSE.md`.

- [ ] 10.3 **Theorem-coverage cleanups** (review #3/#6/#7): (a) `relRepeat` "least fixpoint"
      — **done**: `relRepeat_induction` proved (axioms `[propext]`); (b) `foldl`/`foldr` share
      ~380 lines of near-duplicate well-founded machinery — factor a common `unfoldBy` (this is
      now partly covered by 10.1a's fold-block rework; do them together); (c) dead code — **done**
      for `foldrApply_append`/`cons_head_tail`/`isoMap`/`seq`/`alt`/`fail`; remaining `app`/`unapp`
      are ticketed in 10.1b.

- [x] 10.3a **Chain-combinator decode→encode / injectivity companions** (review CODE-1).
      The primitives gained `encode_ne_none`/`encode_of_decode`/`encode_injective_of_unambiguous`,
      but the chain combinators (`decodeChainl1`/`decodeChainr1`/`encodeChainl1`/`encodeChainr1`)
      have only the soundness direction (`_rel`) and the decoder `_spec` — no `Functional (relChain* …)`-style completeness, no decode→encode law, no injectivity. **Done:** the
      chain combinators are _relations_ not `Codec` values, so the converse laws are stated over
      two new relation-level predicates `relFunctional`/`relUnambiguous` (the generic forms of
      which `Functional`/`Unambiguous` are the `Rel d` special cases), plus `encodeRepeat_ne_none`
      (the `relRepeat`-level `encode_ne_none`). New laws in `Combinators.lean`: `encodeChainl1_ne_none`/
      `encodeChainr1_ne_none` (completeness), `encodeChainl1_of_decode`/`encodeChainr1_of_decode`
      (decode→encode under `relFunctional (relChain* …)`), and
      `encodeChainl1_injective_of_unambiguous`/`encodeChainr1_injective_of_unambiguous` (under
      `relUnambiguous`). Axioms `[propext, Quot.sound]` throughout (`encodeRepeat_ne_none` is
      `[propext]`-only).

- [x] 10.4 **`Buffer` transport surface** (§7.1 partial / review #10; formerly the
      _`ByteArray` wrapper_) — transport the provable `Bytes` (= `List UInt8`) core to a
      packed, `ByteArray`-backed executable surface. **Done** in `Codec/Buffer.lean`: a
      `Buffer` newtype over `ByteArray`, `toBytes`/`ofBytes` routed through `ByteArray.data`
      (the reducible `Array`) rather than the opaque `ByteArray.toList` so the transport laws
      close by `rfl`; the transported interpreters `decodeBuffer`/`encodeBuffer`; and the
      bar-transferred laws `decodeBuffer_eq`/`encodeBuffer_eq`/`decodeBuffer_spec`/
      `roundtripBuffer` (composed from `decode_spec`/`roundtrip`, `[propext, Quot.sound]`,
      no new induction). The `getElem`-with-proof hot-path audit (extraction-level) remains
      part of 10.5.

- [x] 10.5 **Extraction + benchmark** (§7.2/§7.3) — extract the `decode`/`encode` hot
      path to C/LLVM; benchmark a multi-MB roundtrip (`byte`/`many`), record linear time.
      Covers task 1.6 too. (Now unblocked for the chain combinators by 10.0a.)
      **Done.** Tooling decision: the pinned `lean4` 4.34.1 reports `--features []` and
      `-b` (LLVM bitcode) hits a build-time assertion (`Please build a version of Lean4 with -DLLVM=ON`), so the **C backend** (`lake env lean -c`, and lake's own
      `lean_exe` link which produces the `.c`/`.c.o` under `.lake/build/ir/`) is the
      extraction path — not an LLVM-provisioned toolchain. Deliverable: a `bench`
      `lean_exe` (`Bench.lean`, root-level `main`, imported by nothing else) that drives
      `decode`/`encodeRepeat`/`decodeRepeat`/`Buffer.ofBytes`/`Buffer.toBytes` on a
      synthetic `byte`/`many` description, wired into `default.nix` as the `bench`
      derivation (installs `bin/bench`, `meta.mainProgram = "bench"`) and exposed as
      `flake.nix#packages.<system>.bench`.

  **Measured (arm64, `nix build .#bench`; reps=20):**

  | op                  | 512 KiB    | 1 MiB     | 2 MiB      | scaling |
  | ------------------- | ---------- | --------- | ---------- | ------- |
  | `decode byte`       | 100–122 ns | 79–108 ns | 108–164 ns | O(1)    |
  | `encodeRepeat byte` | 13.2 ms    | 31.9 ms   | 64.2 ms    | linear  |
  | `Buffer.ofBytes`    | 2.1 ms     | 5.3 ms    | 8.2 ms     | linear  |
  | `Buffer.toBytes`    | 3.7 ms     | 8.8 ms    | 14.4 ms    | linear  |

  The backward "many" decoder is **quadratic** as the paper §4.4 warns:
  `decodeRepeat byte [8192]` ≈ 2.45 s and `[16384]` ≈ 13.8 s (~2× input → ~5.6×
  time). This is the _output-size-inherent_ blowup (all `m+1` prefixes of up to
  `m` bytes each), not a boxing leak, and is exactly what 10.6 addresses.

  **Hot-path audit (§7.3, "no `getElem`-with-proof leak"):** `decode` destructures
  its input by `match` (never indexed `getElem`), so the only per-step cost is one
  `List.cons` peel; `Buffer.toBytes` routes through `ByteArray.data` (the reducible
  `Array`), not the opaque `ByteArray.toList`, so the transport laws close by `rfl`
  and no `getElem`-with-proof term survives extraction. `Bytes = List UInt8` boxes
  each byte as a `lean_object` (that is the proof substrate); the packed,
  no-boxing representation is `Buffer` (ByteArray), measured by `Buffer.ofBytes`/
  `Buffer.toBytes`. The benchmark home per handoff is downstream `lean-binary`;
  this harness is the _core_ extraction/link vehicle.

  **§10.6 follow-up (Tier A landed in `efficient-backtracking-decoder`):** the
  same `bench` harness gained `decodeFull`/`decodeRepeatFull`/`decodeFast` legs.
  Measured (same machine, reps=20): `decodeRepeat byte [16384]` = 11.2 s (the
  quadratic baseline above); `decodeFull byte [16384]` = 545 µs and
  `decodeRepeatFull byte [16384]` = 632 µs (**~20,000× faster, sub-millisecond**);
  `decodeFast byte` = O(1) (~31 ns, byte-exact equal to `decode byte`). The
  full-consumption ask is now sub-second by ~4 orders of magnitude.

- [x] 10.6 **Efficiency spike (the paper's §4.4 open problem — _last_)** — memoization/DP
      over the _same_ denotation, separate from correctness. Does **not** change semantics.
      **Tier A landed** in `efficient-backtracking-decoder` (`decodeFull`/`decodeRepeatFull`/
      `decodeFast`, all proved denotationally equal, `[propext, Quot.sound]`-only; measured
      ~20,000× faster on the full-consumption ask — see the §10.5 follow-up note above).
      **Tier B (memoizing chart) remains a separate change**, not part of §10.

## 11. Next session — remaining §10 plan (10.5 done / 10.6 last)

Ordered, with the decisions to resolve **before** coding each:

- [x] **10.2 README rewrite.** **Done** — written as the **full architecture
      statement**: intent, the paper TL;DR, the **complete** `[D1]`–`[D8]`/`[S1]`–`[S6]`
      departures/strengthenings (each with a layman "why these choices" justification),
      scope, and getting-started. Deliberately **no** status/issues section (that is
      `openspec/`/`AGENTS.md`) and **no** process/history narrative — the README is then
      purely _about the project and the paper_. Also added `CHANGELOG.md` and `LICENSE.md`
      (AGPL-3.0 + commercial option). Names: `Bytes` (substrate) / `Buffer` (transport),
      no type rename.
- [x] **10.5 Extraction + benchmark.** **Done** — see the §10.5 entry above for the
      full record. Tooling decision: **C backend** (`lake env lean -c` and lake's own
      `lean_exe` link), **not** an LLVM-provisioned toolchain (`--features []`; `-b`
      asserts `-DLLVM=ON`). `Bench.lean` is a top-level `lean_exe` driving the hot paths;
      wired as `default.nix#bench` (installs `bin/bench`, `mainProgram = "bench"`) and
      `flake.nix#packages.<system>.bench`. Measured: `encodeRepeat`/`Buffer.ofBytes`/
      `Buffer.toBytes` scale linearly (64 ms / 8 ms / 14 ms at 2 MiB); `decode byte` is
      O(1); `decodeRepeat byte [16384]` ≈ 13.8 s (quadratic, paper §4.4). Hot-path audit
      clean (`match` destructuring, `ByteArray.data`, no `getElem`-with-proof leak).
      Accepts task 1.6; the benchmark _home_ is downstream `lean-binary`.
- [x] **10.6 Efficiency spike (paper §4.4).** **Tier A done** in
      (`efficient-backtracking-decoder`); no denotation change: `decodeFull`/
      `decodeRepeatFull` (`Option`-valued full-consumption "many") + `decodeFast`
      (list-fused `decode`) are proved equal to the spec (`[propext, Quot.sound]`-only),
      with transfer laws; measured **~20,000× faster** on the full-consumption ask
      (545 µs vs 11.2 s at `[16384]`). **Tier B (memoizing chart) deferred** to a
      separate change. See `openspec/changes/efficient-backtracking-decoder/`.
- [x] **§10.6 buffer-carrier tier (F\* two-tier run-model, no FFI/compiler).** **Done** in
      `buffer-carrier-decoders` — the `Array UInt8` + `Nat`-index run-model proved equal
      to the `List` spec. New `Codec/DecodeArray.lean` (`decodeArray`, internal relative
      `decodeArrayRel`, `decodeArray_eq`/`decodeArrayRel_eq`, `decodeFullArray`/
      `decodeFullArray_spec`, helpers `decode_suffix`/`drop_add_length_of_append`/
      `flatMap_congr`) and `Codec/EncodeArray.lean` (`encodeArray`/`encodeArray_eq`), plus
      three transfer laws in `Codec/Sound.lean` (`decodeArray_spec`, `encodeArray_rel`,
      `roundtripArray`) — all `[propext, Quot.sound]`-only. **Notable lesson:** the
      _membership_-form refinement over `drop` is **wrong** for `pure`/empty-remainder
      (index info lost): the correct form is the function-level
      `decodeArray d a i = (decode d (drop i)).map (fun (x,r) => (x, i + (drop i).length
  - r.length))`. And `Array`here reduces to its`toList`field (no`a.data`; run the
proofs over `a.toList`, reach `ByteArray`only through`ByteArray.data`).
`Bench.lean`gained`decodeArray`/`encodeArray`/`decodeFullArray`legs (5.1);
measured (arm64, reps=20):`decodeFullArray byte [16384]`= 731 µs (≈`decodeFull`'s
1017 µs — it is the composition, same list cost); `decodeArray byte [1048576]`=
16.8 µs and`encodeArray byte`= 914 ns. **Caveat:** the carrier swap **does not**
deliver the design's hoped ~5–20× here, because stdlib`Array.size = a.toList.length`is _structural_ O(n) (no cached length field) — so`decodeArray`'s `i < a.size`guard
walks the whole list each call. The native-array index recursion is correct and
proved-equal, but the`size` cost is the ceiling; the FFI/`@[extern]`/compiler tier
    (a separate deferred change) is where that ceiling is actually lifted.
- [x] **§10.6 LLVM toolchain (the `size`-cost ceiling, lifted without FFI/compiler).**
      **Done** in `llvm-lean4-toolchain` — the pin `lean4` was built _without LLVM_, so
      `Array`/`ByteArray` fell back to pure-`List` (`Array.size = List.length` O(n), no
      `@[extern]` C++ primops) and `lake build bench` failed to link (`ld: library 'c++'
not found`). Fixed by building `lean4` with `LLVM=ON` and the _consistent_ LLVM 19
      toolchain (`llvmPackages_19.stdenv`), wired into every path. Now
      `lean --features` ⇒ `[LLVM]`; `lake build bench` links; the extracted
      `decodeArray byte` lowers to `lean_array_get_size`/`lean_array_fget_borrowed` (O(1),
      flat ~73–188 ns over a 1024× size range) — the O(n) `size` walk is gone.
      Proof gate green, axioms unchanged (`[propext, Quot.sound]`). The author-FFI/compiler
      tier remains deferred; this is only the stock Lean build configuration flipped on.
      See `openspec/changes/llvm-lean4-toolchain/`.
- [x] **§10.6 ByteArray carrier + LEB128 varint (the densest stdlib carrier — the last
      lever).** **Done** in `bytearray-carrier-decoders` — on top of the LLVM-enabled
      toolchain, the **packed `ByteArray` carrier** (`LeanScalarArray`, contiguous
      `uint8_t*`, cached size, `lean_byte_array_get`/`lean_sarray_size`/`lean_sarray_push`,
      **no per-byte boxing**, where `Array UInt8` still boxes each byte), proved equal to
      the `Bytes` spec by the function-level refinement through the reducible
      `ByteArray.data`. New `Codec/DecodeByteArray.lean` (`decodeByteArray d a i =
decodeArray d a.data i`, `decodeByteArray_eq`, `decodeFullByteArray`/`_spec`) and
      `Codec/EncodeByteArray.lean` (`encodeByteArray`/`encodeByteArray_eq`), three transfer
      laws in `Codec/Sound.lean` (`decodeByteArray_spec`/`encodeByteArray_rel`/
      `roundtripByteArray`), and `Codec/VarBinary.lean` — the F\* LEB128 `varint :
Iso Nat Bytes` (7 data bits/byte + continuation high bit, `0 ↦ [0]`,
      `128 ↦ [0x80,0x01]`, `300 ↦ [0xAC,0x02]`) with its roundtrip law (`dec_enc`/`enc_dec`,
      rejecting overlong/non-canonical encodings) plus the `ByteArray`-carrier run-model
      `decodeVarint`/`encodeVarint` + `decodeVarint_eq`/`encodeVarint_eq`/`roundtripVarint`.
      All `[propext, Quot.sound]`-only. **Finding:** `ByteArray` is the densest stdlib
      carrier; the toolchain (LLVM) was the blocker, now the carrier is the last lever.
      **Native-index rewrite (tasks 4.1–4.3 of `bytearray-carrier-decoders`):** the
      carriers were initially shipped by composition over `decodeArray`/`decodeFull`,
      which re-materialized `a.toList` and ran the list decoder — no packed byte was
      ever read. Re-opened as **native `WellFounded.fix` recursions** reading `a[i]`
      (`decodeByteArrayRel`/`decodeFullByteArray` over `ByteArray`, `decodeFullArray`
      over `Array UInt8`), proved equal to the `Bytes` spec via the membership-form
      `decodeFullByteArray_spec`/`decodeFullArray_spec` (mirrors of `decodeFull_spec`,
      same `huniq`), with candidate-correspondence + step lemmas
      (`decodeFullByteArrayStep_some`/`_ne_none`, etc.). The extracted C now lowers to
      `lean_byte_array_fget`/`lean_array_fget_borrowed` (O(1) packed read), no `.toList`.
      `Bench.lean`gained`decodeByteArray`/`encodeByteArray`/`decodeFullByteArray`/
      `decodeVarint`/`encodeVarint`legs: measured (arm64, reps=20)`encodeVarint 12345678`
      ≈ 52 ns/op,`decodeVarint`≈ 108 ns/op,`encodeByteArray byte`≈ 62 ns/op;
      `decodeByteArray byte [1 MiB]`= **83 ns** (was ≈ 0.4 ms compositional — ~4800×),
      `decodeFullByteArray byte [8192]`≈ 298 µs / `decodeFullArray byte [8192]`≈ 302 µs
      (native, but full-consumption is result-list-construction-bound so ≈ `decodeFull`
      ~271 µs — the O(1)-index carrier win is on the single/multi-byte _reads_, not the
      list-building path).
      The author-FFI/compiler tier **remains deferred**; no `[D#]`/`[S#]` anchor change.
      See `openspec/changes/bytearray-carrier-decoders/`.

**Planning-vs-build note:** the `proposal.md`/`design.md`/`specs/codec/spec.md` in this
change were **updated this session** to the _implemented_ reality (backtracking-union
`|`, nondeterministic `List` decoder, unconditional laws, semantic `relRepeat`/
`decodeRepeat`/`encodeRepeat`), replacing the earlier superseded deterministic/`NoAlt`
/committed-`|` plan that predated the reversed `[D5]`. No new spec delta is
required for the remaining §10 work unless 10.1 is spun into its own change.
