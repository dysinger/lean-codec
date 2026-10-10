# Next Session Plan

> Status snapshot written 2026-10-10 at end of the first implementation session.
> The authoritative task ledger remains
> `openspec/changes/invertible-binary-core/tasks.md`; this file records the
> *handoff*: what is done, what is open, and the specific decisions that need
> attention next.

## Where we are

The core framework compiles cleanly (`lake build`, 9 targets, zero sorries, zero
warnings) over `List UInt8`:

- `Codec/Iso.lean` — `Iso` (law as a field), category ops, product bifunctor,
  `associate`/`commute`/`unit`/`element`/`subset`/`inverse`, and `nil`/`cons`
  list isos (§2.1–2.4).
- `Codec/Codec.lean` — the `Codec` description type (`iso`/`seq`/`alt`/`empty`/
  `pure`/`byte`) and `Rel` (defined by structural recursion on `d`) (§3, §5.1).
- `Codec/Decode.lean` / `Codec/Encode.lean` — the two interpreters, written with
  explicit `match` (not `do`) so proofs reduce (§4.1–4.2).
- `Codec/Sound.lean` — `Unambiguous`, `decode_encode` + `roundtrip` proven for
  the `alt`-free fragment (`NoAlt`) (§5.3–5.4, partial).
- `Codec/Combinators.lean` — `many` (partial), `seqRight` (`*>`), `seqLeft`
  (`<*`), `between` (§6.1, partial).

`#print axioms Codec.roundtrip` ⇒ `[propext, Quot.sound]` (stdlib-only, §7.5).

## Decisions recorded this session (read before continuing)

1. **`List UInt8`, not `ByteArray`, for the provable core.** `ByteArray`
   operations (`append`/`get!`/`extract`/`size`) are FFI-backed and do not
   reduce under `simp`/`rfl`, so the roundtrip cannot be *proved* over them in
   Lean ≤ 4.30. This is exactly the design.md mitigation
   ("fall back to a `List UInt8` model + transport lemma"). `ByteArray` becomes
   the executable wrapper (§7.1–7.3), not the proof model.

2. **The roundtrip is *not* unconditional over `alt`.** Committed `|` (a
   documented departure, paper §4.4) means `decode (alt d₁ d₂) s` will steal a
   different prefix when `encode d₁ x = none` but `d₁` still decodes `s`. The
   current `roundtrip`/`decode_encode` carry a `NoAlt d` hypothesis; `NoAlt` is
   the fragment where the law holds with no precondition.

3. **`Unambiguous` (as defined) is *insufficient* for `alt`.** The counterexample
   `alt (pure x') (pure x)` (with `x' ≠ x`) shows that even "at most one value
   per whole string" does not stop `d₁` from consuming a *different prefix/remainder*.
   Correct soundness needs a **prefix-consistency** condition (§4.4's
   "predictive parsing" note). This is a real spec ambiguity to resolve (see
   Open points).

4. **`iterate`/`foldl`/`chainl1` are deferred** (tasks 2.5, 6.1). They are
   coinductive *at the `Iso` level*: `iterate step : Iso α α` would need a
   coinduction argument for its `law` field, which a finite `def` cannot give.
   No `sorry` was introduced; they are simply not yet defined. `many` (which
   produces `Codec` values, carrying no law field) is fine as a `partial def`.

## Open points for next session

1. **[blocking the full roundtrip]** Decide the correct soundness condition for
   the `alt` case. Options: (a) strengthen `Unambiguous` to a prefix-disjointness
   predicate and prove §5.3 over it; (b) keep the `NoAlt` gate and state §5.3
   only for the `alt`-free fragment; (c) confirm the spec (§5.3 is currently
   written *without* any gate) and amend it. This is a spec question — surface it
   before coding.

2. **[§5.2]** Complete `decode_rel` (the `Rel ↔ decode` correspondence) — the
   bidirectional law. Currently only `decode_encode`/`roundtrip` exist; the
   full `Rel d x s ↔ decode d s = .ok (x, [])` statement needs the same
   prefix-consistency resolution as §5.3.

3. **[tasks 2.5 / 6.1]** `iterate`/`foldl` and `chainl1`. Likely approach: make
   the `Iso` law a *theorem* parameterized by the partial `step` rather than a
   field, or prove `iterate`'s law by well-founded induction on the number of
   steps. Needs a design decision, not just mechanical proving.

4. **[tasks 7.1–7.3]** `ByteArray` executable wrapper (`ofList`/`toList`), C/LLVM
   extraction of the interpreter hot path, and the "no per-byte boxing" / linear
   time benchmark. Confirm `get!`/remaining-bytes runs post-extraction.

5. **[task 7.4]** Rewrite `README.md`: current prose references
   `openspec/invertible-binary/` (path is actually
   `openspec/changes/invertible-binary-core/`), and says "implementation has not
   yet started" — now stale. Update to reflect the `List UInt8` core, the `NoAlt`
   gate, and the downstream `lean-binary`/`lean-text` split.

6. **[housekeeping]** `Codec/Codec.lean` has a type-vs-module collision
   (`Codec.Codec` module declaring `Codec`). Consider renaming the description
   type or the module for cleaner identifiers.

## Suggested next-session order

1. Resolve the `alt` soundness condition (Open point 1 + 2) — it unblocks both
   §5.2 and the full §5.3, and it is a *spec* change, so do it first.
2. `iterate`/`foldl` + `chainl1` (Open point 3).
3. `ByteArray` wrapper + extraction + benchmark (Open point 4).
4. README + housekeeping (Open points 5, 6).
