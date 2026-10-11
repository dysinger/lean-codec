# Tasks

## 1. Correct productive repetition decoder (`Codec/Decode.lean`)

- [x] 1.1 Change `decode`'s `many` handling to well-founded recursion on
      `s.length` (productive corecursion: empty result, then each `cons` step on a
      strictly shorter remaining string via `decode p`).
- [x] 1.2 The `many` fixpoint: `decode (many p) s = ([], s) :: (decode p s).flatMap (fun (x, s₁) => (decode (many p) s₁).map (fun (xs, r) => (x::xs, r)))`,
      with the recursive call structurally guarded by `s₁` being a proper suffix
      (established by the `p`-consumes-a-byte witness, passed as an argument — not a
      global predicate).
- [x] 1.3 `#eval decode (many Codec.byte) [1,2,3]` = the four results (empty
      plus prefixes), then terminates.
- [x] 1.4 Confirm `decode (many (Codec.pure ())) []` does **not** fabricate
      `([()], [])`; it is the provably-infinite case (documented, not faked).

## 2. Proved totality boundary (`Codec/Sound.lean`)

- [x] 2.1 State and prove: `(∀ x s₁, Rel p x s₁ → s₁ ≠ []) →` the repetition
      decoder terminates (well-founded on `s.length`).
- [x] 2.2 State the contrapositive: if `Rel p x []` for some `x`, then
      `decode (many p) []` yields infinitely many `[]` results (so no total
      strict-list decoder exists) — a lemma, not a gate.

## 3. Laws re-proved unconditionally (`Codec/Sound.lean`)

- [x] 3.1 `Rel` unchanged; verify the existing `decode_spec`, `bidir`,
      `encode_rel`, `decode_encode`, `roundtrip` still hold for every description,
      with the `many` case's `Rel` being the least fixpoint.
- [x] 3.2 Re-prove the `many` case of the laws via the least-fixpoint `Rel`,
      unconditional (no productivity hypothesis in the _statements_).

## 4. De-confuse `many` (`Codec/Combinators.lean`)

- [x] 4.1 `many` remains a derived combinator; the docstring states: "total as a
      _semantics_ (`Rel`); the strict-list decoder is total exactly for productive
      `p` (theorem), and partial only for the empty-matching (provably-infinite)
      case."
- [x] 4.2 Remove any stale "fuel"/"Productive" language.

## 5. Proof gate & docs

- [x] 5.1 `lake build` clean; zero `sorry`, zero warnings.
- [x] 5.2 `#print axioms` on each law = `[propext, Quot.sound]`.
- [x] 5.3 Update `README.md` (decoder + `many` totality note) and `AGENTS.md`
      handoff.
- [x] 5.4 Commit each file individually; print the staged set first.
