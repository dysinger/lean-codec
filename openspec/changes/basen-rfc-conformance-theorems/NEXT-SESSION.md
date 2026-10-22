# Next session — `basen-rfc-conformance-theorems` (re-anchored to the uniform surface)

Status at handoff: planning re-done, **0 / 19 tasks implemented** (the prior run-triple
work was on the wrong surface and is re-scoped; nothing is committed yet). This file is
the pointer for the next implementation session.

## The one thing this session settled (do not re-litigate)

**`many` is derived, not a constructor.** Both references agree and it is verified
un-implementable in Lean:

- Paper §3.4: `many p = nil $ pure () | cons $ p ∗ many p` — a _derived recursive
  combinator_, never an elementary description.
- F\* `Data.Codec.Types.fst`: no `many` at all — `satisfy_many0`/`count`, `let rec`
  over the finite input; `codec a` is a _record_ of `enc`/`dec`/`roundtrip`.
- Lean: `many {α} (p) (h : Productive p) : Codec (List α)` with a denotational
  `Productive`/`ConsumesByte` field hits the `Codec → witness → Rel/decode → Codec`
  cycle; the mutual-inductive escape is rejected by the universe check (`Codec :
Type → Type 1` vs `Rel : … → Prop`). This is the same wall `11f7072` hit — it was
  _right_ about the impossibility, _wrong_ to fall back to per-format run triples.

**The fix is packaging, not a core change.** `relRepeat`/`decodeRepeat`/`encodeRepeat`
(and `takeWhile`/`sepBy`) are already in `Combinators.lean`, law-bearing,
`[propext, Quot.sound]`-only. The uniform surface is a **`Run` value** (a `structure`
bundling `elem : Codec UInt8` + `step : ConsumesByte elem`, with `decode`/`encode`/`rel`
inherited) + a facade `encode (b : Base)` / `decode (b : Base)`. No `codec`-core change,
no `Codec.rec` conversion, no bespoke per-format function.

## Next implementation order (tasks.md §0–§5)

1. **0.1** Define `Run` in `BaseN` (downstream `../lean-basen`): `structure` over
   `elem` + `step`, decode/encode/rel inherited (`decodeRepeat_spec`/`encodeRepeat_rel`).
   **0.2** `lake build` green (no core change).
2. **1.x** Delete the bespoke base32/64 run triples (`parseB64`/`encodeB64Strict`/
   `relB64Strict`/`decodeB64Strict` + base32 analogues); keep `B32`/`B64` + block
   `Iso`s. Re-express the seven bases as `Run` values (fixed-width `count k (satisfy p)
≫ blockIso`; padded full-block + terminal-tail `alt`/`iso` onto `B32`/`B64`).
3. **2.x** Restore the facade `encode (b : Base) : List UInt8 → List UInt8` /
   `decode (b : Base) : List UInt8 → Option (List UInt8)` + `roundtrip`, dispatching
   `cases b` over the single value type (no `Base.val` family, no three shapes).
4. **3.x/4.x** Re-prove the three conformance families per base (rejection / canonical /
   converse+injectivity) over the uniform decoder; use the carried-over
   `rel_count_satisfy` forward lemma (D4) in `BaseN.Common`.
5. **5.x** Reanchor `Bench.lean` to `Codec.decode`/`Codec.encode` (or the facade), gate
   `lake build` + `lake build bench`, `#print axioms` = `[propext, Quot.sound]`,
   `nix flake check` green.

## Reviewer findings (already folded in)

The independent review (see the conversation) flagged the `many`-constructor cycle; every
point is now addressed in `design.md` D0 and the "verified negative" context. The
`openspec validate --all` is green (8/8) and the change is `state: ready`, 19 tasks.
