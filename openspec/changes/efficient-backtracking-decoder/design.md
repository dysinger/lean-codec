# Design

## Context

The proven core (`Codec/Decode.lean`) is a *specification*: `decode d s` returns the
whole backtracking result list, and `decodeRepeat p h s` enumerates every prefix. The
§10.5 benchmark showed the cost is *not* constant-factor — `decodeRepeat Codec.byte [16384]` is ≈ 13.8 s because the "many" decoder materializes all `n+1` prefixes (each
up to `n` bytes), i.e. Θ(n²) output, and the `alt` append re-traverses shared prefixes.
The proof style of the core is `rfl`/`simp`/`induction` only, `[propext, Quot.sound]`
axiom-free — any efficient interpreter must keep its *equality* proofs in that style.

## Goals / Non-Goals

**Goals:**

- Replace the *runtime* of `decode`/`decodeRepeat` with interpreters that (a) do not
  re-traverse shared prefixes, and (b) do not materialize the all-prefixes list when a
  single/full-consumption result is asked for — while remaining a total `List`/`Option`
  function and being **provably equal** to the spec.
- Keep every existing law valid by *rewrite through equality*, not by re-proving.

**Non-Goals:**

- No change to `Rel`, `Codec`, the combinators, `encode`, or any existing theorem
  statement. No new semantics; no `[Classical.choice]`; no `HashMap`/FFI dependency that
  would break the proof style.
- This is **not** an Earley/CYK chart over arbitrary ambiguous grammars (that is the
  genuinely-hard, possibly-out-of-reach-for-`simp` tier; see Decisions/Open Questions).

## Decisions

1. **Tier the work. Ship the provable tier first; chart the hard tier separately.**
   - **Tier A (provable, this change):** a *single-pass, fused* repetition decoder — the
     "many" decoder restricted to its **full-consumption** reading (`Option (List α)`),
     plus a `decodeRepeat`-shaped *builder* that appends into an accumulator (list fusion)
     instead of `map`-per-step — and a `decode` that uses `flatMap`-fusion. Each is proved
     equal to the spec by `List` equations (`flatMap`/`append`/`map` associativity), the
     same machinery the core already relies on. This removes the Θ(n²) all-prefix
     allocation in the common (deterministic-prefix) case and the per-branch re-traversal.
   - **Tier B (deferred, separate change):** a true memoizing/chart (DP over positions)
     decoder for ambiguous grammars. It needs a numbering of `(sub-description, position)`
     and a proof that the chart equals the denotation — likely beyond `rfl`/`simp` and may
     need a different proof strategy. Keep it out of this change so Tier A land clean.
   - **Rationale:** a provable ~10× or better win on the benchmark is achievable with
     fusion + full-consumption specialization; the chart is a research-grade proof not
     needed to close §4.4's *practical* gap for the deterministic core.
1. **Equality is denotational, not definitional.** `decodeFull p h s : Option (List α)`
   satisfies `decodeFull p h s = some xs ↔ decodeRepeat p h s` with `[]` remainder (or
   `∀ r, decodeRepeat p h s` contains `(xs, r)`). Prove it by induction on `s.length`
   (the same `ConsumesByte` guard), reusing `decodeRepeat_eq`. This keeps the new function
   *total* and *proved*, not a `partial`/opaque value (the §9 lesson).
1. **Use `WellFounded.fix` on `s.length`, not `termination_by`.** Same as `decodeRepeat`
   (§ change note: `termination_by` defs are `[irreducible]` and their recursion equation
   must be `WellFounded.fix_eq`, which is what the core already does) — write an explicit
   `WellFounded.fix` so the equality law closes by `WellFounded.fix_eq` + `List` lemmas.
1. **Add the benchmark leg to `Bench.lean`** (`decodeFull`/`decodeRepeatFull` vs the §10.5
   baseline) so the speedup is *recorded*, reusing the existing `nix build .#bench`.

**Alternatives considered:**

- *Memoization via a `HashMap` keyed by `(d, s)`* — rejected: `Codec` is a structural
  value (no cheap nominal identity), `Std.HashMap` brings `BEq`/`Hashable` obligations and
  an FFI-backed structure that breaks the `rfl`/`simp` proof style, and the equality proof
  against the spec becomes a hash-consistency argument far harder than Tier A's `List` laws.
- *Changing `decode` to committed choice / single result* — rejected outright (decision #2
  in `AGENTS.md`; the backtracking union is semantic, not an efficiency knob).
- *Moving to a lazy/`Thunk` stream carrier* — rejected for this change (§ change note: a
  strict `List` cannot hold infinite results; a lazy carrier is a different, larger design
  and does not by itself fix the all-prefixes Θ(n²) for a *finite* full-consumption ask).

## Risks / Trade-offs

- *[Full-consumption specialization is not the general ambiguous case]* → The equality law
  is stated only for the full-consumption reading; general (partial-prefix) `decodeRepeat`
  remains the spec and is untouched. Document the boundary; do not claim general ambiguity
  is solved.
- *\[`simp`/`rfl` may not close the fusion equality\]* → Use explicit `List` equations
  (`List.flatMap_assoc`, `List.map_append`, etc.) and `WellFounded.fix_eq`, matching the
  core's existing tactics; if a step stalls, fall back to a `decodeFull_spec`-style law
  proved by induction rather than by unfolding.
- *[The speedup may under-deliver on the quadratic "many"]* → Even removing the all-prefix
  allocation is an asymptotic win for the full-consumption ask (Θ(n) space, not Θ(n²)); if
  the chart (Tier B) is needed for arbitrary ask, that is a separate change.

## Migration Plan

Additive only: new interpreters + their equality lemmas land beside the spec; `Bench.lean`
gains a comparing leg. No existing symbol changes signature. Rollback = revert the new
module + bench leg (nothing else depends on the new names until downstream adopts them).

## Open Questions

- Whether Tier B (memoizing chart) is even attempted in this repo, or left as downstream
  research in `lean-binary`. It does not affect Tier A's scope or task breakdown.
