# Proposal

## Why

The backtracking decoder `Codec.decode` is the paper's proof-of-concept
"list-monad" parser: `decode (p | q) s = decode p s ++ decode q s` and unbounded
repetition `decodeRepeat p h s` enumerate **all** results. This is *semantically
necessary* (it is what makes the bidirectional law unconditional, and `decodeRepeat`
handles the empty-match `[]` prefix that a committed choice cannot), but it is the
paper's own §4.4 caveat: **exponential worst-case complexity and a space leak from
unlimited backtracking**. The §10.5 benchmark made the cost concrete — `decodeRepeat Codec.byte [16384]` ≈ 13.8 s (quadratic in output; the all-prefixes enumeration is
Θ(n²)), while the linear encode path is ~47 ms at 2 MiB. This change replaces the
naive interpreter with an efficient implementation of the **same** denotation.

## What Changes

- A **new efficient decoder** `decodeFast` (name TBD in design) over the **same**
  `Rel`/`decode` denotation: memoized / dynamic-programmed over `(description, input)`
  positions so shared sub-derivations are computed once, not re-enumerated per
  backtracking branch.
- A **new efficient repetition decoder** `decodeRepeatFast` over the **same** `relRepeat`
  denotation, addressing the Θ(n²) all-prefixes blowup when only the full-consumption
  (or a single) prefix is wanted.
- **Laws**: `decodeFast d s = decode d s`, `decodeRepeatFast p h s = decodeRepeat p h s`
  (denotational equality — the new interpreters are *proved equal* to the proven ones,
  so every existing `decode_spec`/`bdirection`/`roundtrip`/`decodeRepeat_spec` law
  transfers by rewrite, **no new semantics**).
- **No change** to `Rel`, `decode`, `encode`, the combinators, or any existing theorem
  statement. This is a pure refactor of the *interpreter's runtime*, not the language.

## Capabilities

### New Capabilities

_(None — behavior is unchanged by construction.)_

### Modified Capabilities

_(None — this change proves denotational equality to the existing interpreters, so no
spec-level requirement changes.)_

## Impact

- `Codec/Decode.lean` (added efficient interpreter + equality laws) and a new
  `Codec/DecodeFast.lean` (or similar) module; `Codec/Sound.lean` gains the transfer
  lemmas (derived by `by simp [decodeFast]` from the equalities, no new induction).
- The `Bench.lean` harness grows a `decodeFast`/`decodeRepeatFast` leg so the speedup
  is measured against the §10.5 baseline.
- No API breakage: existing names are untouched; the fast path is additive.
