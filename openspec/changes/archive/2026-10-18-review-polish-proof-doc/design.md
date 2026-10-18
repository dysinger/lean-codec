# Design

## Context

The proven core (`Iso`/`Codec`/`Decode`/`Encode`/`Sound`/`Combinators` +
`Packed`/`ByteSlice`/`DecodeOne`) is `[propext, Quot.sound]`-only, zero `sorry`.
Three defects surfaced by an independent review, none of which are soundness bugs
in the proven laws but which are documentation-vs-proof mismatches and one genuine
outstanding proof gap. The README rewrite (citation/precision, Layer-2 framing,
honest ceiling) is already complete and committed; this change is only the
code/proof half.

## Goals / Non-Goals

**Goals:**

1. Make `decodeArray_bounded`'s docstring truthful (or prove and state the missing
   upper bound).
2. Prove `decodeArray_unambiguous_value`, and align `DecodeOne.lean`'s module
   header with what is actually proved vs still-assumed.
3. Reconcile the Layer-2 seam boundary conditions so the C `memcpy`/`memchr` and
   the Lean `Array.extract`/`findIdx?` body are checked for agreement on the
   out-of-range cases, not merely asserted.

**Non-Goals:**

- Any change to the public denotation or the laws (`decode_spec`, `bidir`,
  `roundtrip` stay byte-identical).
- New C, new package extraction, or format code.
- Making the pure interpreter fast (the ~20–40×-off-C ceiling is accepted).

## Decisions

1. **`decodeArray_bounded`:** prefer **proving and stating the upper bound** `c ≤ a.size`
   rather than only rewording the docstring, because the upper bound is the real
   "never overruns" guarantee the docstring promises and it holds from `consumedAbs`
   - `Suffix.hle`. If that proof turns out to drag in a `Suffix` roundtrip that's
     not worth it, fall back to renaming/rewording to the `i ≤ c` monotonicity fact.

2. **`decodeArray_unambiguous_value`:** the forward bridge is
   `(x, c) ∈ decodeArray d a i → Rel d x s₀` for the genuine consumed prefix `s₀`,
   obtained from `decodeArray_eq` + `decode_spec`; the same consumed count then pins
   the two `s₀`s equal (as the same-length prefix of the same input) before
   `Unambiguous d` forces the values equal. The remaining primitive is a
   `splice`/`prepend` prefix-extraction lemma (`splice hm s₁ s₂ ⟨i, ·⟩ = s₁ ⟨i, ·⟩`
   for `i < m`), seeded earlier as `splice_prefix_read`. No `sorry`/`axiom` ships:
   either it closes `[propext, Quot.sound]`-only or stays explicitly documented as
   open. `DecodeOne.lean` header wording is corrected regardless.

3. **Layer-2 boundary contract:** spell out, clause-by-clause, what the Lean body
   does for `off ≥ size` and `off + len ≥ size` (does `Array.extract` clamp the stop
   index, truncate, or is it undefined?), and make the C (which currently clamps via
   explicit `if dstOff > n`/`if srcOff > slen`) assert the _identical_ clause. If the
   two cannot be shown to agree by inspection, add a `#eval`/bench smoke test over
   the boundary cases (empty source, `off` at/ past end, `len` past end) so the
   "matches byte-for-byte on every input" claim is checkable rather than asserted.

## Risks / Trade-offs

- **`decodeArray_unambiguous_value` may be genuinely hard** (it is the one
  outstanding proof gap the earlier sessions ran out of room on). Risk: this change
  ships the docstring/header corrections and leaves the lemma open _if_ the
  prefix-extraction transport needs more lemmas than fits here; the gate
  ("zero `sorry`") is preserved either way.
- **`Array.extract` boundary semantics are stdlib-defined and may not match the C's
  chosen clamping** on an edge case; the fix is to make the contract explicit, which
  could reveal the C needs a one-line clamp adjustment. That is a correctness fix to
  the trust seam (Layer 2), not a proven-law change.
- No law/spec changes, so `skip_specs: true` stays correct.
