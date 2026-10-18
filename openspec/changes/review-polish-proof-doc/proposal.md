# Proposal

## Why

An independent review of the codec library (this session) found the README's
departures/strengthenings faithful but surfaced three **code/proof** defects that
are not yet fixed, plus it confirmed the README rewrite is complete. These defects
are exactly the kind of "review polish" that belongs in a tracked change rather
than an ad-hoc `AGENTS.md` note: the run-model docstring contradicts its own
theorem, the `decodeOne` header asserts a consequence of a still-unproven lemma,
and the Layer-2 trust-seam boundary semantics are asserted but not reconciled at
the spec level. Closing them removes the only documentation-vs-proof mismatches in
the shipped library and the one genuine outstanding proof gap.

## What Changes

- Fix the `decodeArray_bounded` docstring in `Codec/Packed.lean`: it currently
  claims the consumed count is "at most `a.size`"/the decoder "never overruns",
  but the theorem only proves the lower bound `i ≤ c`. Either rewrite the
  docstring to state what is actually proved, or prove and state the missing
  upper bound `c ≤ a.size` (it follows from `consumedAbs` + `Suffix.hle`).
- Fix the `Codec/DecodeOne.lean` module header: it states "the committed decoder
  then equals the unique result" in present tense, but that consequence depends
  on the unproven `decodeArray_unambiguous_value`. Reword to conditional/future
  tense, then **prove** `decodeArray_unambiguous_value` (`Unambiguous d ⇒` two
  same-count `decodeArray` results agree on the value) — the forward bridge
  `(x, c) ∈ decodeArray d a i → Rel d x s₀` via `decodeArray_eq` + `decode_spec`,
  plus a `splice`/`prepend` prefix-extraction lemma.
- Reconcile the Layer-2 seam boundary conditions at the spec level (not just
  "trusted C"): for `byteSlice`/`blitBytes`/`findByte`, spell out the out-of-range
  clamping semantics of the Lean body (`Array.extract`/`Array.findIdx?` on
  `off ≥ size`, `len` overflow) and make the `Codec/ByteSlice.c` contract
  documents assert the _identical_ semantics clause-by-clause, or add a `#eval`/
  bench equivalence smoke test over the out-of-range cases.

## Capabilities

### New Capabilities

_(none)_

### Modified Capabilities

_(none — pure refactor/doc/proof fixes; no observable spec-level behavior change.
`skip_specs: true` is set.)_

## Impact

- `Codec/Packed.lean` — `decodeArray_bounded` docstring (and possibly its statement).
- `Codec/DecodeOne.lean` — module-header wording + a new `decodeArray_unambiguous_value`
  theorem (and a `splice`-prefix transport lemma in `Codec/Decode.lean`/`Codec/Codec.lean`).
- `Codec/ByteSlice.lean` / `Codec/ByteSlice.c` — boundary-condition contract documentation.
- `Bench.lean` — optionally, an out-of-range equivalence smoke test for the seams.

No public denotation or law changes; `#print axioms Codec.roundtrip` must remain
`[propext, Quot.sound]`-only throughout.
