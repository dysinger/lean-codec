# Tasks

Review-polish batch from the independent review of the codec library. No
spec-level behavior change (`skip_specs: true`); the README rewrite is already
committed, and this change carries the three code/proof fixes plus a comparative
F\* audit.

## 1. Truthful run-model documentation

- [x] 1.1 In `Codec/Packed.lean`, fix the `decodeArray_bounded` docstring so it
      does not claim "at most `a.size`"/"never overruns": either rewrite it to the
      proved fact (`i ≤ c`, the cursor never moves backward), or prove and state
      the upper bound `c ≤ a.size` (via `consumedAbs` + `Suffix.hle`). Verify with
      `lake build` (zero warnings) and re-read the docstring against the statement.

## 2. The `decodeOne` uniqueness proof (the genuine gap)

- [x] 2.1 Reword the `Codec/DecodeOne.lean` module header so the "committed decoder
      then equals the unique result" consequence is conditional on the
      still-unproven `decodeArray_unambiguous_value` (future/conditional tense),
      matching the existing status note. Verify the header no longer asserts an
      unproven fact.
- [x] 2.2 Prove `decodeArray_unambiguous_value` (`Unambiguous d ⇒` two
      same-`count` `decodeArray` results agree on the value): the forward bridge
      `(x, c) ∈ decodeArray d a i → Rel d x s₀` via `decodeArray_eq` +
      `decode_spec`, plus the `splice`/`prepend` prefix-extraction lemma
      (`splice hm s₁ s₂ ⟨i, ·⟩ = s₁ ⟨i, ·⟩` for `i < m`; seed `splice_prefix_read`).
      `#print axioms Codec.decodeArray_unambiguous_value` must report
      `[propext, Quot.sound]`-only, zero `sorry`/`axiom`. If it cannot close, keep
      it explicitly documented as open (no `sorry`).

## 3. Layer-2 seam boundary reconciliation

- [x] 3.1 For `byteSlice`/`blitBytes`/`findByte`, write down the out-of-range
      clamping semantics of the Lean body (`Array.extract`/`Array.findIdx?` on
      `off ≥ size`, `len` past end) and make `Codec/ByteSlice.c`'s contract
      comments assert the _identical_ semantics clause-by-clause, or add a
      `#eval`/bench equivalence smoke test over those boundary cases. Verify the
      "matches byte-for-byte on every input" claim is now checkable, not asserted.

## 4. Comparative F\* audit

- [x] 4.1 Review `../fstar-codec` (its `AUDIT.md`, `README.md`, and `src/`) for the
      gap between the paper and _our_ stated departures/strengthenings in `README.md`
      ([D1]–[D8]/[S1]–[S6]), and record how close vs how far the F\* implementation
      is relative to the Lean port. Expected finding to confirm: the F\* `codec` is
      **far more deviant** (fat `codec a` record with 8 fields, Z3-solver-discharged
      roundtrip instead of structural invertibility, `wfcv`/`rest_cond`/error-position
      additions, ASCII-only `text`, a Pulse/C-extraction layer), whereas the Lean
      port keeps the paper's `Iso`/`Rel` core and lists only the genuine byte/binary
      departures [D1]–[D8]. Deliverable: a short note (in this change's `design.md`
      or a fresh `openspec/changes/…/fstar-comparison.md`) tabulating paper-vs-Lean-vs-F\*.

## 5. Gate

- [x] 5.1 `lake build` zero `sorry`/warnings; `#print axioms Codec.roundtrip` ⇒
      `[propext, Quot.sound]`; every new law `[propext, Quot.sound]`-only.
