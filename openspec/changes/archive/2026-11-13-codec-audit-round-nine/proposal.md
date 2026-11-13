# Proposal — `codec-audit-round-nine`

## Why

The ninth review round ran three read-only workers against `lean-codec` **only** (reports
`/tmp/review-{paper-adherence,gate-coverage,numbers-build}.md`). It returned **13 MUST /
17 SHOULD / 12 NITPICK**. Unlike rounds five and six, almost every MUST was reproduced by
direct measurement before it was accepted — the round's refutation rate on MUSTs was low,
and the two findings that matter most are in code that **no previous round looked at**:

1. `benchBurst`'s fold-detector is not connected for any row it is used on.
2. The README's `77 ns/step` cell is credited to a lane that prints no timing at all.

Both are the "a check reports nothing" family round eight was named for, but neither is in
the axiom gate — round eight audited the gate, not the bench and not the prose table.

## What Changes

### Group 1 — `Bench.lean`: the burst lane's fold guard cannot fire

`benchBurst` ends each variant with `if sink == 0 then throw`. Every one-buffer row passes
`(fun _ => arrayAt 0)`, where `bytesAt` produces a buffer that is **all `1` bytes except
index 0**, and every measured window is a 512-byte slice of it. `sinkOfList` is a
`31a+b` fold mod 256, whose period from seed `7` over a run of ones is **16** — so
`sinkOfList([1]*k)` is `7` for `k = 16, 32, 512, 4096`. **The sink is `7` for every `j`,
`7 ≠ 0`, and the guard passes while the measured work is invariant.** This is the exact
shape as the withdrawn `3 ns/call`.

- **BREAKING (measurement):** the shared buffer becomes non-uniform
  (`UInt8.ofNat (i.val % 251)`) so a slice at `j*8` has a different multiset per call, and
  `benchBurst` gains a **non-invariance assertion** (`eraseDups`-style, as the `packedCands`
  lane already does) rather than the `≠ 0` test.
- Every committed burst median in README's three performance tables is **re-run and
  restamped**. The old medians are not carried forward as "probably still right": a figure
  whose guard could not see a fold has no evidence behind it.
- `benchCReference`'s value check: `| none, none => return ()` exits the whole function
  (it is not `continue`), so a `none` from the C **silently skips both timed lanes** and the
  process still exits 0. Becomes `pure ()`, and the check set gains `n = 0` and `n = 1`,
  which are the C's two real branches.

### Group 2 — README: an underivable cell and a stale-derivation cell

- **The `decodeFullFast` cold cell `77 ns/step` is deleted.** `benchDecodeFullFast` prints
  `"… value + bridge OK (unbenchmarked, see 6.1b)"` and its docstring says twice that it
  prints no timing. The `77` traces to
  `openspec/changes/archive/2026-11-01-codec-review-remediation/tasks.md:2407`, an A/B
  **control** column at `n = 65536` measured in **`ns/byte`** on **2026-11-01** — a
  cross-session, cross-`n` borrow presented as a cell of the current session's table. This
  is the same defect round eight removed one row above (`49 ns/step`), and it is the
  citation form of what `AGENTS.md` forbids.
- `~20–22×` → `~19.6–22.0×`: run 2's own value is `51.1/2.61 = 19.58`, outside the stated
  interval.
- `~2.6–3.0 ns/step` → `2.46–2.67` (the committed range; `AGENTS.md` already carries the
  corrected form and the README sentence that spawned it was not corrected).
- `2.5 vs 6.9` → the actual cells `2.46–2.57` vs `6.85–7.03`; neither `2.5` nor `6.9` is a
  cell in the table the sentence cites.
- The summary performance table gains a `steps/burst` column (`4096` / `512`), which the
  other two tables in the same section already have.

### Group 3 — `Codec/Normal.lean`: a standards misquote and a retracted confusion

- `Normal.lean:10` says "RFC 4648 §8 **requires** a Base16 decoder to accept both `6F` and
  `6f`". `Normal.lean:196` repeats it **inside quotation marks** as the standard's text:
  `(RFC 4648 §8's "a decoder MUST accept both cases")`. §8 says the opposite — "Base 16
  decoders **MAY** accept lowercase letters". `README.md:264–274` records this as fixed by
  `codec-audit-round-eight` M-1; **the README was corrected and the Lean module it cites was
  not.** No arm reads a standards claim, so nothing fired.
- `Normal.lean:196` says `decodeNormal` "has no inverse, **because `norm` is many-to-one**".
  The loss is `fill`'s identification of every spelling in one class, not `norm`'s
  many-to-one-ness — the same constancy-vs-quotient error `[D4]` spends ~40 lines
  retracting, reproduced two files away.

### Group 4 — `Codec/ByteSlice.lean`: one footprint sentence the gate contradicts

`ByteSlice.lean:223` states `#print axioms Codec.blitBytes_spec` reports
`[propext, Quot.sound]`. **Measured: it depends on no axioms**, and `Axioms.lean:2264`'s
`#guard_msgs` is the authority. Its sibling `byteSlice_spec` docstring was rewritten for
this exact reason in round eight; this one was missed and the footprint arm reported both
green (the arm reads `thmInfo` docstrings for claims it can attribute, and this claim's
attribution failed).

### Group 5 — `Axioms.lean`: four escape routes the round-eight arms do not close

- **`Codec.findFrom.induct` is allowlisted with the reason "it is the recursion principle,
  not a law" — and it has footprint `[propext]`.** It is the **only** allowlisted name with
  a non-empty footprint, so the group's implied uniformity ("not a law ⇒ axiom-free") is
  false of the list as a whole. Promoting it naively would make the def-coverage mention
  proxy accept `Codec.findFrom` on the strength of its own recursion principle, so the
  promotion must come with an explicit accounting.
- **`isGeneratedAux`'s `authored` exception** (`Axioms.lean:304`, one name,
  `Codec.Nat.eq_irrel`) is the only way a suffixed name re-enters the gated set, and it has
  **no validity arm** — exactly the gap round eight closed for `propProjections` one list
  over. A rename or an unrelated theorem ending in `eq_irrel` is accepted by every arm.
- **`isBareProj` cannot see `And.left`/`And.right`/`Iff.mp`.** `CandAligned_fst` is
  literally `fun … hal => hal.1` and `CandAligned_at` is `hal.2 i c s hc hs`; both are
  gated as laws with pinned footprints. Measured `isBareProj = false` on all three, because
  Lean elaborates `hal.1` as a **constant application** (`And.left`), not `Expr.proj`. This
  is round five §2.2 one type class over — a hypothesis projection counted as a law — and
  both the completeness arm and the validity arm are blind to the whole class.
- **The footprint arm's `skipped = 8` is one number** covering two unrelated causes: a real
  survey paragraph naming other theorems, and a docstring with **no resolvable name in the
  claim's prefix**. The two claims that carry `decodeFull_spec`'s hypothesis chain
  (`huniq_byte`, `decodeRepeat_mem_iff_general`) land in the second bucket. The arm's
  `thmInfo` filter also puts every `def` footprint claim there, including
  `Codec/ByteSlice.lean:141`'s own (`findFrom` "is `[propext]`-only").
- The `constantKindCensus` walks only the `Codec`/`Iso` namespaces, so the repo's one
  authored `opaque` (`Codec.Bench.cRefByteMany`, bench exe root) is outside the wire the
  census built. Census globally and allowlist the known names.

## Capabilities

### New Capabilities

None. Every finding here is either a violation of a requirement the live spec already
states, or a bench/prose defect that the existing `codec/axiom-gate` requirements on
measurement (`A stated measurement is a measurement, or it is a classification`, `A figure
is committed only with the run that produced it`) already cover in principle.

### Modified Capabilities

- `codec/axiom-gate`: four requirements gain scenarios closing the escape routes found here
  — a name-list validity arm for the authored exception, a structural definition of "bare
  projection" that covers `And.left`/`Iff.mp`, a decomposition of `skipped`, and a census
  whose scope is stated. These are **ADDED scenarios on existing requirements**, not
  rewrites; the delta restates each affected requirement in full so no live scenario is
  dropped (the archive hazard this repo has hit three times).

## Impact

- `Bench.lean` — `benchBurst`, `benchCReference`, the buffer generator, and every call site.
- `README.md` — three performance tables (re-run), one table column, five prose figures.
- `Codec/Normal.lean`, `Codec/ByteSlice.lean` — docstrings only.
- `Axioms.lean`, `scripts/gen-axioms.lean` — gate arms; the pinned counts move, and the
  header table must be regenerated and re-asserted in the same commit.
- `AGENTS.md`, `CHANGELOG.md` — the round's lesson, and the corrected `warningAsError`
  scope (`Bench.lean` is an exe root and sets its own flags, so the flag does **not** cover
  it — `AGENTS.md`'s "including `bench`" over-reads).
- **No `Codec` declaration's statement changes.** Every Lean edit outside `Axioms.lean` is a
  docstring, so no proof is touched and the axiom discipline is unchanged by construction.
