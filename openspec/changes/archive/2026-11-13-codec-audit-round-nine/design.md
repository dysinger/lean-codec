# Design — `codec-audit-round-nine`

## Context

Nine findings are in `Bench.lean` and `README.md`'s performance tables, five in
`Axioms.lean`, and four in Lean docstrings (`Normal.lean` ×2, `ByteSlice.lean` ×1,
`Bench.lean` ×1). Nine of the thirteen MUSTs are _checked_ facts — measured in this
session — rather than reviewer assertions, so this design records the measurement with
each decision rather than re-deriving it in `tasks.md`.

## D0 — Why this round did not find soundness defects, and what it found instead

Rounds six and seven found mostly _false claims about the mathematics_. This round found
**no** mathematical defect: each central law family's antecedent was checked for an
inhabitant and all eight have one (reviewer B's table, reproduced below in D6).

What it found instead is three instances of one shape — **a check whose input cannot
reach the thing it claims to check**:

1. `benchBurst`'s fold guard tests `sink == 0`; the sink is a constant `7`.
2. `isBareProj` tests for `Expr.proj`; `hal.1` elaborates to `And.left hal`.
3. The footprint arm's `skipped = 8` sums two unrelated causes, and two of the eight
   are the claims that carry `decodeFull_spec`'s hypothesis chain.

This is round eight's lesson ("a check is only as good as what _enters_ it") arriving
one layer out: round eight audited what enters the **axiom gate**; nobody asked what
enters the **bench** or the **prose table**.

## D1 — The bench re-run: why (b), and what it costs

**Decision: fix the buffer, add a non-invariance assertion, and re-run every lane.**

The alternative — land the gate and mark the old medians "pre-gate" — was rejected
because a median whose guard could not detect a fold has _no evidence behind it_, and
this project has already withdrawn three performance figures on exactly that basis
(`3 ns/call`, the `430` mislabel, the `2.4` floor). Keeping the numbers with a caveat
reproduces the practice the caveat warns about.

**The mechanism, measured.** `bytesAt j` is `fun i => if i.val = 0 then j%8+1 else 1` —
all-`1` except byte 0 — and `sinkOfList` is `foldl (fun a b => a*31 + b) 7`. `31a+1` mod
256 has period **16** from seed 7, so a run of `k` ones returns the seed whenever
`k ≡ 0 (mod 16)`. Measured `sinkOfList([1]*k) = 7` for `k ∈ {16, 32, 512, 4096}`, and
every window is a 512-byte slice of that buffer. So the sink is `7` for every call index
`j`, `7 ≠ 0`, and the guard passes for an invariant loop.

**The fix, and why not the minimal one.** Adding only the `eraseDups` assertion would
make the lane _fail_ (correctly) but would not make the rows meaningful, because an
all-`1` buffer cannot produce a varying sink under a `31a+b` fold no matter how the
window slides. So the buffer itself changes to `UInt8.ofNat (i.val % 251)` (`251` prime,
so slices at `j*8` differ in multiset), **and** the assertion is added to `benchBurst`
rather than to each caller — one place, every row.

**Consequence:** every committed burst median moves, so the README's vintage stamps
move with them. `packedCands`' 8-buffer rotation is already non-invariant and its rows
are re-run too, for consistency: a table with two vintages is worse than a table
re-run.

## D2 — The `77 ns/step` cell: delete, do not re-derive

`benchDecodeFullFast` prints
`"decodeFullFast root [{n}]: value + bridge OK (unbenchmarked, see 6.1b)"` and its
docstring says twice that no timing is printed, because every in-process attempt gave an
impossible number (`0 ns/op`, then `41 ns/op`).

The `77` is traceable to a single line:
`openspec/changes/archive/2026-11-01-codec-review-remediation/tasks.md:2407`
(`| decodeFullFastRoot (control) | 76–77 | 74–75 |`), an A/B **control** column at
`n = 65536`, measured **`ns/byte`**, on **2026-11-01**. The README's caption claims its
cold cells are "from the same two-run session" (2026-11-07), and its own row for the
_faster_ packed path is `26.98–28.56`. A `77` beside a `27` is the ~2.7× the archive's
control table shows; it is not a cell of this session.

**Decision:** set the cell to `see note`, exactly as round eight did for the adjacent
`49 ns/step` row. Do **not** substitute the docstring's `~1,250–1,500 ns/byte`: that is
a per-_byte_ figure from a different harness and quoting it in an `ns/step` column is the
same category error in the other direction.

## D3 — `isBareProj`: extend to constant-headed projections

The existing test walks `.lam`, `.mdata`, `.app`, `.proj` and returns `true` on
`.proj _ _ _`. Measured `false` on `CandAligned_fst`, `CandAligned_at`,
`CandAligned_tail`, because `CandAligned` is a `def` that elaborates to a `structure`
over `Prop`, so `hal.1` is `And.left hal` — a **constant application**, not an `Expr.proj`
node.

**Decision:** accept a spine ending in `.const` whose name is in a fixed structural set
(`And.left`, `And.right`, `Iff.mp`, `Iff.mpr`, `Prod.fst`, `Prod.snd`), rather than adding
these three to `propProjections`. Adding them to the list would make the round-eight
_validity_ arm fail — and it would be right to fail, since the list's stated property is
"every listed name is a bare `.proj` body".

**Open question, deliberately deferred to implementation:** whether
`Iso.apply_eq_some_of_unapply` / `Iso.unapply_eq_some_of_apply` (both `(i.law a b).2 h`)
belong in the allowlist once the test sees them. They are the same shape, so the
principle says yes; but they are two of the six `Iso` accessors `[S1]` advertises, so
reclassifying them changes what README's `Iso` claims mean. Resolve by measurement, and if
they are reclassified, update `[S1]` in the same commit.

## D4 — `findFrom.induct`: promotion needs an accounting, not a list edit

Measured: `Codec.findFrom.induct` depends on `[propext]` — the only allowlisted name with
a non-empty footprint. Its stated reason ("it is the recursion principle, not a law") is
true and does not address the footprint.

A naive promotion to `gatedNames` would make `mentionedByGated` accept `Codec.findFrom` on
the strength of its own recursion principle — the proxy's documented vacuous-satisfaction
mode. **Decision:** promote it _and_ record the naming explicitly, so the def-coverage
arm's satisfaction for `Codec.findFrom` is attributed rather than inherited. The
`definitionSurfaceAllowlist` entry for `findFrom` therefore becomes the recorded reason,
and the new scenario "A recursion principle does not cover its own function" is what the
gate must then be able to print.

## D5 — The `authored` validity arm

`isGeneratedAux`'s exemption (`Axioms.lean:304`, `Codec.Nat.eq_irrel`) is the only path by
which a suffixed name re-enters the gated set, and it is checked in neither direction.
The round-eight fix for `propProjections` is the template: assert (a) the name exists, (b)
it is in `gatedNames`, (c) the suffix rule _would_ have removed it. (c) is the one that
self-invalidates.

## D6 — Non-vacuity, recorded so it is not re-derived

Every central law family's antecedent has a proved inhabitant in the tree (reviewer B,
reproduced not re-proved here):

| law                    | antecedent                            | inhabitant                            |
| ---------------------- | ------------------------------------- | ------------------------------------- |
| `decode_spec`, `bidir` | none                                  | unconditional                         |
| `encode_of_decode`     | `Functional d`                        | `functional_byte`                     |
| `decodeArray_unique`   | `Functional ∧ RelAligned`             | `functional_byte` + `relAligned_byte` |
| `decodeFull_spec`      | `huniq`                               | `huniq_byte`                          |
| `decodeRepeat_spec`    | `ConsumesByte p`                      | `byteConsumesByte`                    |
| `relRepeat_unique_...` | `LengthDet ∧ RelAligned ∧ productive` | the three `_byte` instances           |

**No family is true only because its antecedent is uninhabited.** This is a refutation of
reviewer B's own opening suspicion and is recorded as such.

## D7 — Archive ordering

This change modifies four requirements in `codec/axiom-gate` and **no other change is
open** against that capability (the two open changes are `basen-*`, disjoint). So no
dependency-first ordering is required. The pre-archive check is the one this repo has
needed three times: **compare the live requirement's scenario count against the delta's
before syncing.** Measured at authoring time: `+7 / -0` across the four, no live scenario
dropped. Re-run it at archive time rather than trusting this line.

## D8 — What is deliberately not in scope

- **`relRepeat`'s `nil` branch** (reviewer C's P-1). The tree is _right_; what is missing
  is a README paragraph saying the `nil` branch is `n = 0`, not the paper's `True`. That
  is a README addition, it is real, and it belongs with the other README prose in Group 2 —
  but it does not change a spec-level behaviour, so it carries no delta.
- **`Codec/CRef.c`'s `none` comment** (N-1 in the numbers report). Prose only.
- **`default.nix`/`flake.nix` describing one link object where there are two** (S-3). Real
  but trivial; folded into the `AGENTS.md` correction.
- **Instrumenting whether the committed medians were _actually_ hoisted.** Reviewer B could
  not settle this without a run; the re-benchmark in D1 settles it empirically, which is
  better than settling it by inspection.
