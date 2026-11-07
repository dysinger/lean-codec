# Proposal — `codec-audit-round-eight`

## Why

The eighth review round ran three read-only workers against `lean-codec` only
(reports `/tmp/r8-{paper,gates,numbers}.md`). It returned **9 MUST / 15 SHOULD /
18 NITPICK**. Five were fixed inline in the same session (`aaa5dbb` and the three
commits before it); this change carries **the rest**, plus the analysis that closed
the two refutations so they are not re-derived.

**Fixed already, not in scope here — do not re-report:**

| id                    | what                                                                                                                                                                                                               | commit    |
| --------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ | --------- |
| R8-03 (footprint arm) | attribution took the nearest _resolving_ token, so a claim whose sentence named `funext`/`congrFun` was attributed away and skipped. Claim sites **145 → 146**, and the newly visible site was a live false claim. | `8410189` |
| —                     | `Codec.Bytes.ext_iff` corrected: `[Quot.sound]`-only, not both axioms                                                                                                                                              | `3a5bb84` |
| M-4 (numbers)         | `Bench.lean` said "~4.3 **microseconds** per call" for a row the same block calls `430–650 ns` — a 10× contradiction in one comment                                                                                | `96a5423` |
| M-1 (paper)           | `README:250` cited RFC 4648 §8 as `MUST` while `AGENTS.md` records `MAY`                                                                                                                                           | `aaa5dbb` |
| M-5 (numbers)         | three measured tables gained run-vintage stamps                                                                                                                                                                    | `aaa5dbb` |

**Refuted, recorded so the next round does not chase them:**

- **R8-01** — "`!(a) || !(b)` evaluates as `&&` inside `List.filter` in this
  toolchain". The reviewer's own reproducer refutes it: every element of
  `[1,2,3]` genuinely satisfies `!(n==2) || !(n==1)`, so `filter` returning `[1,2,3]`
  is _correct_. Verified independently here, including on known-answer data where the
  correct result is `[3]`. **No toolchain bug.**
- **M-2** (`86 → 106` does not reproduce) — the committed figures are internally
  consistent; the reviewer re-timed on a different box (118 vs 106, 11 %), which is
  the cross-session comparison `AGENTS.md` forbids.

## What remains, and why it is worth a change rather than a patch

### 1. The gate's universe is undefined for two of seven `ConstantInfo` constructors

`publicTheorems` and `candidateDefs` both match `| .thmInfo _ | .defnInfo _`. The
header says the universe is _"every constant in the `Codec` or `Iso` namespace"_.
`opaqueInfo` and `axiomInfo` are matched by **no arm**, and `exclusions` actively
_refuses_ an `opaque` (`it is not a public theorem`). Measured today:
`opaque = 0, axiom = 0`, so this is latent — but an authored `opaque`, which is the
standard way to publish a value without a body, would be invisible to all eight arms.

### 2. The gate's own words about `propProjections` are false

`propProjections`' docstring says a name in the list _"that is not actually a
structure-field projection would fail"_, and that it is _"the same kind of data as
`derivedDefPatterns`"_, i.e. audited. Measured: it is **not** checked for validity by
any arm. All four current entries _are_ genuine projections (verified), so nothing is
wrong now — the claim about the mechanism is what is wrong, and it is the same
"name list with no completeness arm" shape round seven fixed one level down.

The reviewer's escalation ("adding `Codec.roundtrip` to `propProjections` makes it
invisible to every arm") is **refuted as stated**: the "in NEITHER" and header arms
both fired when tried. The narrow, true statement is that a _non-projection_ name
would be silently accepted by the list.

### 3. Allowlist reasons that are not measurements

78 entries. Three reason groups do not carry the weight the prose puts on them:

- **`Codec.brecOn.eq`** — the reason says _"the only authorial theorem … ending in
  `eq`"_. It is the compiled-body equation of `def Codec.brecOn`, not an authorial
  theorem. Measured by `#check`.
- **41 `sizeOf_spec` / `congr_simp` / `eq_def` entries** — reason: _"each restates its
  own definition"_. That is a claim about **content**, and no `#print`-the-body evidence
  is recorded for any of them, while the file's own doctrine forbids using an empty
  footprint as a restatement signature. `congr_simp` is the one suffix that could be a
  genuine congruence law.
- **`propProjections`' prose** — see §2.

### 4. One committed figure with no source

`README`'s `decodeFullArrayRoot` **cold** cell says `49 ns/step`. It is not derivable
from any committed row (every committed per-step value for that function lies in
26.98–28.56), and the table's caption says all cold cells come from one session. The
reviewer's _re-timing_ does not reproduce either, but the unsourced figure is a defect
independent of their bench run — it is the same shape as `arrayRead` and
`decodeArray step`, which round seven fixed by dropping the cell.

### 5. `145 claim sites` is a count with no denominator

The arm now prints how many claims it read. It does not print how many docstrings
mention a footprint at all, so a future narrowing of the vocabulary or the predicate
is invisible in the same way the predicate bug was. Cheap to fix; high value.

## Non-goals

- **No re-timing.** §4 is fixed by _dropping_ an unsourced cell, not by re-running a
  lane: the committed tables' absolute ns are from one session and the environment
  cannot reproduce them.
- **Not re-auditing.** This carries round eight's remaining findings; it does not
  commission a ninth round.
- **`basen` is out of scope.** Its two changes are parked pending the library division.

## Risk

The recurring failure in this file's history is **a check that reports nothing**:
round five's classifier dropped `Iso.prod`; round seven's predicate removed 139
declarations; round eight's attribution rule skipped two live claims. Every task here
adds a _reporting_ obligation (print the denominator, assert the list's validity, count
the unexamined constructors) rather than a silent test, and every one must be
mutation-tested before it is believed.
