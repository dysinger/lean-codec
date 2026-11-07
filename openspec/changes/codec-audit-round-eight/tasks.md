# Tasks — `codec-audit-round-eight`

**Direction.** Work top-down. Every task here adds a **reporting** obligation, and every
one must be mutation-tested before it is believed — that is the lesson this file has
paid for three times (round five's classifier dropped `Iso.prod`; round seven's
predicate removed 139 declarations; round eight's attribution rule skipped two live
claims, one of which was a false footprint claim).

**Starting state:** `./lean-codec` @ `aaa5dbb`, tree clean, `lake build` green with
**eight** gate lines — `425 = 347 + 78` theorems, `140 = 115 + 25` defs, **146**
footprint claim sites, 4 bare projections.

**Already fixed this round — do not re-report:** R8-03 attribution (claim sites
145→146), `Codec.Bytes.ext_iff` → `[Quot.sound]`-only, `Bench.lean`'s `4.3 µs` note,
`README`'s RFC `MUST`, three run-vintage stamps. **Refuted: R8-01** (`filter ||` is not
broken — the predicate is true for every element) and **M-2** (`86→106` is internally
consistent; the reviewer re-timed on another box).

## 1. The universe is undefined for two of seven `ConstantInfo` constructors

- [ ] 1.1 Count `opaqueInfo` and `axiomInfo` in `Codec`/`Iso` and **print the count**,
      so "zero" is a measurement. Measured at write time: `opaque = 0, axiom = 0`.
      Print it in the header arm's `logInfo` beside the theorem/def counts.
- [ ] 1.2 Decide and record: are `opaque`/`axiom` **in** the gated universe (and so
      footprint-checkable via `collectAxioms`, which handles a bodyless constant) or
      **deliberately out**? Either way, correct the header's claim that the universe is
      "every constant in the `Codec` or `Iso` namespace" — as written it is false.
- [ ] 1.3 Note the interaction that made this a hole: `exclusions` **rejects** an
      `opaque` (`it is not a public theorem`), so an exclusion could not cover one even
      if it leaked `Classical.choice`.
- [ ] 1.4 Mutate: add a scratch `opaque` to a `/tmp` probe in the namespace and
      confirm the new count changes. (Not in the tree — this is a probe, not a law.)

## 2. `propProjections` asserts nothing about its entries

- [ ] 2.1 Add the missing validity arm: every name in `propProjections` must satisfy the
      same `isBareProj` predicate the completeness arm uses. One `run_cmd` clause; it
      makes the docstring's _"a name here that is not actually a structure-field
      projection would fail"_ true.
- [ ] 2.2 Correct the same docstring's _"the same kind of data as `derivedDefPatterns`"_
      claim if 2.1 lands — with the arm it becomes true; without it, say what is checked.
- [ ] 2.3 **Mutation:** add a genuine theorem that is _not_ a projection
      (`Codec.bytesToArray_size`) to `propProjections` and require 2.1 to fail naming it.
- [ ] 2.4 Record the refuted escalation: the reviewer claimed adding
      `Codec.roundtrip` to `propProjections` makes it invisible to every arm. Measured:
      the "in NEITHER" and header arms both fired. The narrow true statement is 2.1.

## 3. Allowlist reasons: measurement or classification

- [ ] 3.1 `Codec.brecOn.eq` — rewrite the reason. It is the compiled-body equation of
      `def Codec.brecOn`, not _"the only authorial theorem … ending in `eq`"_
      (measured with `#check`). Drop "Measured:" if nothing was measured.
- [ ] 3.2 The 41 `sizeOf_spec` / `congr_simp` / `eq_def` entries: their shared reason is
      a **content** claim (_"each restates its own definition"_) with no body evidence
      recorded, while the file's own doctrine forbids reading an empty footprint as a
      restatement. Either record a `#print`-the-body sample and label it a sample, or
      downgrade the reason to "classified by name, audited only for existence".
- [ ] 3.3 `congr_simp` specifically: it is the one suffix in the list that could be a
      real congruence law. `#print` one and record what it is.
- [ ] 3.4 Keep this honest in the register: a reader must be able to tell a measured
      exemption from a name-based one without leaving the comment.

## 4. An unsourced cell

- [ ] 4.1 Drop `README`'s `decodeFullArrayRoot` **cold** `49 ns/step` cell (and its
      restatement at the later paragraph), replacing it with a pointer to the lane that
      prints it — the treatment `arrayRead` and `decodeArray step` already had.
- [ ] 4.2 State why: every committed per-step value for that function is 26.98–28.56,
      the caption says all cold cells are one session, and `49` is 1.72× the largest.
      **Do not re-run the lane** — the fix is to drop an unsourced number, not to
      produce a new one.

## 5. The footprint count needs a denominator

- [ ] 5.1 Print both figures: how many claim sites were checked **and** how many
      docstrings mention any footprint spelling. A narrowing of the vocabulary or the
      predicate is then visible in the log, which is how the round-seven predicate bug
      would have been caught.
- [ ] 5.2 **Mutation:** narrow the vocabulary (drop `-free`) and confirm the denominator
      changes while the checked count drops — i.e. the log distinguishes "fewer claims
      exist" from "fewer claims are read".

## 6. Remaining SHOULD/NITPICK from `/tmp/r8-*.md`

- [ ] 6.1 Read `/tmp/r8-paper.md`'s SHOULD section and fix or record each item. Its one
      MUST is done.
- [ ] 6.2 Read `/tmp/r8-gates.md` §SHOULD items R8-04 … R8-09 not covered above
      (the paragraph-window lookup at `Axioms.lean:1539`, the inert `!ci.isPartial`
      filter, the `codec/axiom-gate` scenario count) and fix or record each.
- [ ] 6.3 Read `/tmp/r8-numbers.md`'s six SHOULDs and seven NITPICKs; fix or record.
      Note its reproductions of the _passing_ figures are evidence worth keeping in the
      ledger, so a future round does not re-derive them.

## 7. Gates

- [ ] 7.1 `nix fmt`, `lake build` (every gate line, counts in lockstep), `lake build
    bench`, `openspec validate --all`, `nix flake check` (detached with `nohup`).
- [ ] 7.2 Regenerate `Axioms.lean` if any law moved; the header table and the
      `expected*` constants move **together**.
- [ ] 7.3 Commit per task family, individual files, printing
      `git diff --cached --name-only`; push; bump `lean-basen`'s pin **only** if
      `codec` changed (it will, so: bump, re-run its three gates, push).

## 8. Recorded, deliberately not in this change

- **A ninth review round.** This carries round eight's remainder; it does not
  commission more.
- **`basen`'s two parked changes** (`basen-uppercase-prepass`, `basen-nat-iso`) — the
  owner has deferred both pending the library division.
- **The `Float`/`Rat` question** — recorded in `basen-nat-iso`'s §6; `Float` is not an
  `Iso` (measured: `toString (1/3) = "0.333333"`), `Rat` can be (reduced fractions),
  fixed-point is the integer case shifted.
