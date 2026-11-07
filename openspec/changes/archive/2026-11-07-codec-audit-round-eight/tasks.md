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

- [x] 1.1 Count `opaqueInfo` and `axiomInfo` in `Codec`/`Iso` and **print the count**,
      so "zero" is a measurement. Measured at write time: `opaque = 0, axiom = 0`.
      Print it in the header arm's `logInfo` beside the theorem/def counts. **DONE:** the `constantKindCensus` arm prints
      `constant kinds — thm 769 (gated + allowlisted), def 348 (mention proxy),
opaque 0 / axiom 0 (no arm, must be 0), induct/ctor/rec/quot 30 (machinery, not
walked)` — every kind, so the denominator of the walk is in the log, and the two
      unwalked law-shaped kinds are **asserted** zero (`constantKindExceptions`), not
      merely printed. Measured 2026-11-07: `opaqueInfo 0`, `axiomInfo 0`, and the
      seven-constructor census is `thm 769 / def 348 / ctor 14 / induct 8 / rec 8 /
quot 0`.
- [x] 1.2 Decide and record: are `opaque`/`axiom` **in** the gated universe (and so
      footprint-checkable via `collectAxioms`, which handles a bodyless constant) or
      **deliberately out**? Either way, correct the header's claim that the universe is
      "every constant in the `Codec` or `Iso` namespace" — as written it is false. **DONE — decision: deliberately OUT.** Neither has a proof
      body, so neither _can_ be footprint-checked; `collectAxioms` on an `opaque` asks
      about its value, which is not what this gate asks of a law. The header's false
      sentence is replaced by a **measured table** of all seven constructors with the
      in/out decision and today's count, and by the statement that the count is the
      mechanism. Note the census **throws** on a non-zero `opaque`/`axiom` rather than
      tolerating it: an authored `opaque` is law-shaped and invisible to every arm, so
      the tripwire forces the conversation rather than letting it slip in.
- [x] 1.3 Note the interaction that made this a hole: `exclusions` **rejects** an
      `opaque` (`it is not a public theorem`), so an exclusion could not cover one even
      if it leaked `Classical.choice`. **DONE:** recorded in the header table's
      paragraph ("the previous defence was worse than silence — `exclusions` refuses an
      `opaque` outright, so an exclusion could not cover one even if it leaked
      `Classical.choice`") and in the census arm's docstring.
- [x] 1.4 Mutate: add a scratch `opaque` to a `/tmp` probe in the namespace and
      confirm the new count changes. (Not in the tree — this is a probe, not a law.) **DONE — measured.** A `/tmp` probe
      run through `lake env lean` prints `opaqueInfo: 0` on the clean tree and
      `opaqueInfo: 1` with `namespace Codec / opaque scratchThing : Nat := 42`.
      (_Through the census's own predicate, not by planting one in `Axioms.lean`_: a
      `run_cmd` sees only declarations that precede it — measured with a `getEnv` probe
      — so planting one here would have to live above eight arms and would change the
      counts they pin. The **failure branch** was mutated directly instead: setting
      `constantKindExceptions`' `opaque` entry to `3` fails the build naming the
      mismatch — recorded below in §7.1's mutation list.)

## 2. `propProjections` asserts nothing about its entries

- [x] 2.1 Add the missing validity arm: every name in `propProjections` must satisfy the
      same `isBareProj` predicate the completeness arm uses. One `run_cmd` clause; it
      makes the docstring's _"a name here that is not actually a structure-field
      projection would fail"_ true. **DONE:** a second arm whose
      predicate is _the same `isBareProj` definition_, so the two directions cannot
      drift. It checks each listed name for: existence, `thmInfo`-ness, and bare
      projection-ness, and prints `4 listed of 7 bare projections in the namespaces;
the rest are the `dec`-suffixed three, classified by suffix`.
- [x] 2.2 Correct the same docstring's _"the same kind of data as `derivedDefPatterns`"_
      claim if 2.1 lands — with the arm it becomes true; without it, say what is checked. **DONE — it becomes TRUE and the docstring now
      says how:** "Two directions, two arms … The _completeness_ arm has existed since
      `codec-audit-round-seven` GC-04. The _validity_ arm was only added in round eight,
      and until then the sentence above was a claim about a mechanism that did not
      exist."
- [x] 2.3 **Mutation:** add a genuine theorem that is _not_ a projection
      (`Codec.bytesToArray_size`) to `propProjections` and require 2.1 to fail naming it. **DONE — measured:** adding `Codec.bytesToArray_size`
      fails the build with `Codec.bytesToArray_size: its body is not a bare
structure-field projection — listing it REMOVES a real theorem from the gated
universe` (and the "pinned names with no matching theorem" arm fires too). This
      is the file's one live mutation on the record; §1's is a value probe.
- [x] 2.4 Record the refuted escalation: the reviewer claimed adding
      `Codec.roundtrip` to `propProjections` makes it invisible to every arm. Measured:
      the "in NEITHER" and header arms both fired. The narrow true statement is 2.1. **DONE — recorded in the arm's docstring
      verbatim**, plus the wider finding R8-09 asked for: `isBareProj` also **misses** a
      _wrapped_ projection (`fun self => id self.law`). Measured: **zero such theorems
      exist** (a walk for projections under `id`/parentheses finds none; the 19 theorems
      whose bodies _contain_ a projection without being one are `eq_def`/`eq` machinery
      plus `Codec.decodeFull_some`, whose projection is on a destructed pair). Latent,
      stated, deliberately not fixed — tightening `isBareProj` changes the
      _completeness_ arm's definition of "is a projection", which is a different
      decision.

## 3. Allowlist reasons: measurement or classification

- [x] 3.1 `Codec.brecOn.eq` — rewrite the reason. It is the compiled-body equation of
      `def Codec.brecOn`, not _"the only authorial theorem … ending in `eq`"_
      (measured with `#check`). Drop "Measured:" if nothing was measured. **DONE:** rewritten. Measured with
      `#check`/`#print`: type is `brecOn motive t F = F _ t (brecOn.go … ).2`, body is
      the `casesOn` machinery. It _is_ also the only `Codec`/`Iso` name ending in `eq`
      (re-walked: `[Codec.brecOn.eq]`) — both sentences are true, but only the second is
      a _reason_; the docstring now says exactly that.
- [x] 3.2 The 41 `sizeOf_spec` / `congr_simp` / `eq_def` entries: their shared reason is
      a **content** claim (_"each restates its own definition"_) with no body evidence
      recorded, while the file's own doctrine forbids reading an empty footprint as a
      restatement. Either record a `#print`-the-body sample and label it a sample, or
      downgrade the reason to "classified by name, audited only for existence". **DONE — both, per group.** `inj`/`injEq`/`sizeOf_spec`/`eq_def`
      are now labelled **classified by name, machine-checked only for existence and for
      being dropped from the universe**, and the withdrawn content claim is named as
      withdrawn. `congr_simp` is **measured by sample** (4 of 16 `#print`ed).
      `sizeOf_spec` records its one sample (`Codec.Normal.mk.sizeOf_spec`) and says it is
      a sample. The group docstring now opens with a register paragraph telling a reader
      **which two groups carry a measurement and which two are name-based**, which is
      3.4.
- [x] 3.3 `congr_simp` specifically: it is the one suffix in the list that could be a
      real congruence law. `#print` one and record what it is. **DONE — and the reviewer's suspicion is REFUTED.**
      `#print`ed, `Codec.decodeFull.congr_simp` is
      `∀ …, s = s₁ → decodeFull p h n s = decodeFull p₁ (cast h) n s₁` — **argument
      transport**, the shape `simp` needs to analyse recursion through a changing
      argument. A congruence law _constructs_ an equality from a hypothesis; these
      _transport_ one through positions `simp` cannot see. Sample of four
      (`decodeFull`, `fill`, `Iso.foldl`, `Normal.mk`), and labelled a sample.
- [x] 3.4 Keep this honest in the register: a reader must be able to tell a measured
      exemption from a name-based one without leaving the comment. **DONE:** `generatedAuxAllowlist`'s docstring now opens with
      "**Read the next sentence before trusting any reason below.** Only _two_ of these
      four groups carry a **measurement**; the other two are **classifications by name**,
      and the register says which is which" — and each group states its own basis
      (construction / structural arm / sample / measured) in its first line.

## 4. An unsourced cell

- [x] 4.1 Drop `README`'s `decodeFullArrayRoot` **cold** `49 ns/step` cell (and its
      restatement at the later paragraph), replacing it with a pointer to the lane that
      prints it — the treatment `arrayRead` and `decodeArray step` already had. **DONE:** the cell is `see note`, with a paragraph
      explaining it, and the later restatement is replaced by a pointer to
      `benchRatio "decodeFullArray"` and a statement that it answers a _throughput_
      question, not the compute floor. The "Two rows carry no `ns/step` figure" note is
      now **three** and names this one.
- [x] 4.2 State why: every committed per-step value for that function is 26.98–28.56,
      the caption says all cold cells are one session, and `49` is 1.72× the largest.
      **Do not re-run the lane** — the fix is to drop an unsourced number, not to
      produce a new one. **DONE — stated in the README in those terms, and the
      lane was not re-run.** Every committed per-step value for `decodeFullArrayRoot` in
      the document lies in 26.98–28.56; the caption says all cold cells are one session;
      49 is 1.72× 28.56. Also `grep`ed the tree for other restatements of the figure —
      the one at the later paragraph was the only survivor and is now a pointer.

## 5. The footprint count needs a denominator

- [x] 5.1 Print both figures: how many claim sites were checked **and** how many
      docstrings mention any footprint spelling. A narrowing of the vocabulary or the
      predicate is then visible in the log, which is how the round-seven predicate bug
      would have been caught. **DONE — and it prints three,** because two is not enough to
      separate the questions: `769 theorem docstrings scanned, 144 mention a footprint
spelling; 154 claim site(s) found, 146 attributed to self and checked, 8
attributed away or in a `def` docstring (out of scope)`. `scanned` catches a
      narrowed **walk**, `mentioning` a narrowed **vocabulary**, and the checked/left
      split the arm's own removal step. The vocabulary itself is now data
      (`footprintClaimPhrases`) read by **both** the classifier and the denominator, so
      they cannot drift. Honest note: the first run of the skipped counter printed
      **253**, because the attribution test ran before the vocabulary test and counted
      ordinary sentences; a guard fixes that, and the corrected number (8) reconciles
      with 154 − 146.
- [x] 5.2 **Mutation:** narrow the vocabulary (drop `-free`) and confirm the denominator
      changes while the checked count drops — i.e. the log distinguishes "fewer claims
      exist" from "fewer claims are read". *_DONE — measured, and the result was *not* what the task
      expected_: dropping the `-free` phrase from the vocabulary moved **`mentioning` 144
      → 140** while **`claims` stayed 146**. That is correct, not a bug: the `"-free"`
      entry is reached only through `"axiom-free"`, and the segments it removes are
      exactly the ones whose claims are attributed _away_ (`namesSelf` / `namesOther`
      run before the vocabulary test), so removing the spelling removes 4 docstrings
      from the denominator and 0 checked sites. Narrowing the **walk** instead
      (`Iso` dropped from the prefix test) moved `scanned` 769 → 702. Two different
      narrowings, two different counters — which is what the task wanted the log to
      distinguish; the task's assumption that both would drop is the part that was
      wrong, and it is recorded rather than smoothed over.

## 6. Remaining SHOULD/NITPICK from `/tmp/r8-*.md`

- [x] 6.1 Read `/tmp/r8-paper.md`'s SHOULD section and fix or record each item. Its one
      MUST is done. **DONE — all five fixed, each verified against the tree
      before editing.** S-1 `satisfy`'s declaration site is `Codec/Codec.lean` and
      `Combinators.lean` holds only its _use_; S-2 "factored once" is true of the
      `unapply` direction only (`foldApply`/`foldrApply` are separate); S-3 `CHANGELOG`
      attributed `findByte_spec`'s clean footprint to the _replaced_ `Array.findIdx?`
      body — rewritten against `findFrom`, with the historical body named as historical;
      S-4 the `[D4]` premise is generic (`Normal (S) (norm : S → S)`) and length
      preservation is the `Bytes n` _instance_; S-5 the unconditional-iso list is not
      footprint-uniform (`Iso.inverse` is axiom-free, the other twelve `[propext]`).
- [x] 6.2 Read `/tmp/r8-gates.md` §SHOULD items R8-04 … R8-09 not covered above
      (the paragraph-window lookup at `Axioms.lean:1539`, the inert `!ci.isPartial`
      filter, the `codec/axiom-gate` scenario count) and fix or record each. **DONE.** **R8-04** fixed: paragraphs are
      now located by **offset** (a running cursor over `doc` plus a `(start, span)`
      table), not by `String.contains` — which returned the _first_ paragraph for an
      empty fragment and for a fragment occurring twice. **R8-05** fixed: the filters
      moved _into_ the `thmInfo` arm and the inert `!ci.isPartial` (always `false` for a
      theorem) is **deleted** rather than left reading as a guard. **R8-06** fixed:
      154/146/8 printed, and all three **asserted** (`expectedFootprintCounts`).
      **R8-08 fixed as a correction:** the round-seven narrative wrongly credited
      `Codec.Bytes.ext_iff`'s miss to the `getPrefix` narrowing — that theorem's
      `getPrefix` _is_ `Codec`, so the prefix filter never removed it; the
      **attribution** rule hid it. Comment corrected; the prefix narrowing's own
      casualty count is recorded as still unmeasured. **R8-09** (i) done as 2.1; (iii)
      done as both counts printed; (ii) the "wrapped projection" hole is **measured
      latent** (zero live) and recorded in the arm's docstring rather than fixed, because
      tightening `isBareProj` changes the _completeness_ arm's semantics. **The
      `codec/axiom-gate` scenario-count sub-item: refuted** — `openspec validate --all`
      reports 13/13 passed, 0 failed, with no scenario-count error.
- [x] 6.3 Read `/tmp/r8-numbers.md`'s six SHOULDs and seven NITPICKs; fix or record.
      Note its reproductions of the _passing_ figures are evidence worth keeping in the
      ledger, so a future round does not re-derive them. **DONE — 5 of 6 SHOULDs fixed, 1 recorded as already-correct; 5 of 7
      NITPICKs fixed/none-needed, 2 recorded as refuted.**
      SHOULD: **S-1** fixed (the `~12` yardstick is the _withdrawn_ 700×-inversion
      figure; now `~64–67 ns per call`); **S-2** fixed (README `~2.6–2.7` and AGENTS
      `~2.5–2.6` were two intervals neither containing the other's end — both now
      `~2.5–2.7`, which contains all six committed floors 2.456–2.674); **S-3** fixed
      (`~0.045` vs the table's `~0.03` — keep one, `~0.03 = ~125 ns/4 KiB`); **S-4**
      fixed (no lane reads load — the claim is now "recorded by hand beside each
      result", with the lane's actual behaviour stated); **S-5** fixed (`eight
performance figures` recounted: **four distinct quantities across fourteen
      recorded values** — no reading reached eight; the recounted form is now in
      `AGENTS.md`); **S-6** fixed (`"prod"` called a _suffix_ entry — it is a
      last-name-**component** pattern).
      NITPICK: **N-1** — no defect (ordinals correct but abbreviated), recorded here so
      it is not re-derived; **N-2** comment added to the completeness arm (the
      `isGeneratedAux` exemption is audited by `partition`, not there); **N-3** fixed
      (`Axioms.lean` read "three dead suffix entries" then listed four); **N-4** fixed
      (the paragraph forbidding withdrawn figures no longer reproduces their values);
      **N-5** fixed (the `packedCands` burst row is the 8-buffer variant and now says so,
      with the `(burst@8buf)` comparison named); **N-6** fixed (`expectedFootprintCounts`
      asserts claims/mentioning/left — mutation-tested by setting 145 against the real
      146); **N-7 REFUTED** — `lake build` really does print "Build completed
      successfully (15 jobs)" (read off this session's run, three times), so `AGENTS`'
      "15 jobs" is not underivable; the module-count suggestion is unnecessary.
      **Passing figures reproduced this session, kept so a later round need not re-derive
      them:** the eighth gate line's predecessor counts (`425 = 347 + 78`,
      `140 = 115 + 25`, `4` bare projections), `#print axioms Codec.findByte_spec →
[propext]`, `#print axioms Codec.findFrom → [propext]`, the constant-kind census probe's own output
      (`thm 769 / def 348 / ctor 14 / induct 8 / rec 8 / quot 0`), the bare-projection
      walk (`7` in the namespaces, `4` listed, `3` `dec`-suffixed), and the 19
      contain-but-are-not projections.

## 7. Gates

- [x] 7.1 `nix fmt`, `lake build` (every gate line, counts in lockstep), `lake build
bench`, `openspec validate --all`, `nix flake check` (detached with `nohup`).
      **DONE, all five, same session — but with one correction that changes what a
      clean `nix fmt` run means in this repo.** `nix fmt` in this dev shell has **no
      prettier**: it formats `*.nix` only and prints "0 changed" for markdown it never
      touched. So every clean `nix fmt` in this file's history (and in the archives)
      covered Lean and Nix and **not markdown**. The real markdown gate is the flake formatter
      (`nix build .#formatter.…` → treefmt with the sandboxed prettier, cached per
      tree — `--clear-cache` after an out-of-band edit). That is what caught the
      archived round-six ledger (`185eebd`), a **pre-existing** red this change did not
      cause and could not see while the tree was dirty.
      `lake build`: **10** gate lines — `425 = 347 + 78` theorems, `140 = 115 + 25` defs,
      `12` def-name patterns, `54` definitions dropped, constant kinds
      `769 / 348 / 0 / 0 / 30`, footprints
      `769 scanned / 144 mentioning / 154 found / 146 checked / 8 left`, projections
      `4 listed` and `4 listed of 7 found`. Every printed count agrees with the constant
      that asserts it — no `expected*` was stale. `lake build bench`: 28 jobs, links
      `CRef.o`. `openspec validate --all`: **13 passed, 0 failed**. `nix flake check`
      (detached): `treefmt-check` initially failed **on this very file** (the ticked text
      was not fmt-clean — a real catch); `checks.lean` was _cancelled_ on the first run
      because it was killed at the end of that session, and **a cancelled check is not a
      pass**. It was then re-run to completion: see the closing note below.
      **Mutations run this session, and what each proved:** `constantKindExceptions`'
      `opaque` entry → `3` fails naming the mismatch (census branch live);
      `Codec.bytesToArray_size` added to `propProjections` fails naming it (validity arm
      live — 2.3); dropping `-free` moves `mentioning` 144→140 with `claims` held at 146
      (5.2); dropping `Iso` from the prefix test moves `scanned` 769→702;
      `expectedFootprintCounts` → `145` fails naming 146 (assertion live).
- [x] 7.2 Regenerate `Axioms.lean` if any law moved; the header table and the
      `expected*` constants move **together**.
      **DONE — and it found a real defect, so this task paid for itself.** No law
      moved, but running the generator anyway (the honest check: a no-op is evidence,
      an assumption is not) surfaced a **one-line drift that had un-pinned a law for a
      whole round**:

      * `scripts/gen-axioms.lean`'s `localIsGeneratedAux` carries a **mirror** of
        `CodecAxioms.propProjections` — and the mirror listed **three** names while the
        real list had **four**, `Codec.Suffix.hle` having been added by
        `codec-audit-round-seven` GC-02. So the generator emitted
        `Codec.Suffix.hle` into `gatedNames` **and never emitted its `#guard_msgs`
        block**: the file claimed 347 gated theorems and pinned **346**.
      * `headerNumbers` did not catch it because it read `gatedNames.length` — the
        *mirror's* count — so the two numbers agreed with each other while both
        disagreed with the tree. That is the round-five/seven/eight lesson for the
        **fifth** time, in a place nobody had looked: **a mirror list is a name list,
        and a name list with no completeness arm removes things silently.** The
        distribution table was the only thing that disagreed (`348 ≠ 347`), and it is
        generated, which is why it disagreed.
      * **Fix:** `Codec.Suffix.hle` added to the mirror, with the reason at the entry
        (as `propProjections` entries carry theirs), and a comment recording the drift.
        Regeneration then rewrote `347` gates: the distribution moved one law from
        `axiom-free` to `[propext]`-gated (`30 → 29`), and the header table moved with
        it. `#guard_msgs` blocks: **346 → 347**. The footprint gate now footprint-pins
        a law it had only been *naming*.
      * **Not fixed, recorded:** `headerNumbers` still derives `gated` from
        `gatedNames.length` rather than from a count of `#guard_msgs` blocks, so a
        future mirror drift can still hide. A count of `#guard_msgs` occurrences is not
        available to a `run_cmd` (it is source text, not environment), so the durable
        fix is for the generator to be run when a law is added — which `AGENTS`
        already says, and which this task is the evidence for.

- [x] 7.3 Commit per task family, individual files, printing
      `git diff --cached --name-only`; push; bump `lean-basen`'s pin **only** if
      `codec` changed (it will, so: bump, re-run its three gates, push).
      **DONE.** Three commits in `codec`, each staged file-by-file with
      `git diff --cached --name-only` printed first — `217b7e5` (Axioms +
      `gen-axioms.lean`), `0c014bf` (README/CHANGELOG/AGENTS), `14b54fa` (this ledger) —
      pushed as `841c2bb..14b54fa`. `lean-basen`: `nix flake update codec` +
      `lake update codec` to `14b54fa`, then its gates **re-run, not assumed** —
      `lake build` prints all **8** of its lines (`490 = 444 + 46` theorems,
      `137 = 122 + 15` defs, `10` def-name patterns, `native_decide 12`, **46**
      footprint claim sites) and `lake build bench` is 45 jobs; **no `BaseN` source
      changed**, as expected (the bump moved gate machinery, not the API). Committed
      `4806fb8` and pushed as `c32db88..4806fb8`.
      **`nix flake check` was re-run to completion after the final edits** — the
      earlier run was cancelled, and a cancelled check is not a pass. Result and any
      caveat are in this change's closing note below, not in a commit message.

## Closing note — state at the end of the session

**22/22. All gates green, both repos pushed, nothing half-done.**

```
lake build         10 gate lines, 425 = 347 + 78, 140 = 115 + 25,
                   154 claim sites found / 146 checked / 8 left
lake build bench   28 jobs
openspec validate  13 passed, 0 failed
nix flake check    checks.aarch64-darwin.{formatting,openspec,lean} all ✅
```

Commits, `codec`: `217b7e5` (gate code), `0c014bf` (docs), `14b54fa` (ledger),
`c00ca7f` (7.3), `185eebd` (the archived-ledger format fix). Pushed to `master`.
`lean-basen`: `4806fb8`, pin bumped to `14b54fa`, its 8 gate lines + 45-job bench
re-run on the bumped pin, pushed.

**The one thing a next session must not re-derive the wrong way:** `nix fmt` in this
dev shell has no prettier, so "`nix fmt` clean" says nothing about markdown. The
markdown gate is the flake formatter, and it caches per tree. This change spent a
build cycle learning that, and `AGENTS.md` now carries the correction.

## 8. Recorded, deliberately not in this change

- **A ninth review round.** This carries round eight's remainder; it does not
  commission more.
- **`basen`'s two parked changes** (`basen-uppercase-prepass`, `basen-nat-iso`) — the
  owner has deferred both pending the library division.
- **The `Float`/`Rat` question** — recorded in `basen-nat-iso`'s §6; `Float` is not an
  `Iso` (measured: `toString (1/3) = "0.333333"`), `Rat` can be (reduced fractions),
  fixed-point is the integer case shifted.
