# AGENTS.md

Guidance for AI coding agents working in this repository.

> ## NEXT SESSION: ONE TASK, AND ONLY THIS TASK
>
> **`huniq` for unequal-length `alt` — the one real proof obligation left in the
> whole-buffer story. No OpenSpec change; work on the tree.**
>
> **Why this and nothing else.** A three-reviewer audit of the project against
> `PAPER.md`/`README.md` established that the core is pure and proved but that
> "ready to use" was false for three reasons — no `Iso` helper, no `ConsumesByte`
> for `seq`/`iso`, no single-value decode — and **all three are now fixed with
> format-agnostic primitives only** (`Iso.ofTotal`,
> `Codec.seqConsumesByte`/`isoConsumesByte`, `decodeWholeOne`).
> **No concrete format was added to this package**, and none should be: `[S3]`
> stands, and the formats (base2/4/8/10/16/32/64) live in `../lean-basen`. A first
> attempt did add a `Codec/Examples.lean` with `u8`/`u16le`/`u16be`; it was removed
> as bleed-in from the downstream repo's territory. What is left is the fourth
> finding, and it is a theorem, not an ergonomics gap:
>
> `decodeFull_spec` takes `huniq` (at most one value list fully consumes a string).
> It is discharged **only** at `Codec.byte`, through a chain that needs
> `LengthConst` — a _constant-step-length_ relation. Every variable-length format
> (a `varint`, a text format, anything with `alt` over unequal lengths) is outside
> it. `huniq_not_derivable` already machine-checks that unambiguity + productivity
> do **not** imply `huniq`, so this is not a formality.
>
> **The task:**
>
> 1. State the honest general sufficient condition. `relRepeat_unique_same_length`
>    is indexed by list length; the counterexample (`[a]` vs `[b, b]`) is excluded
>    by the _length index_, not by `LengthDet`. So the work is a condition that
>    pins the consuming list's length without requiring constant step length —
>    the `RelAligned` direction already sketched in `Codec/Sound.lean`.
> 2. Discharge it at **one** new codec with unequal-length branches (`varint`-shaped:
>    `satisfy`-guarded `alt`), so the premise has an in-tree supplier that is not
>    `Codec.byte`. That is the same move task 2.6 made for `byte`, and it is what
>    turns "proved for literals" into "proved for a real format".
> 3. Record the outcome in `Codec/Sound.lean`'s section note and `README.md`
>    (the `[S1]`/`huniq` discussion). If the condition turns out not to be
>    statable without new hypotheses, say so and say exactly which — do not weaken
>    `decodeFull_spec`'s statement to make it go through.
>
> **Requirements:** green `lake build` + `lake build bench` (zero warnings),
> green `openspec validate --all`, individual-file commits, `#print axioms` on
> **every** new lemma must report `[propext, Quot.sound]`-only (run it; do not
> assume — the `Classical.choice` trap has bitten twice in this tree), and every
> figure you write must be a lane's literal output from that session.
>
> **Explicitly out of scope:** any new OpenSpec change; `lean-basen`; a hand-written
> C parser for `k > 1` (the `CRef` reference exists and measures ~4× at `k = 1`);
> and `utf8`, which needs a text-carrier decision, not a proof fix.
>
> **Known-open, recorded so it is not rediscovered:** `decodeOne` is a
> committed-choice decoder with no completeness theorem and no wired entry point;
> `decodeFullArray` is a documented footgun (commits to `head?`); the Layer-2
> seams are trusted-not-proven by design and are excluded from the axiom gate.

**Four hard requirements, before anything else:**

1. **Play an audible alarm every time you pause** — see
   [Pause signal](#pause-signal-mandatory) below. It is a mandate, not a nicety.
2. **This file is a pointer to the active OpenSpec change, not a second copy of
   it.** Direction for the next session is `openspec/changes/<name>/`, applied
   through `openspec instructions apply`; `AGENTS.md` says _which_ change to work
   and _how this environment works_, and nothing else. Do not restate task lists,
   measured numbers, lemma tables, or status here — that is what `tasks.md` and
   `review.md` are for, and a copy in this file is stale the moment the ledger
   moves. When a fact already lives in `openspec/`, **link to it instead of
   duplicating it**; if this file and an `openspec/` artifact disagree, the
   artifact wins and this file gets fixed.
3. **Direction lives only here and in `openspec/`.** No `HANDOFF.md`, no
   `NOTES.md`, no `*-wip.lean` scratch files, no second place a next session could
   look. If a scratch file earns its keep, land its content in the library or in
   the change's `tasks.md` and delete the file.
4. **Work lands in the repo, and every session ends with a checkpoint commit.**
   Do **not** develop proofs in `/tmp` (or any path outside the repo) and intend
   to splice later. `AGENTS.md` permits `/tmp/probe.lean` for exactly one case —
   the library does not build and you need to iterate against the built library —
   and that file is deleted the moment the build is green again. New proofs, new
   lemmas, and half-finished cases are **written into `Codec/*.lean`**, with the
   unfinished obligation marked by a `sorry` that fails `lake build` (the gate is
   the honest marker). This is not a style preference: work in `/tmp` is invisible
   to `git`, to the build gate, and to the next session, and one reboot loses it.
   End every session with a commit (individual files, per the git conventions) so
   the tree is never the only copy of anything.

**This file is forward-looking operating instructions, not a session diary.**
History — what landed when, what was reverted, what a past session measured —
belongs in `openspec/` (the task ledger) and `CHANGELOG.md`. Do not append
"session status" sections here; that practice is what made this file 536 lines
of mutually-contradicting snapshots. Keep it short and true.

**Where a session leaves its handoff: the `## Current state` block below, in
place.** Rewrite that block; do not add to it, and do not create a new
`HANDOFF.md`/`NOTES.md`/`STATUS.md` per session — a second handoff file is the
same session-diary failure in a different filename, and it silently rots the
moment `Current state` disagrees with it. The distinction that keeps this file
honest: `Current state` states _what is true now and what is next_ (always
rewritten, never appended), while _how it got there_ and _what was measured_ live
in the change's `tasks.md` and in `CHANGELOG.md`.

## Where the truth lives

**One source of truth per concern.** When two files disagree, the left column wins:

| Question                                        | Authoritative file                                |
| ----------------------------------------------- | ------------------------------------------------- |
| The `Bytes` type's definition                   | `Codec/Codec.lean:68`                             |
| What is this library, why each design choice    | `README.md` (`[D#]`/`[S#]`), `PAPER.md`           |
| **Which change to work next**                   | `openspec list --json` + `## Current state` below |
| What work is open, and how done is done         | `openspec/changes/<name>/tasks.md`                |
| The evidence behind a finding                   | `openspec/changes/<name>/review.md`               |
| What a change is _allowed_ to change            | `openspec/changes/<name>/proposal.md`             |
| The behavioural contract                        | `openspec/specs/**/spec.md`                       |
| How this environment is set up and how to build | this file                                         |

**Anything else is a summary.** If a summary and an `openspec/` artifact differ,
the artifact is correct and the summary is stale — fix the summary.

**`Bytes n` means `Fin n → UInt8`** (`Codec/Codec.lean:68`). That line is the
definition; every other document is a _record_ of it. A `Bytes` spelled without
its length index, or as `List UInt8`/`Array UInt8`/`ByteArray`, is a **defect**
in whichever doc contains it (including a changelog entry — a corrected entry can
drift again; a stated precedence cannot). The removed `List`-carrier's
`Array.extract`/`toList` transport lemmas are the `Classical.choice` source
`README.md`'s "Representations" section exists to keep out.

## Current state

**The next session's work is the boxed task at the top of this file. Everything in
this section is background for it; nothing here competes with it.**

**Do not record status here — compute it.** Two commands answer everything:

```bash
nix develop --command openspec list --json | sed -n '/^{/,$p'   # active changes + counts
nix develop --command openspec validate --all                    # spec deltas sound
```

**No OpenSpec change is open in this repo, and none is to be created for the next
session** — that session's work is the boxed task at the top of this file, done
directly on the tree. `codec-review-remediation` was archived on 2026-11-01 into
`openspec/changes/archive/2026-11-01-codec-review-remediation/`, and its
requirements are now live under `openspec/specs/codec/**` — read those for the
behavioural contract, and the archived `tasks.md` / `review.md` for how it got
there and what was measured. **Do not continue that change.**

**`lean-basen` is open and is NOT the next session's work.** Its code lives in the
sibling repo `../lean-basen` in that repo's own `nix develop`, so it touches nothing
here; its ledger is `openspec/changes/lean-basen/tasks.md` (this repo) plus its own
`tasks.md` there. It carries the MODIFIED-replaces-wholesale archive hazard (it
MODIFIES "The `basen` bases are `Codec` values"). **Leave it alone until the boxed
task is done** — then it is a separate session in a separate repo.

**No deferral remains.** The one item 5.10 left open — the `lean` skill's
~70-char bold-lead-in cap — was closed on 2026-11-02: all 60 entries now comply,
by shortening the title and moving the original wording into the entry body, so
nothing a reader would quote was lost (verified: line and bullet counts unchanged,
zero titles dropped). 5.10's deferred item is therefore done, not dropped.

**Not a deferral, and not to be "finished" later:** `huniq` is supplied for
`Codec.byte` only (`decodeFull_spec_byte`). Task 2.6 asked for exactly one concrete
instance so the premise is demonstrably satisfiable in-tree, and that is done. For
an arbitrary codec `huniq` is a hypothesis _by design_ — and for a
non-constant-length relation the un-indexed statement is simply false
(`Codec.huniq_not_derivable`). Do not reopen this as unfinished work.

**Direction lives in exactly two places: this file and `openspec/`** — no
`HANDOFF.md`, no notes file, no scratch tree. `openspec/lean-notes.md` is
_lessons, not direction_ (it is the project half of the global `lean` skill); if an
entry there ever reads like a task list, move it to the ledger.

Five facts about that change are worth stating here **only because a reader who
skips the ledger would get them wrong**, and all five are also in `tasks.md`:

- **`decodeFull_spec`'s `huniq` is now supplied at `Codec.byte`, and nowhere
  else.** `Codec.decodeFull_spec_byte` needs no hypothesis. For any **other** codec
  `huniq` remains a hypothesis and the derivation is open — do not claim it is
  discharged there. The chain itself is in `tasks.md` 2.6; do not re-derive it.
- **Run the wired surfaces, not the specification.** `decodeWhole` /
  `decodeWholeBytes` and `encodeWhole` / `encodeWholeRepeat` / `encodeWholeBytes`
  are the named entry points, each tied to `decodeFull` / `encode` /
  `encodeRepeat` by a law. `decodeFull` and `encodeRepeat` stay the specification.
  (Those laws equate them to `decodeFull`; where that carries `huniq` it is finding
  7.6, not a defect in the wiring.)
- **Read `tasks.md` 6.1b's "SESSION 9" block before touching
  `Codec/Packed.lean`** (five plan corrections), and check `#print axioms` on
  **any** new transport lemma rather than assuming — the `Classical.choice` trap
  bit twice exactly there.
- **The Layer-2 `memcpy` seam is deliberately NOT wired, for an axiom reason.**
  `commitRemainder` is ~50–75× faster than the `List` transport (measured live by
  `benchRemainderTransports`), but the connecting lemma needs
  `Array.toList_extract`, which carries `Classical.choice` here. Speed is not the
  obstacle; the gate is. Do not "fix" this by weakening to a classical proof.
- **Only `R5.1` may change a declaration _shape_** (design D9), and it must keep
  every theorem's statement, prove the new definition equal to the old, and stay
  `[propext, Quot.sound]`-only / zero-`sorry` / `#eval`-able. Nothing else may.

**History is not direction.** What landed, when, and what was measured belongs in
the change's `tasks.md` and in `CHANGELOG.md` — including for archived changes,
whose own `tasks.md` under `openspec/changes/archive/` is the reference. Do not
re-teach landed work here, and do not extend an archived change with new audit
work.

**Archive hazards, recorded where the archive step will look for them.** A
MODIFIED requirement **replaces** the whole block on archive, so: re-read
`openspec/specs/<area>/spec.md` immediately before archiving, confirm the delta's
text is a superset, and run `openspec validate --all` after **each** archive. Two
changes modifying the same requirement must archive dependency-first, with the
required order recorded in the later change's `tasks.md`. (`lean-basen` carries
the last live instance of this: it MODIFIES "The `basen` bases are `Codec`
values".)

Each verified format/protocol is its own git repo, initialized from
`lean-nix-flake-template`, prefix-dropped internally (`lean-basen` → `basen`/
`BaseN`; `lean-vbin` → `vbin`; …), depending on `codec` **by flake input + `require
codec from git` injection — never vendored**, and inheriting the single-`Bytes n`-
substrate and `[propext, Quot.sound]`-only discipline.

In `../lean-basen`, `codec` is a flake input threaded into `default.nix`, which
rewrites `require codec from git …` → a local `require codec from "./codec-src"`
path dependency, so the sandboxed `lake build` needs no network. (`lean-codec` is
public, so the `github:` input fetches anonymously — no token, no `--impure`.)

## Verification recipe

Every command below names **its own repository**. They are different flakes with
different `checks` sets — never run one tree's recipe in the other.

### In `lean-codec` (this repo)

```bash
nix develop --command lake build            # 13 jobs, zero warnings; FAILS on `sorry`
nix develop --command lake build bench      # the bench lane (links Codec/ByteSlice.c)
nix develop --command openspec validate --all   # after ANY spec or task edit
```

`openspec` above needs **this** repo's `openspec/` root; `nix flake check` is
likewise a **per-repo** command (this flake's `checks` are
`formatting`/`lean`/`openspec`, which `../lean-basen` does not have) — never
"run it once for the ecosystem".

**`lake build` enforces zero-`sorry`.** `lakefile.lean`'s `codec` lib carries
`moreLeanArgs := #["-DwarningAsError=true"]`, so `sorry`'s
`declaration uses 'sorry'` warning becomes an **error** and the build exits
non-zero naming the declaration. `default.nix`'s `check` runs that same build, so
`nix build '.#checks.…'` is the gate, not an observation. Verified load-bearing:
stubbing `Codec.roundtrip` to `sorry` fails the build with
`error: Codec/Sound.lean:441:8: declaration uses \`sorry\``.

Because the flag is on the _library_ rather than on one consumer, every path that
compiles `Codec` inherits it (including `bench` and the sandboxed `check`) —
there is no separate lint to drift from the compiler.

`nix build '.#checks.aarch64-darwin.lean'` is the same build, sandboxed — it is a
**long** build: detached with `nohup … > /tmp/x.log 2>&1 &`, then poll. Never
foreground it. To check one law by hand (in-repo):

```bash
printf 'import Codec\n#print axioms Codec.roundtrip\n' > /tmp/c.lean
nix develop --command lake env lean /tmp/c.lean    # expect [propext, Quot.sound]
```

### In `../lean-basen` (its own `nix develop`)

```bash
nix develop --command lake build         # library + Axioms.lean: zero sorry/warnings
nix develop --command lake build bench   # the bench lane (dev-loop only)
```

The `bench` line above is **known-incomplete**: there is no `packages.bench` in
that flake, so the exe is not a flake target — that repo's task 5.3 owns wiring
it. Do not read a green `lake build bench` as "the bench is verified in CI",
and do not add a `nix build '.#bench'` for it here. 5.3 is a
_verification-recipe_ item, not a docs nit; do it first if you need the bench.

`Axioms.lean` is a `@[default_target]` lib, so `lake build` runs its `#guard_msgs`
gates; a `Classical.choice` regression fails the build. To check one law by hand:

```bash
printf 'import BaseN\n#print axioms BaseN.Base64.decodeFullB64_reject_arity\n' > /tmp/c.lean
nix develop --command lake env lean /tmp/c.lean    # expect [propext, Quot.sound]
```

### The rail for a cross-repo import failure

`bad import 'Codec.Normal'` (or any core module) from `../lean-basen`'s
**sandboxed** build does **not** mean a bad import: the flake's `codec` pin
predates that module. Check `../lean-basen/flake.lock` →
`nodes.codec.locked.rev` against `git log --oneline -1 -- Codec/Normal.lean` here,
then `nix flake update codec` (targeted — not all inputs) and `lake update codec`
in `../lean-basen`. Never "fix" it by editing the importing Lean file.

- **Axiom discipline.** Every law stays `[propext, Quot.sound]`-only, zero
  `Classical.choice`, zero `sorry`. `#print axioms Codec.roundtrip` is the check;
  `../lean-basen`'s `Axioms.lean` is a `@[default_target]` lib so `lake build`
  enforces its `#guard_msgs` gates. **In _this_ repo the gate is enforced too**
  (`moreLeanArgs := #["-DwarningAsError=true"]` in `lakefile.lean`): a `sorry`
  fails `lake build` instead of warning. What is _not_ machine-enforced here is
  the `Classical.choice` half — that is what `#print axioms` is for, run per law
  family rather than by the build.
- **The `Bytes n` spec substrate is single.** `Bytes n := Fin n → UInt8` is both
  the proof substrate and its own scalar-read run-model. The packed (`Array UInt8`)
  and byte-slice (`ByteArray`) carriers are proved-equal or trust-seam
  _implementations on top of it_ — the laws never leave `Bytes n`.
- **Two proof layers are never conflated.** Layer 1 (packed carrier + refinement
  theorems) is proven and is the only layer in the axiom gate. Layer 2
  (`byteSlice`/`blitBytes`/`findByte`/`commitRemainder`, `@[extern]` into
  `Codec/ByteSlice.c`) is a **named runtime trust contract, excluded from the gate**.
  `#print axioms <seam>` reporting "no axioms" is **by construction** and says
  **nothing about the C** — `@[extern]` swaps only emitted C; the kernel sees the
  Lean body. "No axiom" is never "no trust."
- **All codecs are pure Lean.** C is only generic bulk byte movement
  (`memcpy`/`memchr` shapes). **No per-format C, no C that parses digits, numbers,
  fields, or format structure.** That is a hard design rule.
- **Speed: get as close to C as possible, with no set threshold — and attribute
  the gap to named causes, never to "boxed scalars".** The owner has explicitly
  set **no ratio to hit**; the requirement is to make the per-element loop as fast
  as it can be and to say honestly where it stands.

  **The numbers live in `README.md`'s stamped table, not here** (this file's rule 2:
  one source of truth per concern). Quote them only with that table's vintage stamp,
  and only from the run that produced it.

  **What belongs here is the attribution discipline, and the fact that it has been
  wrong twice.** The named causes are: the per-step `List` that `decodeArray`
  returns; `packedCands`' `attach.map` rebuilding `PackedCand`'s _proof terms_; and
  the accumulator. The `Array` indexed read is cheap enough that the memory floor is
  **not** the problem — that part of the attribution has survived every
  re-measurement. What did not survive:

  - `packedCands` was attributed **91**, then **32**, then **~430 ns/call**, then
    **3 ns/call hot**, and in the compiled burst lane is **86 ns/call at `k = 1`**
    and **106 at `k = 2`**. **The 3 is withdrawn, not qualified**: its sink was
    `(…).length`, a constant, so the call was folded away. The 430 is a _memory_
    figure wearing a compute label (first-touching a 4 KiB array). Treat the
    remaining numbers as one lane each, and never as a sequence that "improved".
  - The "ideal floor" was quoted as **6 ns/step**, then **16**, then **2.4**, then
    **3.0**, and is **~2.5–2.6 warm (latest burst median) / ~15–18 cold**. Each step of that sequence was a
    different mistake: the 6 came from a lane that `Array.push`-ed every element
    (floor plus n elements of growth); the 16 is a real number but _cold_; and the
    2.4 was the **minimum of 5 decaying rounds** at an `8n` working set — the most
    favourable endpoint of the wrong variant. `benchBurst` now reports
    min/median/max over one L1-resident buffer, and 3.0 is its median.
  - The `Array` read was quoted as **3** and is **~14–18** (cold, per `n`) / **~78
    ns per call** (burst, one read per call).

  **A three-reviewer audit (against `PAPER.md`/`README.md`) is on the record.**
  It found the core pure and proved, and "ready to use" **false** for three
  concrete reasons (no total-bijection `Iso` constructor; `ConsumesByte` never
  derived for `seq`/`iso`; no single-value decode entry point) — all three fixed
  in `Iso.ofTotal`, `seqConsumesByte`/`isoConsumesByte`, `decodeWholeOne` — all
  format-agnostic, **none with an in-tree caller**, because `[S3]` means this
  package ships no concrete codec. A `Codec/Examples.lean` (`u8`/`u16le`/`u16be`)
  was written and then **removed**: that is `../lean-basen`'s territory, and adding
  it here was a `[S3]` breach. It also found the remaining hole is `huniq` for
  unequal-length `alt`. **Do not re-audit; continue from the box above.** One reviewer claim was **refuted** on inspection: the
  paper's `iterate` does _not_ trivially satisfy `Iso.law` — substituting its two
  `Just ∘ driver` directions into `apply a = some b ↔ unapply b = some a` gives
  exactly the fixpoint-agreement claim, so `[D7]` is correct as written.

  **Warm and cold are two different questions and the bench now prints both.**
  `benchRatio` interleaves a same-size `memcpy` (right for a ratio to `memcpy`, but
  it evicts the input, so the figure is _cold_); `benchBurst` runs back-to-back
  calls in one window (the input stays hot, and the span clears the ~41 ns clock
  granularity). A **floor** is a compute claim, so quote it from a burst; a
  **throughput** figure comes from the interleaved lane. Never present one as the
  other — that conflation is what made a 2.4 ns/step floor read as 16 and turned an
  ~11× gap into a claimed ~3×.

  **And a burst is a _range_, not a point.** `benchBurst` used to report the
  minimum of its rounds and the rounds are not independent — they differ only in
  cache warm-up, so the minimum is systematically the most favourable one. It now
  prints min/median/max and the round count, over **one** buffer (the working set is
  `n`, not `8n`; the old 8-buffer rotation is still printed as `(burst@8buf)`).
  Quote the **median** and the range, never the min alone. The same rule as the rest
  of this section: the lane is the source, and the lane now prints the spread it
  always had.

  So: **a number is sourced because the lane, run, prints it — not because a lane
  exists.** Three rows were labelled with a lane and still did not match it. When
  you quote a figure here, run the lane in the same session and paste its output.

  Withdrawn, because no lane ever produced them: the "~1,200–1,290 ns/byte",
  "~8.5× floor", and "20–40× ceiling" figures that used to sit here. **Do not quote a
  "× off C" ratio for a per-element codec measured against `memcpy`** — `memcpy`
  moves a byte; a parser does per-element work, so the comparison is a category error
  and the honest reference is a hand-written C _parser_. **This repo now measures
  one** (`Codec/CRef.c` + `benchCReference`, bench-only, not Layer 2, not in the
  axiom gate), value-checked against `decodeWhole` before it prints. Measured:
  **Lean ≈ 4× the C parser** (28.6 / 27.0 ns/step vs 7.03 / 6.85), so the "10–21×"
  figures are _Lean-relative_ and must never be quoted as "off C" — that was the
  category error this bullet warned about, committed by omission while no C column
  existed. Note also the Lean floor (2.5) is _faster_ than the C reference (6.9):
  C spends most of its time materialising an n-element value array, not parsing.
  Before timing anything here read `tasks.md` 6.1b's MEASUREMENT RULES:
  naive timing reliably produces a wrong number (dead-code elimination reporting
  `0 ns/op`, loop hoisting, cold-start means).

- **The packed cursor is `Nat`, not `USize`.** A `System.Platform.numBits = 64`
  premise would break the `[propext, Quot.sound]`-only gate. `commitRemainder` is
  `USize`-indexed (matching `byteSlice`) so there is no `Nat ↔ USize` roundtrip;
  the conversion is the caller's, once.
- **No unbounded `many` `Codec` value.** It is derived, not a constructor — verified
  un-implementable: the definition-order cycle `Codec → Productive → Rel → Codec`, and
  the mutual-inductive escape fails the universe check. Unbounded repetition is the
  already-proved `relRepeat`/`decodeRepeat`/`encodeRepeat` triple, exposed as a **run
  value**. See the archived `basen-rfc-conformance-theorems`'s `design.md`
  §D0/D7 under `openspec/changes/archive/`.

## Lean proof ergonomics (learned the hard way)

- **`Classical.choice` trap — three verified shapes.** All three are silent (`#print
axioms` on the enclosing theorem is the only check) and all three happened here:
  1. **Dependent `cases`/`match` on a list whose _equation_ sits in context**
     (`bs.length = 1 ∨ bs.length = 2`, `ds.length = k`) — leaks even when every
     cited lemma is `[propext]`-clean. Fix: restate the hypothesis numerically
     (`1 ≤ bs.length`, `bs.length ≤ 2`) or derive the index from the term
     (`count ds.length …`) so the match stays non-dependent.
     **Bisection is goal-shaped, not universal.** Shrinking the body to
     `⟨_, rfl⟩` bisects a **sigma/`∃`** goal. On any other goal shape it does not
     typecheck at all (`⟨_, rfl⟩` is not a term there), so the prescribed
     bisection silently fails rather than isolating the leak. For a
     `decide … = true` goal, prefer rewriting the _proof shape_ — the disjunction
     form of shape 2 below is often the real culprit.
  2. **`decide_eq_true (by omega)` on a disjunction** — `omega` closes a disjunction
     by case analysis, which pulls in classical logic. `decide` alone is fine; the
     _disjunctive_ proof is not. Fix: build the disjunct explicitly
     (`decide_eq_true (Or.inl ⟨a, b⟩)`) and let `omega` close only the arithmetic
     leaf. Reproducer: a `decide ((48 ≤ n ∧ n ≤ 57) ∨ (65 ≤ n ∧ n ≤ 70)) = true`
     goal closed with `decide_eq_true (by omega)` reports
     `[propext, Classical.choice, Quot.sound]`.
  3. **A `match`/`if` on a `Bool` in the _goal_** — a dependent match: `cases b`
     fails with "Dependent elimination failed", and `subst h; rfl` fails with
     "not definitionally equal to `match true, ⋯`". Fix: split the claim into
     `_true`/`_false` lemmas, or `cases b <;> simp_all`.
- **`omega` and modulo.** It **cannot** use a modulo _hypothesis_
  (`n % 4 = 0`) or prove an existential from one; the equational form
  `n = 4 * k → n % 4 = 0` _is_ in its fragment. When it stalls, rewrite to the
  equational form and `rw [hn, Nat.mul_mod_right]`.
- **Never `git stash` / `git reset` / `git checkout -- <file>` to "start clean"** —
  it has destroyed verified work here. If a proof will not compile, stub **that one
  theorem** to `sorry`, get the build green, and iterate in `/tmp/probe.lean`
  against the built library. Commit per law-family so a revert is never tempting.

## Standing preference (the owner's bias — apply it without being asked)

**Always take the most correct solution, not the most convenient one.** This is a
standing instruction, not a per-session choice. Concretely:

- When a plan's stated lemma turns out to be **false**, prove the true statement
  and fix the plan. Do not narrow, weaken, or paper over it to keep the plan. Do
  not stop and offer "the weaker option" as an alternative.
- Prefer the formulation that is actually true and sufficient, even when it is
  more work, an extra case split, a stronger hypothesis, or an extra file.
- If a choice is between _correct_ and _cheap_, take correct. If between two
  correct options, take the one that is more honest about its preconditions.
- Pause and ask only when the requirement itself is genuinely ambiguous or when
  doing the correct thing would be **outside the change's declared scope** — never
  merely because the correct path is harder.
- Record findings and refutations where the next reader will look (`tasks.md`,
  module docstrings), rather than silently diverging from the plan.

## Pause signal (MANDATORY)

**Always play an audible alarm when you pause.** Every time you stop and hand
control back to the owner — end of session, blocked on a question, waiting for a
decision, or presenting options — play an alarm first, then write the summary.
This is a **mandate**, not a nicety: the owner steps away while a long task runs
and relies on the sound, not on watching the terminal, to know when to come back.
A pause with no alarm is a defect in the session — the owner may sit idle for
minutes before noticing your output.

Play one for ~5 seconds (macOS):

```bash
for i in 1 2 3 4 5 6 7 8; do afplay /System/Library/Sounds/Sosumi.aiff 2>/dev/null & sleep 0.35; done; wait
```

- **Play it first, then write prose.** The alarm must arrive _before_ the summary
  it announces. Playing it after the last line defeats the purpose — by then the
  reader has already been waiting.
- **Do not skip it because the pause feels brief.** A one-line "which option?"
  question is exactly the kind of pause this exists for.
- **Do not skip it because it might be noisy.** That judgement belongs to the
  owner, not the agent.
- If `afplay` is unavailable, fall back to terminal bells (`printf '\a'`) in a
  loop, and say which fallback was used.

## OpenSpec workflow

This repo uses OpenSpec (spec-driven). Changes live under `openspec/changes/`;
planning artifacts (proposal / spec delta / design / tasks) are written before
implementation. See `.pi/prompts/opsx-*.md`.

**Consider every open change when forming or validating a plan.** Before authoring
a new change's spec deltas — and before validating any plan, new or in-flight — run
`openspec list --json` to see _all_ active (`in-progress`, `complete`-not-yet-
archived) changes, read their deltas under `openspec/changes/<name>/specs/**`
alongside the main `openspec/specs/**`, then run `openspec validate --all`.

**The MODIFIED-block hazard.** Two changes that each clarify the _same_ requirement
can add _different_ scenarios to the same block; whichever syncs/archives first
leaves the other's MODIFIED block stale, and a MODIFIED requirement **replaces the
whole block**, so a later `openspec validate` flags the dropped scenario. Reconcile
such overlaps at planning time — carry every scenario into each delta's MODIFIED
block — rather than discovering the collision during archive.

**Archive ordering.** When two changes MODIFY the same requirement, archive the
dependency first and re-run `openspec validate --all` after **each** archive. Record
the required order in the later change's `tasks.md`.

## Git conventions

- Commit **individual files**, never `git add -A` or broad globs. Print the exact
  staged set (`git diff --cached --name-only`) before committing.
- A pre-commit hook runs `nix fmt` and **rejects** the commit if it reformats a
  staged file; re-`git add` and commit again. That is normal, not a failure.
- `lake-manifest.json` is gitignored (the library shouldn't pin deps);
  `flake.lock` **is** tracked, for reproducibility.
- New files matter to Nix: `src = ./.` snapshots only **git-tracked** files, so an
  untracked `Codec/*.c` breaks the sandboxed bench build from a clean clone.
  (The dev-loop command is `lake build bench`, which links the `.c` from the
  working tree and does not care about `git`. `nix build '.#bench'` exists —
  `flake.nix:58`, `packages.bench` — as the sandboxed/CI equivalent, and it is a
  **long** build: `nohup`, never foreground.)

## Skills

- Global Lean theorem-proving skill: `lean4` (official).
- Our supplement (project layout, proving-over-primitives, `partial`/coinduction
  lessons, the `Classical.choice` and `omega`-modulo traps above): global skill
  `lean`. It holds **only the generic half** — keep it that way.
- **`openspec/lean-notes.md` is this project's half of that skill.** It is the
  domain-specific record (`Codec`, `Bytes n`, `relRepeat`, `Suffix`, the Layer-2
  seams) that used to live in the skill's Append; the skill points here. Read it
  when a proof involves this library's own primitives, and add to it — not to the
  global skill — when the lesson only makes sense knowing this library. It holds
  **lessons, not direction**: 57 of its entries are also still in the skill, which
  `tasks.md` 7.4 tracks closing. Do not add a new entry to both files.
- Lean PR/convention/proof/MWE skills: `lean-pr`, `lean-bisect`, `lean-proof`,
  `lean-mwe`, `mathlib-build`, `mathlib-pr`, `mathlib-review`, `nightly-testing`,
  `lean4-setup` (all under the `leanprover` skill family).
- Nix: the `nix` skill; `devenv`/`devenv-migration` only for actual devenv work.
