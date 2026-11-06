# AGENTS.md

Guidance for AI coding agents working in this repository.

> ## START HERE: there is no open change
>
> **All three audit rounds are archived.** `codec-audit-round-three` closed 56/56 and
> archived 2026-11-06 as
> `openspec/changes/archive/2026-11-06-codec-audit-round-three/` (7 requirements
> added, 6 modified, 0 removed; `codec/law-coverage` is new with its `## Purpose`
> carried across, and round two's three partition scenarios survived — verified
> scenario-by-scenario at archive time, not assumed).
>
> **First action of the session, always:**
>
> ```bash
> nix develop --command openspec list --json          # is anything open?
> nix develop --command openspec validate --all       # are the deltas sound?
> ```
>
> If a change is open, its `tasks.md` is the ledger and the only direction — open it
> and work top-down. If none is open (today's state) **there is no queued work**, and
> the next piece of work is an _owner decision_: author a new change under
> `openspec/changes/` (the archived ledgers are models for _shape_, never a template
> to resume). Do not invent one from this file.
>
> Do not work from this file; it holds the **stable** part — how to work here, what
> the gates are, and the traps that have cost sessions. Status is computed from
> `openspec/`, never recorded here.
>
> **Nothing in this file names a task or a next task — that is deliberate.** Sessions
> have repeatedly let a prose "next task" go stale while the ledger moved on (a
> START-HERE box said "§1.5 next" long after §1.5–§1.10 had all landed). Do not
> reintroduce a task pointer here, and do not trust one if you find one.
>
> **Re-derive the state; do not believe a number in prose.** Two commands, plus the
> gates below:
>
> ```bash
> nix develop --command openspec list --json | grep -E 'completedTasks|totalTasks'
> nix develop --command lake build 2>&1 | tail -5    # four gate lines, see below
> ```
>
> `lake build` prints **four** gate lines — footprint, partition, definition
> coverage, header numbers — and `openspec validate --all` is 10/10. Read those
> numbers off the run, not off this page.
>
> **`[x]` means "in the tree AND evidence recorded in the ledger" — never tick on
> intent, and never leave a finished task unticked.** A checkbox reports a fact; the
> schedule is a separate sentence. So §2 tasks that the round-four audit closed are
> ticked **even though §1.5 is unstarted** — leaving them `[ ]` made the ledger
> report 16/56 while 28 were done. Before starting anything in §2, read its "evidence
> / what remains" cell: some are already implemented (template `warningAsError`,
> `master`, the arity renames, the `enrichHex`-style prose fixes) and redoing one is
> the concrete cost of this confusion.
>
> **Three items are open in code, not as task numbers** — do not "discover" them as
> bugs: basen's three `native_decide` bench uses (annotated with the route out,
> which needs a `b32TailApply_b32MZTA_chars`-shaped lemma that does not exist), the
> general arity rejection for the fixed-width bases (needs a `decodeFull`-length
> lemma), and `LengthDet → RelAligned` (neither proved nor refuted).
>
> **Never cite a line number in this file or the ledger.** Both carried stale
> `:693`/`:646` figures for the same laws within a single session; cite the grep.
>
> **Rounds two and three are both archived, and the hazard they shared is the one to
> carry forward.** `2026-11-05-codec-audit-round-two` (42/42) and
> `2026-11-06-codec-audit-round-three` (56/56) are history. Round three's delta was
> authored against the _pre_-sync text, so it replaced `codec/axiom-gate`'s
> requirement a second time; it was archived **after** a live-vs-delta scenario diff
> and `openspec validate --all` was re-run **after** the archive — both green, and
> round two's three partition scenarios survived. Do the same for any future change
> that touches a requirement another change already rewrote.

## Current state

**Do not record status here — compute it.** The ledger is the source of truth:

| Question                       | Authoritative file                                                               |
| ------------------------------ | -------------------------------------------------------------------------------- |
| **What is the task right now** | nothing queued — `openspec list --json` returns no open change                   |
| Open changes + task counts     | `nix develop --command openspec list --json`                                     |
| Are the spec deltas sound      | `nix develop --command openspec validate --all`                                  |
| Archived history               | `openspec/changes/archive/<date>-<name>/tasks.md` (e.g. `2026-11-05-lean-basen`) |
| Lessons (not direction)        | `openspec/lean-notes.md`                                                         |

**No change is open; rounds two and three are archived history.**

- `codec-audit-round-three` — **archived** 2026-11-06 as
  `openspec/changes/archive/2026-11-06-codec-audit-round-three/` (56/56 tasks). It
  came from the third audit (three read-only reviewers; reports in `/tmp/r3-*.md`):
  §1 made law coverage structural, §2 fixed prose. The pre-archive scenario diff found
  **no live scenario dropped** (every MODIFIED requirement was a strict superset or
  identical) and `codec/law-coverage` was created with its `## Purpose` carried
  across. Do not reopen it; read its archived `tasks.md` as history.
- A **round-four audit** (three read-only reviewers, 2026-11-05; `/tmp/r4-*.md`) ran
  on top of that and its findings are **applied and pushed** — see the archived
  ledger's "Round-four audit" section in
  `openspec/changes/archive/2026-11-06-codec-audit-round-three/tasks.md` for what was
  fixed, what was refuted, and what is open.
  Its two structural additions are worth knowing before touching a gate: both
  `Axioms.lean` headers are now **asserted** by a `headerNumbers` `run_cmd` (a stale
  count is a build failure), and the template finally enforces `warningAsError`.
  Round three then went further: codec's `Axioms.lean` gained a **third** check
  (definition coverage, §1.8) and its footprint _distribution_ table became
  **generated** by `scripts/gen-axioms.lean` (§1.9) — so in codec the counts are
  asserted and the distribution is emitted, and the two must not be confused when
  updating the header.
- `codec-audit-round-two` — **archived** 2026-11-05 as
  `openspec/changes/archive/2026-11-05-codec-audit-round-two/` (42/42 tasks, all
  gates green, three spec deltas synced and verified). Do not reopen it; read its
  archived `tasks.md` as history.

### How `lean-basen` closed (history — the archived ledger has the detail)

§6.1 (proof gate), §6.2 (base64 `Zh==`/`Zm9=` whole-input rejection) and §6.3b
(base32 `MZ======`) all landed and gated, and the two post-audit items closed:
**§6.4** closed the gate's coverage of the then-current theorem set (91/404 ->
all of it; the count has moved since — read `../lean-basen/Axioms.lean`'s header,
not this file), and **§6.5** removed
every `set_option linter.… false` rather than deferring it. **§6.10** closed:
the ecosystem is on Lean 4.35.0. The `lean-toolchain` pins
now match what builds (`v4.35.0`), the lockfiles are nixpkgs `1d06008`
(2026-11-03), and `basen` tracks `codec` `3277d48`. The bump cost **one line**
in `Codec/Packed.lean` — `basen` needed no source changes — because the
toolchain itself was a cache substitution. Two traps from that bump:

- **A single law was toolchain-dependent, and is now simply shorter.**
  `Codec/Packed.lean`'s `decodeFullArraySearch_cons`: 4.35.0 closes the goal at
  the `conv`+`rw` that 4.34.1 left open, so the old `simp only`/`split`/
  `injection` tail became dead. The provenance is worth knowing because the
  naive fixes were _wrong_: plain deletion is green on 4.35.0 but **red on
  4.34.1**, and `try`-wrapping fails the other way. While both toolchains were
  supported it carried a `first | (tail) | skip` guard; now that the ecosystem
  is pinned to 4.35.0 the guard is gone and the proof is **one line**. Verified
  non-vacuous by mutating an arm of the statement (it then fails with
  `unsolved goals`) — do that check whenever a proof collapses to one tactic.
- **A `lake build` segfault after a bump means stale build state.** Right after
  the bump, `lake build bench` aborted with `unsupported IRType` (exit 139);
  `rm -rf .lake` and the same command is green. So before diagnosing a crash as
  a toolchain or lakefile problem, clean the build dir.

**The one scoping lesson worth keeping, because it cost sessions.** §6.2 was for
a month recorded as "repeatedly blocked on `Suffix`/`splice` index bookkeeping
in the `blocks = []` branch" — and that was **wrong**. Measured: for the 4-byte
`Zh==` input, `decodeRepeat b64BlockElem …` yields **one** decomposition,
`blocks = []`, `t.remaining = 4`, because a base64 full block consumes exactly 4
bytes and a 4-byte input cannot populate `blocks` at all. There was no `cons`
branch to kill and no `splice` work; the `ZgAAAA`-shaped difficulty belonged to
that 8-byte input. The landed proof keeps a two-line `omega` for the `cons`
branch anyway — it must not depend on a `#eval` about one literal — and it
closed in one session.

### Where the work is going (a pointer, not a ledger)

The roadmap **lives in `openspec/`**. Three audit rounds have landed and each one
found a different layer: round one the gate's _existence_, round two the gate's
_mechanism_, round three the gate's _universe_ (it covers theorems, not
definitions, so a public `def` with no law is outside every check). Round three's
`tasks.md` §1 closes that, and §2 is the prose.

The next **format port** (another `lean-*` repo) is still an owner decision; this
file does not guess it. When one is chosen, author it as a new change under
`openspec/changes/` — the archived `lean-basen` ledger is the model for shape, not
a template to resume.

### Traps that have actually cost sessions here

- **`Suffix`/`splice` bookkeeping is _not_ where §6.2 died — check the input
  length before reaching for it.** The old version of this bullet asserted six
  sessions were lost to `splice` in the `blocks = []` branch. Measured
  2026-11-05, that branch is **trivial** for the actual 4-byte `Zh==` input
  (`decodeRepeat` returns exactly one decomposition, `blocks = []`), because a
  full base64 block is 4 bytes. Reach for `Suffix`/`splice` API reading only if
  a `#eval` of the decomposition shows a non-empty `blocks`; do not assume it.
- **`decodeFull` is not `decodeFullB64`.** The fixed-width bases use the `Run`
  combinator (unfolds with `WellFounded.fix_eq` + `decodeFullStep.eq_def` +
  `simp`); the padded bases use a `filterMap` composition that same recipe gets
  **stuck** on. Use `cases h : decodeFullB64 s` + `decodeFullB64_some` instead —
  the library never unfolds that recursion, and none of its own rejection
  theorems do either.
- **A §3.5 pad-bit rejection is a `decide`, not an induction** — but the recipe
  does **not** transfer verbatim between bases. For base32,
  `b32BlockDecodeLenient` matches an **8-binder** list, and both `split` (its
  internal simp) and `simp_all` blow the simp step limit; `unfold … ; decide` on
  the whole closed goal is what works. Base64's 4-binder version does close with
  `split` + `decide`. See §6.3b's note in the ledger.
- **A base32 twin transfers the proof _shape_, never the constants.** Base64's
  `Zh==` needs `b64BlockUnapply [0x66] = some Zg==`; base32's `MZ======` needs
  `MY======`, because the two bases pad at different widths. Re-`#eval` every
  literal before writing the proof — `decide` will catch it, but only if you let
  it.
- **`../lean-basen` pins `codec` through `flake.lock`.** If it predates something
  this repo added, the fix is a targeted `nix flake update codec` + `lake update
codec` — a `bad import` means a stale pin, never a wrong import.
- **`huniq` is a hypothesis by design for any codec other than `Codec.byte`**
  (`Codec.huniq_not_derivable` machine-checks that it does not follow from
  unambiguity + productivity). Do not reopen it as unfinished work.

### Traps specific to the current ledger (round three)

These cost time _this_ session and are the ones §1/§2 will run into. Read them
before starting §1.

- **The `Classical.choice` leak in §1.2 is the trap to carry into §1.5+ — carry a
  `Nat` equation into an induction and a proof _compiles clean and leaks_.**
  Proving `Rel (count k p) xs s ↔ xs.length = k ∧ …` by induction on `k` with
  `xs.length = k` in context makes every `cases xs` a dependent match; the result is
  `[propext, Classical.choice, Quot.sound]` with **no compiler error**, only
  `#print axioms` shows it. Bisected: every ingredient was `[propext]`-only alone and
  the leak appeared only when the recursive call carried the equation. **The fix:
  recurse on the _list_ and let the length be `xs.length` derived from the term**
  (`relRepeatToCount`). Applies to every `count`/length-shaped law still to come.
- **A `simp only` set that does not fire leaves `sorryAx`, not an error.** For
  `seqRight`'s composite `Iso`, `Option.some.injEq` does not match the
  `(some (y,u)).bind … = some x` shape, and an attempt that dropped the `simp`
  entirely still compiled. `injection … with h; subst h` is what closes it.
  `seqLeft`'s shape _is_ `simp`-dischargeable, so the recipe does not transfer
  between the two halves of the same family. Always `#print axioms` a new law family.
- **`unfold <def>` does not reduce a `match`-`def` at a variable argument.**
  `count` (matches on `n`) and `relRepeat` (matches on the list) both stay opaque, so
  `Rel_iso`/`Rel_seq`/`relRepeat_cons` cannot fire. State the recursion equation as
  its own `rfl` lemma (`count_succ`) or `cases` on the matched argument first.
- **A gate whose _prose_ quotes counts needs the counts asserted, or the prose rots
  while the gate stays green.** Both `Axioms.lean` files had a header table that was
  stale by a full regeneration (`292` vs `310` in codec; `446 / 437 / 9` vs
  `483 / 437 / 46` in basen — the `9` was a genuine authoring error, not drift),
  because `partition`/`gateCoverage` compare set _membership_ and never read prose.
  Both files now carry a `headerNumbers` `run_cmd` asserting the table's numbers and
  their sum. **When you regenerate, the header check fires — update the table and the
  `expected*` constants together.** Do not weaken it to a `logInfo`.
- **The gate catches your own new laws, by design — regenerate, do not investigate.**
  Every law added in §1 fails `lake build` with `not pinned by this gate` until
  `scripts/gen-axioms.lean` is run. That is §1.1 doing its job, not a regression.
- **A `def` with no law used to be invisible to every gate — §1.8 closed that, but
  only as a _mention proxy_.** `Axioms.lean`'s theorem partition is `thmInfo` only,
  so a public `def` was in neither `gatedNames` nor `generatedAuxAllowlist` — not
  "un-gated", _outside the partition_ — which is why `btake`, `maybe`, `manyUpTo`,
  `seqRight`, `seqLeft`, `between` shipped with zero theorems while the gate was
  green. There is now a third `run_cmd` requiring every public `def` to be mentioned
  by some gated theorem's **type** or listed in `definitionSurfaceAllowlist` with a
  reason, and the header asserts the counts (`140 = 111 + 29`). Read it as the proxy
  it is: it cannot be satisfied by _silence_, and it **can** be satisfied vacuously.
  When you add a `def`, still grep for a theorem mentioning it before believing the
  law is worth having.
- **"Free theorem" claims used to live in `Codec/Combinators.lean` and were false at a
  variable `n`; §1.7 rewrote them.** The docstring claimed the derived combinators'
  characterizations were definitional consequences and that
  `decode_spec`/`bidir`/`roundtrip` "hold unconditionally via `Codec.Sound`". Those
  three are **structural inductions on the `Codec` value** and `count n p` is
  `iso` of `seq p (count (n-1) p)`, so the case cannot close — no such law exists for
  any of the eight derived values, and that is a fact about the derivation's shape,
  not a backlog item. Do not reintroduce the claim.
- **`List.ofFn` equality is not `rfl` across two different functions.** In the
  base32 §3.5 work, `List.ofFn sb₁ = List.ofFn s₀` needed `congr 1; funext i;
exact hsb_eq i.1 i.2`. `cases`/`decide` on the whole goal also works when the
  inputs are literals.
- **`Iso` projections of structure fields defeat `unfold`/`split`.** A structure
  literal's `.apply` does not reduce under `split`; use
  `simp only [<the def>] at h` to expose it first. This is why the `Unambiguous`
  counterexample proofs use `simp only [uniqSeqBo, uniqSeqBt, Rel_alt, Rel_pure,
Rel_iso] at hx hy` rather than unfolding.
- **A `have := …` whose name collides with a definition shadows it.** `have := h …`
  named it `this`; naming it `RelAligned` or `hcon` collided. Use a name that is
  not a declaration.
- **Do not trust a reviewer's arithmetic without re-deriving it.** Round three
  reported `Axioms.lean`'s footprint table as wrong (197 vs 195); re-derived it was
  correct — their parser truncated at the `?` in `attach_getElem?_corr`. Design D1
  records this. A refuted finding is a result; relaying it unverified is the defect.
- **`native_decide` is banned for laws and fine in the bench.** It appears only in
  `Bench.lean` (a `packages` entry, not a `checks` one). Never introduce it into
  `Codec/`.

### Rules about this file

- **Direction lives in exactly two places: this file and `openspec/`.** No
  `HANDOFF.md`, no `NOTES.md`, no scratch tree. `openspec/lean-notes.md` is
  _lessons, not direction_ (the project half of the global `lean` skill); if an
  entry there reads like a task list, move it to the ledger.
- **History is not direction.** What landed, when, and what was measured belongs
  in the change's `tasks.md` and `CHANGELOG.md` — including archived changes,
  whose own `tasks.md` under `openspec/changes/archive/` is the reference. Do not
  re-teach landed work here.
- **Archive hazard.** A MODIFIED block **replaces** the live requirement wholesale,
  so any live scenario the delta does not restate is dropped at sync time. Two
  changes modifying the same requirement must archive dependency-first, with the
  order recorded in the later change's `tasks.md`. This has already fired twice:
  `lean-basen` / "The `basen` bases are `Codec` values", and
  `codec-audit-round-two` / `codec-audit-round-three` both rewriting
  `codec/axiom-gate`'s partition requirement. **Check the live spec's scenario
  count against the delta's before syncing** — `openspec validate` will not always
  catch a narrowed set, and round three authored its delta against the pre-sync
  text.

### Ecosystem shape (stable, not status)

Each verified format/protocol is its own git repo, initialized from
`lean-nix-flake-template`, prefix-dropped internally (`lean-basen` → `basen`/
`BaseN`; `lean-vbin` → `vbin`; …), depending on `codec` **by flake input +
`require codec from git` injection — never vendored**, and inheriting the
single-`Bytes n`-substrate and `[propext, Quot.sound]`-only discipline.

**Toolchain: all four Lean 4 repos are on 4.35.0** (2026-11-05):
`lean-codec`, `lean-basen`, `lean-nix-flake-template` and `../workflow` each pin
`lean-toolchain` `v4.35.0` and nixpkgs `1d06008`. Keep them in step —
`lean-basen` fetches `codec` by rev, so a `codec` bump means
`nix flake update codec` + `lake update codec` there.

**`../workflow` was the one exception and no longer is.** It used to pin a
`cauli/lean4` fork (`62b6a229`) with "Do NOT move this pin", because it was
compiling the kernel to WASM and needed emitted C to match a prebuilt link kit.
**That WASM path never worked and was removed 2026-11-05** — the link-kit
archives are `-m32` cross-compiled while the emitted `Kernel.c` is not (OOB crash
inside `l_Lean_Json_parse`), and rebuilding Lean to wasm32 to match hit an
`emscripten`/`lld-22` wall. The fork input and both packages that served it are
gone; it now uses nixpkgs `lean4` like everything else. **Do not reintroduce a
fork pin** without evidence the link kit is regenerated at a matching sha.

Two traps from the 4.35.0 bump: `lean-toolchain` is **inert** in these repos
(nothing reads it — check `lake build -v`), and a `lake build` segfault right
after a bump means stale `.lake` artifacts, so `rm -rf .lake` before diagnosing.

In `../lean-basen`, `codec` is a flake input threaded into `default.nix`, which
rewrites `require codec from git …` → a local `require codec from "./codec-src"`
path dependency, so the sandboxed `lake build` needs no network. (`lean-codec` is
public, so the `github:` input fetches anonymously — no token, no `--impure`.)

## Verification recipe

Every command below names **its own repository**. They are different flakes with
different `checks` sets — never run one tree's recipe in the other.

### In `lean-codec` (this repo)

```bash
nix develop --command lake build            # 15 jobs, zero warnings; FAILS on `sorry`
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
nix develop --command lake build bench   # the bench lane (fast dev loop)
nix build '.#bench'                      # same lane, sandboxed — BUILDS AND RUNS it
```

`packages.bench` exists and is a **package, not a `checks` entry**: the lane
value-checks known vectors, which is evidence, not proof, so it must not be able
to fail the proof gate. Its `installPhase` _runs_ the executable, so
`nix build '.#bench'` verifies the vectors rather than merely producing a binary.
Do not add it to `checks`, and do not treat a green `lake build bench` as having
verified anything — that only compiles.

`Axioms.lean` is a `@[default_target]` lib, so `lake build` runs its `#guard_msgs`
gates; a `Classical.choice` regression fails the build. To check one law by hand:

```bash
printf 'import BaseN\n#print axioms BaseN.Base64.decodeFullB64_reject_arity\n' > /tmp/c.lean
nix develop --command lake env lean /tmp/c.lean    # expect [propext, Quot.sound]
```

**Since §1.0 it also has a _mechanism_, not just blocks.** `lake build` now prints
three lines and fails if any disagrees with the environment:

```
info: basen axiom gate: 438 pinned + 46 allowlisted = 447 of 484 public theorems (0 explicit exclusion(s))
info: basen axiom gate: 484 public theorems partitioned, 438 pinned and 46 allowlisted
info: basen axiom gate: header numbers verified (484 = 438 + 46)
```

So a new `BaseN` law fails the build until it is pinned, and a stale pin fails too.
Two traps, both hit in §1.0: a probe theorem must be **inside** `namespace BaseN.*`
or it is outside the gated universe and the gate stays green; and a `lake build`
that reports `Replayed Axioms` after you edited an imported module is reading a
stale `.olean` — delete `.lake/build/lib/lean/{BaseN/…,Axioms}.olean` before
believing a green result.

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
  This package has had **eight** performance figures wrong at some point (6 → 15 →
  2.4 → 3.0 → 2.46 for the floor; 91 → 32 → 430 → 3 → 75 → 86 for `packedCands`,
  the 3 withdrawn outright; 3 → 11–18 for the array read; and "~11×" derived from a
  cherry-picked burst round). **Two were caught by the owner asking why two
  committed figures could not both be true, not by a lane** — so an internal
  inconsistency between two numbers is itself a legitimate check, and "it came from
  a lane" is not sufficient.

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
