# Tasks — `basen-radix`

> **START HERE.** This change adds the one missing rung in `basen`: a radix-generic
> conversion from a numeral (digit bytes) to the number it denotes (a `Nat`). Today the
> package decodes text to `List UInt8` and **never to a number** — see `design.md` D0 for
> the measured evidence, including `grep -rn 'radix|base : Nat|pow' BaseN/*.lean` → nothing.
>
> **It supersedes `basen-nat-iso`**, which is the base-10-only slice of the same layer.
> Retire that change; do not land both (`design.md` D8).
>
> **`basen-uppercase-prepass` is NOT in scope.** Different requirement family (case folding
> vs padding), still parked on the owner's library-division decision.
>
> Scope decisions already made, so they are not re-litigated mid-implementation:
> **`Nat` only** (no `Int`), **zero is the single zero digit** (not the empty sequence,
> D4), **`numeralIso` does not touch the padded bases' tail spine** (D5), **block isos are
> kept and proved equal** (D6).
>
> **The first task to do is 3.2 as a spike.** The six block-iso equalities are the risk
> sink: if a base's existing block iso does **not** agree with the generic fold, that is a
> real bug in `basen` today, and it is better found at task 1 than at task 6.
>
> ### Where things are — measured 2026-11-13, read before the first command
>
> |                                                               | where                                                             |
> | ------------------------------------------------------------- | ----------------------------------------------------------------- |
> | the **code** (`BaseN/*.lean`, `Axioms.lean`, `lakefile.lean`) | `../lean-basen`                                                   |
> | the **spec** and this change                                  | `lean-codec` (this repo) — `../lean-basen` has **no `openspec/`** |
>
> **`../lean-basen` builds green today**: clean tree on `master`, `lake build` →
> `Build completed successfully (25 jobs)`, all six gate lines self-consistent
> (`490 = 444 + 46`). That is a **regression baseline**, not a repair job — re-run it first,
> expect green, and expect the job count to **rise** as you add `Radix.lean`.
>
> The `codec` pin is `14b54fa` (68 commits behind `lean-codec`'s HEAD) and **`Codec/Normal`
> is identical at that pin and at HEAD**, `fill_surj` included. **No `codec` bump is
> needed** — see §0.2 and §6b.3, and do not bump it "just in case".
>
> **A new module must be imported by `BaseN.lean`** or it is never compiled and its laws
> never reach the gate (§0.4, §1.1). That failure mode looks exactly like success.
>
> Legend: **[M]** MUST, **[S]** SHOULD.

## 0. Preconditions — MEASURED 2026-11-13, so the first step is not a discovery

**Everything in this section was checked by command on 2026-11-13.** Read it as the state
of the world, not as work to do; re-verify only if the tree has moved.

- [x] 0.1 **`../lean-basen` builds green today.** Measured:

      ```
      git status --porcelain          -> empty (clean, branch master)
      nix develop --command lake build -> Build completed successfully (25 jobs)
      ```

      All six gate lines printed and self-consistent: `444 pinned + 46 allowlisted = 490
      of 490`, `header numbers verified (490 = 444 + 46)`, `137 public definitions`
      (`122 mentioned + 15 allowlisted`), `native_decide 12 uses, all bench-lane`, `46
      claim site(s)`. Zero `sorry`, zero warnings. **Re-run this build as the very first
      command of the session** — it is a regression check, not a repair job.

- [x] 0.2 **The `Codec/Normal` layer is reachable, and is the same API as today's.** The
      pin is `codec @ 14b54fa` (`flake.lock` → `nodes.codec.locked.rev`), which is an
      **ancestor** of `lean-codec`'s HEAD, **68 commits behind**. Measured by diffing the
      file at both revisions: `Normal`, `Normalizer`, `fill`, `fill_raw`, `fill_fixed`,
      **`fill_surj`**, `fill_inj`, `decodeNormal`, `decodeNormal_of_fixed`,
      `decodeNormal_encode` exist at **both**, with identical signatures. So nothing in
      this change needs a `codec` bump.

      **Toolchains agree**: `basen`'s `lean-toolchain` and `codec`'s are both
      `leanprover/lean4:v4.35.0` at the pin and at HEAD.

- [x] 0.3 **Which repo holds what — the fact a first step gets wrong.** Stated once here
      because it is not inferable from either tree:

      | thing | repo |
      | --- | --- |
      | the **code** (`BaseN/*.lean`, `Axioms.lean`, `lakefile.lean`) | `../lean-basen` |
      | the **spec** (`openspec/specs/basen/spec.md`) | **this** repo (`lean-codec`) |
      | **this change** (`openspec/changes/basen-radix/`) | **this** repo |
      | `Codec/` (the `Normal` layer, `Iso`, `Codec`) | **this** repo, consumed via `flake.lock` |

      `../lean-basen` has **no `openspec/` directory at all** — `ls openspec` there fails.
      Every `openspec` command in this change runs in `lean-codec`; every `lake` command
      runs in `../lean-basen`. Mixing the two up is the single likeliest first-step error.

- [x] 0.4 **A new module must be registered.** Adding `BaseN/Radix.lean` is not enough:
      `BaseN.lean` imports each base explicitly, one line per base. A file that is not
      imported by `BaseN.lean` is **not compiled by `lake build`** and its laws never reach
      the gate — a silently unbuilt module. Add `import BaseN.Radix` to that list in §1.1,
      and confirm the build's job count rises.

- [x] 0.5 **The dev-loop `codec` copy is the pin, not `master`.** `lakefile.lean` says
      `require codec from git … @ "master"`, but `.lake/packages/codec` is checked out at
      **`14b54fa`** — the ref was resolved once and cached. So a plain `lake build` here
      tests against the **pinned** `codec`, while `nix build` also uses the pin. They agree;
      do not "fix" the `@ "master"` line (the lakefile's own comment says why pinning it to
      a SHA is the wrong move).

- [ ] 0.6 Re-read `design.md` D2 (codomain is the quotient) and D5 (padded tails are out of
      scope). Both are the decisions a careless implementation gets wrong, and both are
      stated as requirements so the gate can catch them.

- [ ] 0.7 Do **not** `git stash` / `git reset` / `git checkout -- <file>`. Commit per
      section **in `../lean-basen`**, whose history is separate from this repo's — a commit
      here does not commit a `BaseN/` edit, and vice versa. `AGENTS.md` records that a stash
      has destroyed verified work in this ecosystem.

## 1. [M] The generic layer — `digitVal`, `toNat`, `ofNat`

Findings: `design.md` D0/D1. The whole change rests on this section being right.

- [ ] 1.1 Create `BaseN/Radix.lean` with `digitVal (radix : Nat) (b : UInt8) : Option Nat`.
      It SHALL accept the RFC 4648 alphabets for 16/32/64, the bit/quartet/octal digit
      alphabets for 2/4/8, and decimal digits for 10 — **one** function, not a dispatch on
      hand-rolled copies. Prove it agrees with each base's existing alphabet function
      (`bitVal`, `quartetVal`, `octToVal`, `hexToNibble`, `b32ToVal`, `b64ToVal`, `digVal`)
      at that radix, so `design.md` D1's "proved-equal specialisation" is a theorem and not
      a claim.

      **Register the module in the same step** (§0.4): add `import BaseN.Radix` to
      `BaseN.lean`'s import list. A file not imported there is not compiled by `lake build`
      and its laws never reach the gate. Confirm it took by watching the job count rise —
      an unimported module looks exactly like a module with no laws.

      The exact loop for every task in this change:

      ```
      cd ../lean-basen
      nix develop --command lake build          # ~25 jobs; expect it to RISE as you add
      nix develop --command lake build bench    # the bench lane, unchanged by this change
      ```

      and, for the spec side, in **this** repo:

      ```
      cd ../lean-codec
      nix develop --command openspec validate --all
      ```

- [ ] 1.2 `toNat (radix : Nat) (ds : List UInt8) : Option Nat` — the most-significant-first
      fold `acc := acc * radix + d`. Total on valid sequences; `none` on any out-of-alphabet
      byte, and **not** partially converted. State and prove the fold's recursion equation
      as its own lemma (`AGENTS.md`: `unfold` does not reduce a `match`-def at a variable
      argument).
- [ ] 1.3 `ofNat (radix : Nat) (n : Nat) : List UInt8` — canonical digits, minimal, no
      leading zeros, and `ofNat radix 0` is that radix's **single zero digit** (D4). Prove
      `toNat radix (ofNat radix n) = some n` and `ofNat (toNat radix ds)` returns the
      canonical form, i.e. the round-trip pair at the heart of the `Iso`.
- [ ] 1.4 Mutation-test 1.2 and 1.3: reverse the digit order in `toNat` and confirm the
      round-trip proofs fail. A round-trip pair that survives a reversed fold is not
      constraining anything.

## 2. [M] The quotient and the `Iso`

Findings: `design.md` D2/D4.

- [ ] 2.1 Define `trimFor (radix : Nat) : List UInt8 → List UInt8`, absorbing leading zeros
      and leading whitespace, and prove it total and idempotent. It SHALL NOT absorb
      trailing whitespace, a radix prefix, or anything that changes the value (D3's table).

      **Before writing it, read `basen-uppercase-prepass`'s `upperNormalizer`.** That parked
      change builds a `Normal`-based pre-pass with the same shape, and its §8 explicitly
      says trimming "belongs with whatever numeric codec is eventually built, and should
      reuse `upperNormalizer`'s shape rather than invent a second mechanism". This change
      was authored without knowing that, and it is exactly the kind of pair
      `AGENTS.md` warns about — two normalisers that must agree, and no arm comparing them.
      Either reuse its shape, or record in `design.md` why a second mechanism is right.

- [ ] 2.2 State `numeralIso : (b : Nat) → 2 ≤ b → Iso Nat (Normal (List UInt8) (trimFor b))`
      and discharge its `law` from 1.3's round-trip pair plus `fill_surj`. **The codomain is
      the quotient** — a version stated over raw `List UInt8` must be rejected in review,
      and this task's own acceptance is that the law holds _unconditionally_ with no
      hypothesis about spelling.
- [ ] 2.3 Prove the **three-spelling witness** — canonical, leading-zero, and
      leading-whitespace spellings of one number all reach the same image — and
      **mutation-test it** by removing one absorbed variation and confirming it fires. This
      is the task `basen-nat-iso` §Risk named as "the first task, before any other proof",
      and it stays true here.
- [ ] 2.4 Prove the rejection direction: a trailing non-digit, an out-of-alphabet digit, and
      trailing data after a valid numeral all yield `none`. State these as their own laws
      rather than as prose.

## 3. [M] The seven radices, and the block isos proved equal

Findings: `design.md` D5/D6.

- [ ] 3.1 Instantiate `numeralIso` at radices 2, 4, 8, 10, 16, 32, 64. Each SHALL carry its
      `2 ≤ b` witness explicitly. Enumerate the seven from one source in the gate so a
      missing radix is a build failure rather than a shorter list.
- [ ] 3.2 Prove, for each of the six power-of-two bases, that its block iso agrees with
      `toNat` restricted to that block (`bitBlockIso`, `quartetBlockIso`, `octBlockIso`,
      `hexBlockIso`, `b32BlockIso`, `b64BlockIso`). These are the "kept and proved equal"
      theorems of D6.
- [ ] 3.3 **Mutation-test every 3.2 equality** by perturbing that block iso's digit order
      and confirming the theorem fails naming it. Six equalities, six mutations.
- [ ] 3.4 Record, in the module docstring, that `numeralIso` is **not** defined through the
      padded bases' `B32`/`B64` tail spine (D5), and why — a numeral has no padding. State
      it where a future implementer will reach for `b64BlockIso`.

## 4. [M] The gate

- [ ] 4.1 Pin every new law in `../lean-basen/Axioms.lean` and regenerate. The gate fails
      the build on an unpinned law, which is the intended behaviour, not a regression.
- [ ] 4.2 Every new law stays `[propext, Quot.sound]`-only: `#print axioms` per law family.
      Watch for the two recorded leaks — a dependent `cases` carrying an equation, and
      `decide_eq_true (by omega)` over a disjunction (`AGENTS.md`). Both are silent.
- [ ] 4.3 Update the header counts the `headerNumbers` arm asserts, in the same commit as
      the regeneration. The gate fires on a stale table, and that is the check working.

## 5. [S] Verification

- [ ] 5.1 `nix develop --command lake build` in `../lean-basen` — zero `sorry`, zero
      warnings, all gate lines green. **Baseline for the job count is 25** (§0.1); it must
      have risen by the new module, and the header counts must have been re-asserted (§4.3).
- [ ] 5.1b `nix develop --command lake build bench` in `../lean-basen` — the bench lane must
      still link and run. This change adds no bench row, so this is a regression check; a
      break here means `Radix.lean` perturbed something the bench depends on.
- [ ] 5.1c `nix build '.#bench'` in `../lean-basen` — the **sandboxed** lane, which is the
      only one that proves the Nix build still works after a module was added. It is a long
      build: `nohup … &`, then poll. Never foreground it.
- [ ] 5.2 `nix develop --command openspec validate --all` in **this** repo.
- [ ] 5.3 Every value-checked claim in this change is a _theorem_, not an `example`; if any
      run-time check is added, it goes in the bench and `checks.bench` must reach it.
- [ ] 5.4 `CHANGELOG.md` entry in the register of an **addition**, naming the three new
      requirements.

## 6. [S] Retire `basen-nat-iso`

- [x] 6.1 Delete `openspec/changes/basen-nat-iso/` and record in this change's `tasks.md`
      that its three ADDED requirements are subsumed — base 10 is one of §3.1's seven — so a
      future reader does not wonder where it went.

      **RETIRED 2026-11-13 (at authoring time, by owner decision).** The three requirements
      it would have added, and where each now lives:

      | `basen-nat-iso` | `basen-radix` |
      | --- | --- |
      | The numeric codec's value type is a number, not a byte list | **A numeral denotes a number** |
      | Information-free variation is normalised, not rejected | **A number is its canonical numeral modulo information-free variation** |
      | The normaliser is one total idempotent function, proved | same requirement, §2.1's `trimFor` |

      No requirement *name* collides, so nothing had to be reconciled. The change was never
      started (0/18), so no partial work is stranded.

      **It was retired rather than landed because it is the base-10-only slice of this
      layer.** Landing both would put two `Nat` codecs in one package with two quotient
      stories and two zero conventions — `basen-nat-iso`'s proposal left "is the empty
      encoding zero?" open, and `design.md` D4 answers it once for all seven radices.

- [ ] 6.2 Confirm nothing in that change's analysis is lost: its `Nat`-first scoping, its
      codomain-in-the-quotient decision, and its `Nat`-only recommendation are all carried
      forward in `design.md` D2/D4/D7.

## 6b. [M] The two-repo mechanics, stated once

**This section exists because it is the most likely source of first-step confusion**, and
it was measured rather than assumed.

|                                  | where                                               |
| -------------------------------- | --------------------------------------------------- |
| the change's planning artifacts  | `lean-codec/openspec/changes/basen-radix/`          |
| the `basen` **spec** it modifies | `lean-codec/openspec/specs/basen/spec.md`           |
| the **code** it changes          | `../lean-basen/BaseN/`                              |
| the `codec` layer it consumes    | `lean-codec/Codec/`, via `../lean-basen/flake.lock` |

- [ ] 6b.1 **Two histories.** `../lean-basen` is a separate git repo. Committing
      `BaseN/Radix.lean` does not commit the spec delta, and vice versa. Each repo is
      committed and pushed on its own; a session that commits only one leaves the other
      dirty, and `AGENTS.md`'s "commit early" rule applies **per repo**.
- [ ] 6b.2 **A `codec` change is not needed.** `basen-radix` consumes `Codec/Normal.lean`
      as it exists at the pin (`14b54fa`). If an implementation step is tempted to edit
      `Codec/`, stop: that is a different change, in a different repo, and it would need its
      own delta and its own gate run.
- [ ] 6b.3 **Do not bump the `codec` pin as part of this change.** It is unnecessary (§0.2:
      the `Normal` API is identical at the pin and at HEAD), and a bump would move 68
      commits of unrelated `codec` work into this change's blast radius. If a bump ever
      becomes necessary, it is `nix flake update codec` + `lake update codec` in
      `../lean-basen`, **targeted** — never a full `nix flake update`.

## 7. Recorded, deliberately not in this change

- [ ] 7.1 **`varint`.** Enabled by this layer (radix 128 with a continuation bit) but not
      delivered: it is a run triple over bytes with its own benchmark, and this change stops
      so the numeral layer can be measured first (`design.md` D7).
- [ ] 7.2 **`Int`.** Deferred; `-0x10` raises sign canonicalisation, which is a design
      question in its own right.
- [ ] 7.3 **`basen-uppercase-prepass`.** Parked on the owner's library-division decision.
      Untouched.
- [ ] 7.4 **Reading a padded encoding as a number.** Out of scope by D5, and stated as a
      requirement so no theorem accidentally claims it.
