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
> tied to the fold by a canonicity-filtered implication** (D6).
>
> **Progress: 6/39** (the six `[x]` are §0's five measured preconditions
> plus §6.1's retirement; every implementation task is open).
>
> **The first session is §1, not §3 — and that is a correction.** An earlier banner said "do 3.2
> first as a spike", which is impossible: 3.2's statements mention `toNat`, so the fold must
> exist before the ties can be stated. What the advice was _trying_ to say is that **3.2 is the
> risk sink** — if a base's block iso genuinely contradicts the fold, that is a real bug in
> `basen` today. So session 1 builds the fold and **probes** one block iso against it; the
> seven ties land in session 2.
>
> ### Session plan — this is several sessions, and each one ends green
>
> | session             | tasks                                                            | green at the end means                                                                                                 | **not yet true**                             |
> | ------------------- | ---------------------------------------------------------------- | ---------------------------------------------------------------------------------------------------------------------- | -------------------------------------------- |
> | **1. The fold**     | 1.1–1.4, plus a throwaway probe of one block iso (not committed) | `toNat`/`ofNat` exist, round-trip proved, `BaseN.lean` imports `Radix.lean`, gate green with the new def + laws pinned | no `numeralIso`, no ties, no radix instances |
> | **2. The ties**     | 3.1–3.5, 4.2, 4.2b, 4.3 (partial)                                | all seven block isos tied by implication pair; allowlist trimmed 10→3; header constants re-derived                     | no quotient, no `Iso`                        |
> | **3. The quotient** | 2.1–2.4, 3.1's radix instances                                   | `trimFor` total+idempotent; three-spelling witness mutation-tested; `numeralIso` at seven radices                      | —                                            |
> | **4. Gate + docs**  | 4.1, 4.4, 4.5, 5.x, 6.x                                          | everything pinned, CHANGELOG, all gates                                                                                | —                                            |
>
> **Tasks that cannot be left half-done** (stopping mid-way leaves a red gate): **4.1** (an
> unpinned law fails the build), **4.2 with 4.2b and 4.3** (trimming the allowlist without
> re-deriving the constants trips `headerNumbers`), and **any commit that adds a `BaseN` public
> theorem** without its `#guard_msgs` block. Everything else can stop at a task boundary.
>
> **A cold-start reader needs:** this table, §0's measured facts (the two-repo split, the pin,
> the `BaseN.lean` import requirement), and the note that **`basen` has no generator** — pinning
> is by hand (4.1).
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
> The `codec` pin is `14b54fa` (measured 70 commits behind `lean-codec`'s HEAD as of
> `9a7231f`, and the count moves every commit — quote it with its HEAD or not at all) and **`Codec/Normal`
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
      **ancestor** of `lean-codec`'s HEAD, and far behind it — the exact count moves on every
      commit, so it is **not** quoted here (a previous draft said 68, which reproduced at no
      stable revision: 67 at the authoring commit, 69 and 70 at the two after it). What is
      load-bearing is the API, measured by diffing the **declaration lines** of
      `Codec/Normal.lean` at both revisions:

      `Normal`, `Normalizer`, `fill`, `fill_raw`, `fill_fixed`, **`fill_surj`**, `fill_inj`,
      `decodeNormal`, `decodeNormal_of_fixed`, `decodeNormal_encode` — **identical names and
      signatures at both**. The two files differ in **docstring prose only** (29 insertions / 9
      deletions, from `codec-audit-round-nine` §4), which does not affect the pin. A previous
      draft claimed the files were "identical", which is false and is the repo's own
      stated-method defect; the declaration-line diff is the check that matters.

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

- [x] 0.6 Re-read `design.md` D2 (codomain is the quotient) and D5 (padded tails are out of
      scope). Both are the decisions a careless implementation gets wrong, and both are
      stated as requirements so the gate can catch them.

- [x] 0.7 Do **not** `git stash` / `git reset` / `git checkout -- <file>`. Commit per
      section **in `../lean-basen`**, whose history is separate from this repo's — a commit
      here does not commit a `BaseN/` edit, and vice versa. `AGENTS.md` records that a stash
      has destroyed verified work in this ecosystem.

## 1. [M] The generic layer — `digitVal`, `toNat`, `ofNat`

Findings: `design.md` D0/D1. The whole change rests on this section being right.

- [x] 1.1 Create `BaseN/Radix.lean` with `digitVal (radix : Nat) (b : UInt8) : Option Nat`.
      It SHALL accept the RFC 4648 alphabets for 16/32/64, the bit/quartet/octal digit
      alphabets for 2/4/8, and decimal digits for 10 — **one** function, not a dispatch on
      hand-rolled copies. Prove it agrees with each base's existing **digit-value** function
      (`bitVal`, `quartetVal`, `octToVal`, `hexToNibble`, `b32ToVal`, `b64ToVal`, `digVal`)
      at that radix: **7 equalities, decode direction only**.

      **Do not attempt to unify the encode direction.** `valToBit b := if b = 0 then 48 else
      49` (`BaseN/Base2.lean:49-50`) is deliberately non-injective — the module's own
      docstring says the sentinels differ on purpose, are sound only because every use
      supplies `b ≤ 1`, and "Do not 'fix' one sentinel to match the other".
      `valToQuartet`/`valToOct` have the same shape. `ofNat` is this change's own encoder; it
      is not claimed to be a copy of the three at 2/4/8.

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

- [x] 1.2 `toNat (radix : Nat) (ds : List UInt8) : Option Nat` — the most-significant-first
      fold `acc := acc * radix + d`. Total on valid sequences; `none` on any out-of-alphabet
      byte, and **not** partially converted. State and prove the fold's recursion equation
      as its own lemma (`AGENTS.md`: `unfold` does not reduce a `match`-def at a variable
      argument).
- [x] 1.3 `ofNat (radix : Nat) (n : Nat) : List UInt8` — canonical digits, minimal, no
      leading zeros, and `ofNat radix 0` is that radix's **single zero digit** (D4). Prove
      `toNat radix (ofNat radix n) = some n` and `ofNat (toNat radix ds)` returns the
      canonical form, i.e. the round-trip pair at the heart of the `Iso`.
- [x] 1.4 Mutation-test 1.2 and 1.3: reverse the digit order in `toNat` and confirm the
      round-trip proofs fail. A round-trip pair that survives a reversed fold is not
      constraining anything.

### Session 1 landed — MEASURED 2026-11-14

`BaseN/Radix.lean` and `BaseN/RadixAlphabets.lean` are committed in `../lean-basen`
(`c1cfe50`). The gate went from `490 = 444 + 46` / 25 jobs to
**`533 = 484 + 49` / 27 jobs** — the job count rising by two is the evidence the two
new modules are actually compiled (§0.4's failure mode).

What the commands settled, which is the part worth carrying:

| claim                                           | how it was checked                                   | result                                             |
| ----------------------------------------------- | ---------------------------------------------------- | -------------------------------------------------- |
| `toNat 10` of `"300"` is `300`                  | `#eval`                                              | `some 300`                                         |
| `toNat 2` of `"01100001"` is `97`               | `#eval`                                              | `some 97`                                          |
| round trip at all seven radices                 | `#eval` over `0,1,7,37,255,1000,123456` × 7          | all `true`                                         |
| zero is one digit, not empty                    | `#eval ofNat b 0` × 7                                | `[48]` … `[65]` (base 32's alphabet starts at `A`) |
| out-of-alphabet rejects, not partially converts | `toNat 8 [0x39]`, `toNat 16 [0x47]`, `toNat 10 "7x"` | `none`, `none`, `none`                             |

**Two corrections to the plan's derived prose, both found by the compiler:**

1. **`ofNat`'s `n+1`-then-drop-the-head trick is wrong as written.** Taking the
   _tail_ of `n+1`'s digits gives `300 + 1 = 301`'s digits `[3,0,1]`, whose tail is
   `[0,1]` — the number 1, not 300. Measured with `#eval` before the theorem was
   attempted. The shipped `ofNat` spells `0` as the zero digit and otherwise maps
   `natDigits radix n`, which is minimal by construction.
2. **`Classical.choice` leaked from `omega` on a _conjunction_, not only a
   disjunction.** §4.5 of this file records the disjunction shape; the conjunction
   form is the same trap in different dress: `inWin_iff.2 (by omega)` for a goal
   `lo ≤ c ∧ c ≤ hi` reports `[propext, Classical.choice, Quot.sound]`, while
   `inWin_iff.2 ⟨by omega, by omega⟩` is clean. Five laws leaked this way and all
   five were fixed; the final measurement is **zero** `Classical.choice` in the
   module, and three laws report no axioms at all.

**§1.4's mutation test, run.** A right-to-left fold over the same alphabet returns
`some 3` for `ofNat 10 300` where `toNat` returns `some 300`, so the round-trip law
constrains the fold's direction rather than holding vacuously.

**§3.2's probe, run and thrown away.** The plan's D6 claim — that the block isos are a
_canonicality-filtered restriction_ and not an equality — was checked directly against
base 10 rather than trusted:

```
digBlockApply "255" -> some 255      toNat 10 "255" -> some 255      (agree)
digBlockApply "999" -> none          toNat 10 "999" -> some 999      (do NOT agree)
```

So an equality really is false and the implication pair is the right shape. That is
the one derived claim this session tested, and it held.

**Not done, and the gate is green without them:** `numeralIso` (§2), the seven ties
(§3.2), §4.2/§4.2b's allowlist trim, and §5/§6. §4.1's pinning _was_ done — 40 new
`#guard_msgs` blocks and 40 `gatedNames` entries — because the coverage arm fails the
build without it, which is the "cannot be left half-done" rule this file opens with.

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

## 3. [M] The seven radices, and the block isos tied to the fold

Findings: `design.md` D5/D6.

- [ ] 3.1 Instantiate `numeralIso` at radices 2, 4, 8, 10, 16, 32, 64. Each SHALL carry its
      `2 ≤ b` witness explicitly. Enumerate the seven from one source in the gate so a
      missing radix is a build failure rather than a shorter list.
- [ ] 3.2 Prove, for **each of the seven** bases, that its block iso is tied to `toNat` by
      the **canonicity-filtered implication pair** of `design.md` D6 — _not_ an equality.

      Seven, not six: `digBlockIso` (`BaseN/Base10.lean:250`, base 10) is the same shape and
      the first draft silently dropped it, which is an unexplained 6-of-7 list.

      The statement is NOT `blockIso = toNat` restricted, and attempting that will fail:
      `b64BlockApply` re-encodes and compares (`Base64.lean:265-270`), `digBlockApply`
      rejects `n > 255` (`Base10.lean:121-128`), and the `UInt8`-valued bases truncate via
      `UInt8.ofNat`.

      **Two schemas, not one — a single `BlockVal` placeholder does not typecheck.** The seven
      split by codomain: `bitBlockIso`/`quartetBlockIso`/`octBlockIso`/`digBlockIso`/
      `hexBlockIso` are `Iso (List UInt8) UInt8` (schema `_8`, consequent
      `some (UInt8.ofNat n)`, losslessness from the block's `n < 256` guard);
      `b32BlockIso`/`b64BlockIso` are `Iso (List UInt8) (List UInt8)` (schema `_L`, consequent
      `some (bytesOfNat n)`, `→` held by base 64's re-encode guard rather than a range bound).
      See `design.md` D6 for both statements.

- [ ] 3.3 **Mutation-test every 3.2 theorem** by perturbing that block iso's digit order
      and confirming it fails naming that base. Seven theorems, seven mutations.
- [ ] 3.4 Record, in the module docstring, that `numeralIso` is **not** defined through the
      padded bases' `B32`/`B64` tail spine (D5), and why — padding there encodes a _length
      class_, which a minimal-width numeral does not have. State it where a future
      implementer will reach for `b64BlockIso`.
- [ ] 3.5 **Reconcile `BaseN.lean`'s design sentence.** `BaseN.lean:20-22` states: _"There is
      **no** `Base` enum and **no** `encode (b : Base)` / `decode (b : Base)` facade: the
      radix lives in the value the caller already holds, **never on a dispatch index**."_
      `toNat : (radix : Nat) → …` puts the radix on exactly such an index.

      The *spirit* survives — no `Codec`-level dispatch replaces `Codec.decode` — but the
      *letter* does not, and leaving the sentence unreconciled is the "a claim whose stated
      method is not its code's method" class this ecosystem has closed six times. Amend the
      docstring in this change to say the radix-parameterised functions are a **numeral
      helper layered above** the per-base `Codec` values, and that no `Codec`-level dispatch
      was introduced.

## 4. [M] The gate — and `basen`'s gate is NOT `codec`'s

Findings: review `gate-coverage` M-1/M-2/M-3. **Measured, because the first draft of this
section described `codec`'s machinery and `basen` does not have it.**

- [ ] 4.1 Pin every new law **by hand**. There is **no generator here**:

      ```
      ls ../lean-basen/scripts/            -> No such file or directory
      grep -c 'BEGIN GENERATED' Axioms.lean -> 0
      grep -n 'BEGIN PINNED' Axioms.lean    -> 2061   # a HAND-WRITTEN list, not generated
      ```

      `lean-codec` has `scripts/gen-axioms.lean` and a `checks.mirror` guard; `basen` has
      neither. So "regenerate" — which this task said in its first draft — is a **`codec`
      construct with no referent in the target repo**. The actual loop, per new theorem:

      1. add a `#guard_msgs` / `#print axioms` block by hand, exactly as the existing 444 are;
      2. add the name to `BaseNAxioms.gatedNames` (the `BEGIN PINNED` list, `Axioms.lean:2066`);
      3. let the coverage arm tell you if you missed one — it fails the build naming every
         public `BaseN` theorem that is in neither `gatedNames` nor `generatedAuxAllowlist`,
         with the message `theorems not pinned by this gate`.

      That coverage arm **is** the enforcement. Nothing regenerates; the list is maintained.

- [ ] 4.2 **Drop the seven block isos from `definitionSurfaceAllowlist`** — and **keep three**.
      This is the task the first draft did not have; the second draft's version of it was
      ambiguous, which is why it is now an explicit name list.

      The allowlist region is `Axioms.lean:1922-1946` (the `def` at 1922, not 1920). It holds
      **ten** `Iso`-law-as-field entries, not seven. **Remove exactly these seven:**

      ```
      `BaseN.Base2.bitBlockIso        (:1925)
      `BaseN.Base4.quartetBlockIso    (:1926)
      `BaseN.Base8.octBlockIso        (:1927)
      `BaseN.Base10.digBlockIso       (:1928)
      `BaseN.Base16.hexBlockIso       (:1929)
      `BaseN.Base32.b32BlockIso       (:1931)
      `BaseN.Base64.b64BlockIso       (:1933)
      ```

      **Keep exactly these three, each with its current reason:**

      ```
      `BaseN.Base16.hexBlockIsoF      (:1930)  -- Iso UInt8 (Normal ...), not a block
      `BaseN.Base32.b32TailIso        (:1932)  -- a tail; D5 puts tails out of scope
      `BaseN.Base64.b64TailIso        (:1934)  -- likewise
      ```

      §3.2 generates no theorem for those three, so their reason ("no theorem names it")
      **stays true** and they pass both the `both` arm (`:2860`) and the `stale` arm
      (`:2849`). Removing them would make the `silent` arm fire naming them — the arm working,
      but a wasted build caused by this task's own wording.

      **Why it is safe to leave them:** a def that is allowlisted and *unmentioned* is in
      neither `both` nor `silent`; only a def that is **mentioned and allowlisted** trips
      `both`. That is the state the seven move *into*, and the three must stay out of.

- [ ] 4.2b **Record the reason where it moves.** `Axioms.lean:1699`'s prose says "the 15
      allowlisted are 10 `Iso`-law-as-field values"; after 4.2 that is "15 − 7 = 8 allowlisted,
      of which 3 are `Iso`-law-as-field" — re-derive from the list, do not paste. The
      "no theorem names it" justification is now false of the seven **by design**, so the
      header prose must say the seven have a constraining theorem instead.

- [ ] 4.3 Update **every** asserted constant the gate checks — there are **11**, in **four**
      arms, not "the header counts":

      | arm | constants | line |
      | --- | --- | --- |
      | theorem table | `expectedPub`, `expectedGated`, `expectedAllow` | `Axioms.lean:2742-2744` |
      | header prose | `statedPrintBlockCount`, `statedGatedNamesCount` | `:2784-2785` |
      | footprint distribution | `statedDistPS`, `statedDistP`, `statedDistZ` | `:2817-2819` |
      | def table | `expectedDefs`, `expectedMentioned`, `expectedDefAllow` | `:2866-2868` |

      plus the header prose tables they mirror (`:1655-1700`). `stated := 12`
      (`:2905`, the bench `native_decide` count) does **not** move.

      **Worked example — and the first version of it was wrong in three ways**, so read the
      caveats as the content:

      - **"+7" counts NEW theorems, not the existing `*_law`s.** Each base already has a
        `bitBlockIso_law`-style theorem; §3.2's pair is *additional*. And the pair is an
        **implication pair**, so a base may contribute **2** new theorems, making the delta
        `+14` rather than `+7`. Count against the build; this example is the shape, not the
        number.
      - **`expectedMentioned +n` / `expectedDefAllow −n` are arithmetically automatic** — the
        arm computes `mentionedCount := defs.size - allow.size` (`:2858`) — **but semantically
        conditional**: they only move if each new theorem's *statement names the iso value*.
        If a theorem names `bitBlockApply` instead of `bitBlockIso`, the seven stay unmentioned
        and the `silent` arm (`:2852`) fires naming them. That is exactly what the `both` arm
        exists to verify, so it belongs here as a caveat rather than a footnote.
      - **It is `statedDistPS`, and three constants move with it** — not "one bucket". The
        distribution is `distPS + distP + distZ == baseNPins` (`:2830`), so a new
        `[propext, Quot.sound]` law moves `statedDistPS` **and** `statedPrintBlockCount`
        **and** `statedGatedNamesCount`.

      So: `expectedPub`, `expectedGated`, `statedGatedNamesCount`, `statedPrintBlockCount` and
      `statedDistPS` all move by the number of new pinned theorems; `expectedDefAllow` moves by
      minus the number of *named* isos. Re-derive from `lake build`.

- [ ] 4.4 **State the two posture greps and run them** before pinning. Measured baseline
      today, which the new module must not break:

      ```
      grep -rn 'native_decide' --include=*.lean ../lean-basen/BaseN/
        -> 0 in BaseN/. The 12 sanctioned uses are in Bench.lean and are asserted by the
           gate at Axioms.lean:2905; do not add a 13th.

      grep -rn '\bsorry\b' --include=*.lean ../lean-basen/BaseN/ ../lean-basen/Axioms.lean
        -> 3 hits, ALL docstring prose (the phrase "zero `sorry`" at Base64.lean:15,
           Base32.lean:13 and :3655). The task is "no `sorry` TERM", not "no match" —
           a literal zero-grep would fail forever on the prose that documents the rule.
      ```

- [ ] 4.5 Every new law stays `[propext, Quot.sound]`-only: `#print axioms` per law family.
      **All three** recorded leak shapes apply (`AGENTS.md`), not the two the first draft
      named — the third, a `match`/`if` on a `Bool` in the goal, is exactly what 2.4's
      rejection laws and 1.3's `ofNat` are shaped like.

      Measured this session, so the expectation is evidence rather than hope:
      `Nat.div_eq`/`Nat.div_add_mod`/`Nat.mod_lt`/`Nat.div_lt_self` are all
      `[propext, Quot.sound]`, and `Codec.fill_surj`/`fill_inj`/`decodeNormal_encode` are
      `[propext]`-only. Meanwhile `omega` closing a **disjunction** leaks `Classical.choice`
      (measured live), and the explicit `Or.inl`/`Or.inr` form does not. Rejection laws are
      `Option`-and-disjunction shaped — use the explicit form.

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
