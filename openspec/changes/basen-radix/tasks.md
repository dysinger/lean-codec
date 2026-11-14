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
> Legend: **[M]** MUST, **[S]** SHOULD.

## 0. Preconditions

- [ ] 0.1 In `../lean-basen`, confirm the tree is clean and the gate is green **before**
      any edit: `git status --porcelain` empty, `nix develop --command lake build` passes
      with zero `sorry`/warnings, and `Axioms.lean` prints its six gate lines with every
      asserted count matching.
- [ ] 0.2 Re-read `design.md` D2 (codomain is the quotient) and D5 (padded tails are out of
      scope). Both are the decisions a careless implementation gets wrong, and both are
      stated as requirements so the gate can catch them.
- [ ] 0.3 Read `../codec/Codec/Normal.lean` in full before writing the `Iso`. The layer
      being reused is `Normal`/`Normalizer`/`fill`/`decodeNormal`; its docstring is the
      statement of the thesis this change depends on. **Read `fill_surj` especially** — it
      is what makes every lax spelling reach a canonical form.
- [ ] 0.4 Do **not** `git stash` / `git reset` / `git checkout -- <file>`. Commit per
      section; `AGENTS.md` records that a stash has destroyed verified work here.

## 1. [M] The generic layer — `digitVal`, `toNat`, `ofNat`

Findings: `design.md` D0/D1. The whole change rests on this section being right.

- [ ] 1.1 Create `BaseN/Radix.lean` with `digitVal (radix : Nat) (b : UInt8) : Option Nat`.
      It SHALL accept the RFC 4648 alphabets for 16/32/64, the bit/quartet/octal digit
      alphabets for 2/4/8, and decimal digits for 10 — **one** function, not a dispatch on
      hand-rolled copies. Prove it agrees with each base's existing alphabet function
      (`bitVal`, `quartetVal`, `octToVal`, `hexToNibble`, `b32ToVal`, `b64ToVal`, `digVal`)
      at that radix, so `design.md` D1's "proved-equal specialisation" is a theorem and not
      a claim.
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
      warnings, all gate lines green.
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
