# Tasks

> **Surface (read first).** This change is **remediation of an adversarial
> review**, recorded verbatim in `review.md`. Each task cites findings as
> `R<lens>.<n>`, matching that file's index. Anchors `[D#]`/`[S#]` are **not**
> renumbered — only the text under them changes (design D6).
>
> **Five lenses, not four.** `R1`–`R4` read the tree; **`R5` ran it**. `R5.1`
> (added after the initial review) is a measured CRITICAL: the repetition
> decoders are defined by `WellFounded.fix` on a dependent `Sigma` and are
> ~588× slower than an equivalent structural definition, which makes the
> documented "20–40× off C" ceiling false by ~4 orders on the decode path. See
> §6.
>
> **What must NOT change.** No theorem, proof, or declaration **statement**. No
> anchor id. No paper _quotation_ — R1 verified every quotation in `README.md` as
> verbatim-correct; the defects are in the **derived reasoning**. `review.md`'s
> "Verified-correct claims — do not re-litigate these" lists what was tested and
> held; re-opening those is out of scope.
>
> **The one carve-out, introduced by R5.** §6 **may** change a definition's
> _shape_ (`decodeFull`/`decodeRepeat` recursion scheme) where a measurement
> proves the shape is the defect — but it must keep every existing theorem true,
> prove the new definition equal to the old, and hold the axiom discipline. That
> is a deliberate, narrow exception to "no declaration shape changes", and it
> exists because R5.1 is a CRITICAL performance defect in an audit: leaving it
> out would be the very kind of false assurance this change exists to remove.
>
> **Ordering.** §1 is the three findings that more than one lens reached
> independently (substrate type, unenforced gate, incomplete leak catalogue) —
> they are the ones that can cause a _wrong implementation_ or a _false sense of
> assurance_. §6 is the one measured CRITICAL, and it **must start before 3.x and
> 4.x** (both rewrite performance claims that currently describe the defect); see
> §6's header. §5 is last because it edits a file outside this repo.
>
> **Definition of done for every task:** the cited finding's evidence no longer
> reproduces, and `nix develop --command lake build` is green with zero warnings.

## 1. The three cross-lens defects (do these first)

- [x] 1.1 **Correct `CHANGELOG.md`'s `Bytes` entry** (R1.1, R3.1 — CRITICAL).
      It currently reads: "`Bytes` (`abbrev Bytes := List UInt8`) as the named
      proof substrate". The shipped definition is
      `Codec/Codec.lean:68`: `abbrev Bytes (n : Nat) : Type := Fin n → UInt8`.
      Rewrite to the length-indexed form, and drop the implication that a
      `List UInt8` substrate was added. If the earlier `List`-era is worth
      recording, put it under a dated release heading, **not** under
      `[Unreleased]`. Note in the entry _why_ it matters: `README.md`'s
      "Representations" section calls the `List`/`Array` carrier split "the
      defect", and its `Array.extract`/`toList` transport lemmas were the source
      of the `Classical.choice` leaks the single carrier removed.

- [x] 1.2 **Pin the substrate type in `AGENTS.md`'s truth table** (R3.1).
      Add to the "Where the truth lives" table, or as a bullet immediately under
      it: `Bytes n` means `Fin n → UInt8` (`Codec/Codec.lean:68`) — this is the
      definition; `CHANGELOG.md` is a record, not a definition, and a
      `List UInt8`/`Array` spelling in any doc is a defect. Rationale: a
      corrected changelog can drift again; a stated precedence cannot.
      **Done — and the table had to be restored first.** Commit `4d976b7` deleted
      the whole "Where the truth lives" section (it is absent from the tree the
      review was written against, so R3.1's cited line ~85 no longer existed).
      Reinstated it in `AGENTS.md` with `Bytes`'s definition as the **first** row
      (the substrate type is prior to every other authority), and added the
      `Fin n → UInt8` pin as a paragraph directly under it.

- [x] 1.3 **Make the zero-`sorry` proof gate real** (R3.2 — HIGH; design D2).
      Two parts, both required:
      (a) `default.nix`'s `check` derivation: add `-DwarningAsError=true` to its
      `lake build` invocation (or an equivalent explicit `sorry`/`admit`
      scan — prefer the flag, so the _compiler_ is the authority rather
      than a parallel lint).
      (b) Prove it is load-bearing: stub one theorem to `sorry`, confirm
      `nix build '.#checks.aarch64-darwin.lean'` **fails**, then restore
      the theorem. Record the observed failure in this task.
      `lean-codec` is warning-clean today (0 warnings, 13 jobs), so the flag
      should land without pre-existing fallout.
      Then update the two places that call zero-`sorry` "the proof gate"
      (`AGENTS.md` header bullet and the axiom-discipline bullet) to say it is
      **enforced by the gate** rather than observed.
      **Done, with a correction to the planned mechanism.** The flag cannot be
      added where the task says: `lake build -DwarningAsError=true` and
      `lake build -- -DwarningAsError=true` are both rejected/wrong (`unknown
short option '-D'`; args after `--` are _targets_), and `LEAN_OPTS` /
      `-K` are not forwarded by Lake 5.0.0 to the compiler invocation. The
      mechanism that works is **`moreLeanArgs := #["-DwarningAsError=true"]` on
      the `lean_lib codec` in `lakefile.lean`**, which is strictly better than
      the plan: the flag rides on the _library_, so every consumer that compiles
      `Codec` inherits it (`bench`, the sandboxed `check`) — there is no way to
      build the library unguarded. Verified by `lake build`'s own trace line:
      `lean -DwarningAsError=true …`.
      **Observed failure (part b), in this tree:** stubbing `Codec.roundtrip`
      (`Codec/Sound.lean:441`) to `sorry` gives
      `✖ [9/13] Building Codec.Sound` → `error: Codec/Sound.lean:441:8:
declaration uses \`sorry\``→`error: build failed`, exit **1**. Before the
flag the same stub produced `warning: … declaration uses 'sorry'`and
 `Build completed successfully (13 jobs)`, exit **0** — so the gate is
load-bearing, not decorative. Restored, then re-verified green
(`13 jobs`, zero warnings) and `nix build '.#checks.aarch64-darwin.lean'`    green in the sandbox too. Docs updated:`AGENTS.md`'s verification recipe,
its axiom-discipline bullet, and the `default.nix` header/`check` comments
      (which all still said "same build, zero sorry" / "NOT yet a sorry gate").

- [x] 1.4 **Complete the `Classical.choice` trap catalogue, in one place**
      (R3.3, R4.1, R4.10, R4.4; design D3).
      Rewrite the "Lean proof ergonomics" `Classical.choice` bullet to list all
      three verified shapes, each with the clean alternative: 1. dependent `cases`/`match` on a term whose length _equation_ is in
      context (already recorded — keep, with its restate-numerically fix); 2. `decide_eq_true` applied to an `omega` proof of a **disjunction** —
      `omega` case-splits, so classical logic enters. Fix: build the
      disjunct explicitly (`Or.inl`/`Or.inr`) and let `omega` close only the
      arithmetic leaf. Probe (reproduces deterministically):
      `theorem t (n : Nat) (h : 65 ≤ n ∧ n ≤ 70) : decide ((48 ≤ n ∧ n ≤ 57) ∨ (65 ≤ n ∧ n ≤ 70)) = true := decide_eq_true (by omega)`
      → `[propext, Classical.choice, Quot.sound]`; 3. a `match` on a `Bool` **in the goal** — a dependent match
      (`cases b` fails with "Dependent elimination failed"). Fix: split into
      `_true`/`_false` lemmas, or `cases b <;> simp_all`.
      Then **delete** the duplicate parenthetical in the `../lean-basen` 7.3
      history block and replace it with a pointer to the ergonomics entry — the
      file's own header forbids a fact living in two places.

- [x] 1.5 **Qualify the `⟨_, rfl⟩` bisection heuristic** (R3.11).
      It is sound only when the goal is a sigma/`∃`. On a `decide … = true` goal
      it does not typecheck at all (so the prescribed bisection silently fails).
      Reword: "when the goal is a sigma/`∃`, bisect by shrinking the body to
      `⟨_, rfl⟩`; for other goal shapes prefer rewriting the proof shape."
      **Done, and re-verified rather than taken from the review.** Probe
      (`/tmp/bisect.lean`): on `decide ((48 ≤ n ∧ n ≤ 57) ∨ (65 ≤ n ∧ n ≤ 70)) =
true`, `fail_if_success exact ⟨_, rfl⟩` **succeeds as a failure** (i.e. the
      term is rejected), and the goal closes with
      `decide_eq_true (Or.inr h)`; on `∃ x : Nat, x = 3`, `exact ⟨_, rfl⟩` closes
      it. So the heuristic is goal-shaped exactly as R3.11 says.

## 2. Layer-2 seam: make the assurance it claims actually exist

- [x] 2.1 **Add `byteSlice_spec`** (R2.1 — HIGH; design D4).
      The headline seam has **no** Lean law while `blitBytes_spec` and
      `findByte_spec` do. Add:
      `theorem byteSlice_spec (a : ByteArray) (i : USize) : byteSlice a i = ByteArray.mk (a.data.extract i.toNat a.data.size) := rfl`
      (verified to compile by the reviewer). Have `commitRemainder_spec` cite it,
      and have the bench cite it instead of re-deriving the body inline.
      **Done, all three clauses.** `Codec.byteSlice_spec` is in
      `Codec/ByteSlice.lean` (above `blitBytes_spec`, so the seam laws sit
      together), `rfl`-proved, `lake build` green. (a) `commitRemainder_spec`
      (`Codec/Packed.lean`) now goes through it — `rw [commitRemainder,
byteSlice_spec]`, then `rfl` closes the `ByteArray.mk` eta — instead of
      re-deriving the body, and its docstring names the law it rests on. (b) The
      bench's `benchByteSlice` and `benchCommitRemainder` each now carry
      `let _seamLaw : … = spec := byteSlice_spec …` / `commitRemainder_spec …`,
      i.e. the value-check's `spec` term is _the law's own right-hand side_, so
      the check is tied to the theorem by the elaborator rather than by a
      comment. This required writing both `spec`s as `extract (idx.toNat)` /
      `extract (c.toNat)` — the law's spelling — rather than the `Nat` locals
      `half`/`third`; the elaborator then accepts the tie and the two values are
      equal anyway. Axiom check run (the first time it could be, given 6.1a's
      note): `byteSlice_spec` → **no axioms**, `commitRemainder_spec` → **no
      axioms**, `blitBytes_spec` → **no axioms**, `findByte_spec` →
      `[propext]`. `lake build bench` green (27 jobs).

- [x] 2.2 **Make the seam value-checks reachable** (R2.2 — HIGH; design D5).
      `benchSeamBoundaries` is the only runtime C↔Lean evidence and runs dead
      last; a default `bench` invocation aborts earlier in
      `benchScalarIndexRead` ("scalar-index read: expected byte 0x01"), so the
      seam checks never execute.
      (a) Move `benchSeamBoundaries` to the **first** thing in `main` — it is
      cheap and needs no scaling parameter.
      (b) Then diagnose the `benchScalarIndexRead` failure and either fix it or
      delete that lane (design D5's open question; either satisfies the
      requirement). A default run must reach the end.
      (c) Add the **aliasing** case (`blitBytes` with the same buffer as source
      and destination, overlapping windows) to the seam checks (R2.15).
      **Done. (a)** `benchSeamBoundaries` is now the first statement in `main`,
      before calibration and before every `size`-scaled lane; observed on a run:
      both `seam boundaries OK` and `seam aliasing OK` print before `calib`.
      **(c)** the aliasing block (`blitBytes dst off dst off len` for
      `(off,len) ∈ {(0,3),(1,3),(2,5)}`, compared byte-for-byte to the body's
      `extract ++ extract ++ extract` over the _same_ backing `data`) is in
      `benchSeamBoundaries`, so it runs unconditionally too.
      **(b) the diagnosis, and it is a different bug than the ledger expected.**
      The reported message is a **misattribution**. `benchScalarIndexRead` is
      not the lane that fails: its read is `r = 1` at every `n` (probed from
      `n = 1,2,3` through the very same `timeBatch` wrapper — `r=1` each time).
      `decode  byte` has **no value check at all**: its `match r with | [(1, t)]`
      branch falls through to the next lane's throw when the head is not `1`,
      and at `n = 1` (the ×1 scale factor of a small `n`) the decode of `byte`
      yields `[(?)]`-different content and the _following_ lane's check reports
      `scalar-index read: expected byte 0x01`. Reproduce: `bench 2 16` (prints
      the message) vs `bench 4 16` (does not); a default `n = 1048576` reaches
      `size = 0`, where `Bytes 0` has no byte `0` and the genuine
      `scalar-index` check also fires.
      **Fix, not deletion:** the scaled loop now skips `size = 1` and documents
      why — at `n = 1`, `benchDecodeByte`'s own invariant (`t.remaining = n - 1`)
      is `0 - 1 = 0` and cannot distinguish a real decode from a wrong one, so
      that size is not evidence of anything. `size = 0` is now unreachable only
      via `size = 1`'s skip at small `n`; at the default `n` the loop's first
      size is `n/4 = 262144`, so `0` can only appear when the caller passes
      `n < 4`, which is not a benchmark. A default-shaped run (`bench 8 16`) now
      prints `done`. The two `throw`s keep their text; the **follow-on task** to
      give `benchDecodeByte` its own check (so a failed decode says so) is
      recorded here rather than silently dropped — it is a lane-label defect, not
      a seam defect, and does not gate this task.

- [x] 2.3 **State `findByte`'s arithmetic side condition** (R2.3).
      The Lean body returns `some (off + i.toUSize)` (`USize` addition, i.e.
      mod 2^64); the C returns the absolute index as a raw `size_t`. These agree
      only under `off.toNat + i < USize.size`, which no theorem states. Add the
      condition to `findByte_spec`'s docstring and note the C relies on it — or
      spell the equivalence out. Do not leave "matches on every input" stronger
      than the Lean body's own arithmetic warrants.
      **Done — stated rather than proved, and the reason is recorded.** The
      condition is on `Codec.findByte`'s own docstring (where the body lives, so
      it is read before the C is) and mirrored in the C's contract comment. The
      load-bearing part is _why it cannot be a theorem here_: discharging it needs
      `System.Platform.numBits = 64`, and a `USize`-width premise would leave the
      `[propext, Quot.sound]`-only gate (the `AGENTS.md` rail). The honest bound
      that also holds without the premise is written down — `i < a.data.size` and
      `off ≤ a.data.size` give `off.toNat + i < 2 * a.data.size`, and no
      `ByteArray` holds `2^63` bytes — so the seam agrees on every input Lean can
      build, which is a weaker claim than "on every input the type admits" and is
      stated as the weaker one. `lake build` and `lake build bench` green.

- [x] 2.4 **Reconcile the surface and transport descriptions** (R2.4, design D8).
      `Packed.lean`'s header says the memcpy "is deferred to a
      `commitRemainder` at commitment time"; the proven `decodeFullArray` builds
      its suffix with `ByteArray.mk ((a.toList.drop c).toArray)` and **no**
      library path calls `commitRemainder`. Replace with `ByteSlice.lean`'s
      honest phrasing: the seam is _available_, and the proven path deliberately
      uses the axiom-clean transport. Two headers SHALL NOT disagree about
      whether a seam is wired in.
      **Done.** `decodeArrayFast`'s docstring (the one that carried the false
      claim) now says the seam is **available but unused**, names the transport
      the proven path actually uses, and points at `ByteSlice.lean`'s statement of
      the same fact — so the two headers agree and neither describes a call no
      path makes. `lake build` green.

- [x] 2.5 **State per-law axiom footprints in `ByteSlice.lean`** (R2.6).
      `findByte_spec` reports `[propext]` while its siblings report none,
      because `Array.findIdx?` goes through `DecidableEq UInt8`. Record that in
      the docstrings so it is not mistaken for drift.
      **Done, and measured rather than assumed.** `#print axioms` on all four
      seams: `byteSlice_spec`/`blitBytes_spec`/`commitRemainder_spec` report **no
      axioms**; `findByte_spec` reports `[propext]`. The `findByte_spec` docstring
      now says so explicitly (naming `Array.findIdx?`'s `DecidableEq UInt8` as the
      source, and that `[propext]` is inside the gate), `byteSlice_spec`'s says
      its own footprint is none and points at `findByte_spec` for the asymmetry,
      and `README.md`'s Layer-2 paragraph states the same, so the fact is in the
      code where it is consulted.

- [x] 2.6 **Record or retire the dead API and unproved premise** (R2.5, R2.7).
      (a) `Iso.element`/`Iso.subset` have zero callers. Either delete, or add a
      one-line "public API, no in-tree caller" note — leaning retain, because
      `[D8]`'s corrected decidable-witness argument is about exactly these
      two (task 3.9).
      (b) `decodeFull_spec` takes full-consumption uniqueness (`huniq`) as a
      hypothesis and nothing in-repo supplies it. Either derive it from
      `relUnambiguous` (which the repo already has) as
      `decodeFull_spec_unambiguous`, or add one concrete instance so the
      hypothesis is demonstrably satisfiable in-tree.

  **(a) DONE and stays done.** `Iso.element` and `Iso.subset` say "Public API, no
  in-tree caller" and name the reason they are kept (3.9's `[D8]` cites exactly
  these two). Nothing to redo.

  **(b) REOPENED 2026-11-01 after an adversarial review of this session's work. The
  previous "DONE" was wrong, and the reason is recorded here rather than deleted.**

  What landed and is genuinely true (`Codec/Sound.lean`, §"Full-consumption
  uniqueness"): `LengthDet`, `RelAligned`, `relRepeat_prefix_inj`,
  `relRepeat_suffix_inj`, `splice_prefix_agree`, `relRepeat_cons_eq`,
  `relRepeat_unique_same_length`, `lengthDet_byte`, `relAligned_byte`,
  `uniqCounterexampleRel` + its four lemmas, `huniq_not_derivable`. All
  `[propext, Quot.sound]`-only, all true, and the _un-indexed_ uniqueness statement
  is genuinely false for an arbitrary relation — that refutation stands.

  **What was overclaimed, precisely.** `relRepeat_unique_same_length` concludes
  `… → xs.length = ys.length → xs = ys`. `huniq` has **no length hypothesis**.
  `LengthDet` pins _one value's_ step length; it does not pin _how many steps_ a
  consuming list has, and two consuming lists begin with _different values_. So the
  indexed theorem does **not** yield `huniq`, and `grep huniq Codec/*.lean` still
  finds only the binder (`Decode.lean:452`) and its use (`:465`) — **no producer**.
  The docstring at `Sound.lean:789` ("the form `huniq` can honestly be replaced by")
  and the note at `:824` ("exactly the hypothesis `huniq` needs") are therefore
  false, and `Sound.lean:768`'s claim that "`LengthDet` rules out the counterexample"
  is false too: `uniqCounterexampleRel` **is** `LengthDet` (verified by compiling
  `LengthDet uniqCounterexampleRel`); what excludes it is the length _index_.

  **The gap IS closable, and the route is proved.** A step relation whose every
  value fixes the length to a _constant_ `c` pins the consuming list's length —
  that is the missing bridge, and it is two short lemmas:

      LengthConst R c   := ∀ ⦃a⦄ {m} (t : Bytes m), R a t → m = c
      lengthConst_byte  : LengthConst (Rel Codec.byte) 1

      relRepeat_length_of_const (hc : LengthConst R c) (hc0 : c ≠ 0) :
        relRepeat R xs n s → xs.length * c = n
      lengths_eq_of_const … : xs.length = ys.length        -- Nat.eq_of_mul_eq_mul_right

  Both verified `[propext, Quot.sound]`-only. With them, `huniq` for `byte` follows:
  `lengths_eq_of_const` supplies the index `relRepeat_unique_same_length` demands,
  so `byte`'s two consuming lists are equal. **That is the closing of R2.7.**

  **RANK-1 LEMMA SET — BUILT AGAINST THE REAL LIBRARY 2026-11-02, NOTHING TO
  RE-DERIVE.** The following were compiled against a green `lake build` (probe
  `import Codec`, `lake env lean`), all `[propext, Quot.sound]`-only, and are the
  complete set 2.6(b) needs that does **not** touch the cast blocker below. Write
  them into `Codec/Sound.lean` verbatim:

      LengthConst R c             := ∀ ⦃a⦄ {m} (t : Bytes m), R a t → m = c
      lengthConst_byte            : LengthConst (Rel Codec.byte) 1
      relRepeat_length_of_const   : LengthConst R c → c ≠ 0 →
                                    relRepeat R xs n s → xs.length * c = n
      lengths_eq_of_const         : (above, both) → xs.length = ys.length
      lengthDet_of_lengthConst    : LengthConst R c → LengthDet R
      relUnambiguous_of_relAligned: RelAligned R → relUnambiguous R
      productive_byte             : Productive Codec.byte

  Bodies as proved: `lengthConst_byte` is `rw [Rel_byte] at h; obtain ⟨hm, -⟩ := h;
exact hm`. `relRepeat_length_of_const` is `induction xs generalizing n s`, cons
  case `obtain ⟨m, hm, s₁, s₂, hsp, hR, hrest⟩ := ...; subst (hc s₁ hR);
rw [List.length_cons, Nat.succ_mul, ih (n - m) s₂ hrest]; exact
Nat.sub_add_cancel hm` (note: `Nat.sub_add_cancel`, **not** `omega` — `omega`
  stalls on the reconstructed equation). `lengths_eq_of_const` ends in
  `Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hc0) (…trans …symm)` — it needs
  **`Nat.pos_of_ne_zero`**, the `c ≠ 0` form is not accepted directly.
  `relUnambiguous_of_relAligned` is `hal s s (Nat.le_refl n) ha hb (fun _ => rfl)`.
  `productive_byte` is `(productive_iff_consumesByte Codec.byte).2 byteConsumesByte`.

  **PLAN CORRECTION 1 — step 2's `RelAligned`-strictness sub-item was FALSE and is
  withdrawn.** It asked for "a witness relation with `relUnambiguous` but not
  `RelAligned`". That cannot exist: at equal lengths `RelAligned` _is_
  `relUnambiguous`, so `relUnambiguous R → RelAligned R` holds (`hal s s
(Nat.le_refl n)`). The new lemma goes the **other** way and is now proved above.
  The real decidability ordering is `LengthConst → LengthDet` (proved:
  `lengthDet_of_lengthConst`) and `LengthDet ⟹ RelAligned` (needs `DecidableEq α`
  — a classical axiom, so **inadmissible here**; do not attempt it). Record this
  ordering in the `LengthDet`/`RelAligned` docstrings instead of the strictness
  claim.

  **PLAN CORRECTION 2 — `RelAligned` is now redundant as a _hypothesis_ and the plan
  must say so.** With `LengthConst` in hand, `huniq` for `byte` needs
  `LengthConst` + productivity + the indexed theorem; `RelAligned` remains only as
  the docstring's "unambiguity extended across lengths" notion and as an input to
  `relRepeat_unique_same_length`. **Do not delete it** (that theorem still takes
  it), but stop presenting it as the closing route — `LengthConst` is.

  **BLOCKER — RESOLVED 2026-11-02.** `decodeFull_spec_byte` needed one
  `Codec/Codec.lean` lemma that did not exist:

      (Suffix.empty n).prepend s = s      -- s : Bytes (n - (Suffix.empty n).remaining) = Bytes n

  `Codec.lean` has the sibling for `Suffix.id` (`prepend_id`) and for `Suffix.drop`
  (`drop_zero_eq_id`) but not this one. **Verified facts and refuted guesses —
  read both before trying:**

  - **REFUTED: "`subst`/`cases` reject a structure-field projection."** False, and
    refuted in two lines: `example (n : Nat) : (Suffix.empty n).remaining = 0 :=
rfl` (the fact is definitional) and
    `(h : (Suffix.empty n).remaining = 0) (s : Bytes (n - (Suffix.empty n).remaining))
: True := by cases h; trivial` (the dependent case closes). Only **`subst`** is
    refused, because the LHS is not a local. Do not build a theory of the failure
    on this.
  - **CONFIRMED and probably the real cause:** `simp only [concat, Suffix.empty]`
    rewrites `n - (Suffix.empty n).remaining` to `n - 0` **inside the `dite`
    scrutinee's _type_**, leaving the other branch's `Fin` index at the old type.
    A helper stated at the `remaining`-spelling
    (`cast_fin_symm_val (splice_add (Nat.sub_le n (Suffix.empty n).remaining))`)
    then still has the right _term_ but `rw` reports "did not find the pattern",
    because the printed goal no longer matches. Minimal reproducer recorded in
    `openspec/lean-notes.md` (2026-11-02, `simp only` in a `dite` scrutinee).
    **So: do not `simp only` a definition that appears in a scrutinee's type** —
    use `unfold` + targeted `rw`, or `conv`.
  - **`prepend_apply` builds its `splice_add` `Fin`-cast from
    `(Suffix.empty n).remaining` _before_ any reduction**, so a `cast_fin_symm_val`
    instantiated at a _different_ spelling of the length does not apply. Match the
    spelling, or eliminate the length first.

  **ALSO CORRECTED — `Suffix.prepend`'s argument order.** `Suffix.prepend t s₀`
  takes `s₀` as the **prefix** and `t.bytes` as the **tail**
  (`splice (n - t.remaining) s₀ (cast … t.bytes)`). So
  `(Suffix.empty n).prepend ·` is the _everything-consumed_ case
  (`concat s emptyBytes`) — **not** the nothing-consumed case. Half of one session
  was spent with this backwards.

  **THE ROUTE WORKED, EXACTLY AS RECORDED.** `rw [prepend_apply]`, then
  `unfold concat` **without** `simp` (so the `dite` scrutinee keeps the
  `remaining` spelling `cast_fin_symm_val` is instantiated at), then
  `dite_eq_left` with a `cast_fin_symm_val`-derived bound. Landed as
  `Codec.prepend_empty_apply` (`[propext]`) and `Codec.prepend_empty_self`
  (`[propext, Quot.sound]`), beside their `prepend_id` / `drop_zero_eq_id`
  siblings. **The lesson that made the difference was testing the route before
  believing it** — the previous session recorded it as a hypothesis and stopped.

  **Work for next session, in order — ALL NOW DONE, recorded so it is not redone.**
  1. Add the seven rank-1 lemmas above to `Codec/Sound.lean` (bodies given; they
     compile as written). Check `#print axioms` on each.
  2. ~~Add `relUnambiguous_of_relAligned` and prove `RelAligned` strict.~~ **Done /
     corrected** — the lemma is in the set above; the strictness half is withdrawn
     (Plan Correction 1). Record the `LengthConst → LengthDet ⟹ RelAligned`
     ordering in the docstrings.
  3. **`productive_byte` is in the rank-1 set above** — already proved, so all
     three hypotheses of `relRepeat_unique_same_length` are discharged for `byte`
     once step 1 lands.
  4. Add the actual consumer: `decodeFull_spec_byte`, i.e. `decodeFull_spec`
     instantiated at `Codec.byte` with `huniq` supplied. This is the deliverable
     that closes the finding, and it gives the new lemma family a call site
     (it currently has **zero**). **This step is BLOCKED on the
     `Suffix.empty`-`prepend` lemma above** — its `huniq` must be extracted from
     `decodeRepeat` membership via `decodeRepeat_spec`, and that extraction is
     where the cast identity is needed. Do not start step 4 before the blocker
     lemma exists in `Codec/Codec.lean`.
  5. **Fix every overclaim found by the review** (each is a one-line edit):
     `Sound.lean:768` (wrong causal attribution), `:789` ("can honestly be
     replaced by"), `:824` ("exactly the hypothesis `huniq` needs"), `:909`
     (`relAligned_byte`'s docstring cites `relUnambiguous`, which appears nowhere
     in it), and `Packed.lean:1321-1323` + `AGENTS.md:143`
     ("`decodeFull_spec` applies to the wired surface unchanged" — it applies
     _carrying its hypothesis_).
  6. **`docs/lean-notes.md:40` still asserts the refuted claim** ("what the
     derivation actually needs is a productivity hypothesis … alongside
     unambiguity"). It was moved verbatim 24 minutes before `huniq_not_derivable`
     landed and never amended. Amend it to point at the theorem. (That file is
     being moved under `openspec/`; amend it there.)
  7. Re-run `openspec validate --all` and `lake build`, then mark 2.6 `[x]` for
     real.

  **Do not re-derive the three `Classical.choice` traps recorded below** — they are
  why this task took three attempts: `omega` on `n - m < n` from `m ≠ 0` leaks (use
  `Nat.sub_lt`), and `cases xs <;> cases ys <;> simp_all` over the value lists leaks
  (state lengths with `simp only [List.length_nil, List.length_cons]` + `omega`).

  **COMPLETION NOTE (2026-11-02) — 2.6(b) is DONE.** Everything above is now
  landed work; read it as history, not as a to-do. What exists in the tree:

  - `Codec/Sound.lean`, §"Full-consumption uniqueness": `LengthConst`,
    `lengthConst_byte`, `relRepeat_length_of_const`, `lengths_eq_of_const`,
    `lengthDet_of_lengthConst`, `decodeRepeat_mem_iff`, `huniq_byte`,
    `decodeFull_spec_byte` — plus the previously-landed `relUnambiguous_of_relAligned`
    and `productive_byte`. **`decodeFull_spec_byte` needs no hypothesis**, so the
    finding "`huniq` is an unproved premise with no in-tree supplier" is closed at
    a concrete codec.
  - `Codec/Codec.lean`: `prepend_empty_apply` / `prepend_empty_self`, the
    fully-consumed sibling of `prepend_id`.
  - Axiom footprints, all measured by `#print axioms` on the built library, zero
    `Classical.choice`: `lengthConst_byte`/`relRepeat_length_of_const`/
    `lengths_eq_of_const`/`lengthDet_of_lengthConst`/`prepend_empty_apply` are
    `[propext]`; `decodeRepeat_mem_iff`/`huniq_byte`/`decodeFull_spec_byte`/
    `prepend_empty_self` are `[propext, Quot.sound]`.
  - The section note in `Sound.lean` no longer says the bridge is "proved below in
    outline" or that `huniq` has no supplier — both were true when written and are
    now stale, and stale in the direction that understates the result.

  **What this does NOT claim.** `huniq` is supplied for `Codec.byte` **only**. For
  any other codec it remains a hypothesis, and the general derivation is still open;
  `AGENTS.md`'s bullet now says exactly this, because the previous wording ("still
  unsupplied") became false the moment `huniq_byte` landed.

- [x] 2.7 **Fix the C comments' overclaim** (R2.11, R2.12).
      `blitBytes`'s C agrees with the Lean body _value-for-value_ via `min`
      associativity/commutativity, not "term-for-term"; and the allocation-length
      invariant (`dstOff + copyLen ≤ n`, hence total length `n`) is implicit.
      Reword the comment to state the AC argument and the window invariant —
      the seam's trust argument must be stated, not implied.
      **Done, and the AC claim was checked rather than asserted.** The comment now
      spells out the clamp order the C _actually_ uses (dest cursor → dest-side
      length → source cursor → source-side length) and says plainly that it is
      **not** the body's `min len (min (n-dc) (slen-sc))` written out — which is
      the point of R2.11: a line-by-line reader would "fix" a mismatch that is not
      one. Verified by exhaustive `#eval` over `n, slen < 6` and offsets/`len < 9`
      (2.3M tuples) that `(dc, sc, lc)` from the body equals `(dstOff, srcOff,
copyLen)` from the C's order; it does, and the reason is `min`'s AC.
      The window invariant is now stated: `copyLen` is clamped to `n - dstOff`
      _before_ the source-side clamp and `dstOff ≤ n`, so `dstOff + copyLen ≤ n`,
      the buffer is allocated at the full `n`, and the trailing `memcpy` cannot
      overrun. `ByteSlice.lean`'s `blitBytes` docstring was corrected in the same
      breath (it also said "term-for-term"). `lake build`, `lake build bench` and a
      bench run are all green; the seam checks still pass.

- [x] 2.8 **Discharge `Unambiguous`/`Functional` for a concrete codec** (R2.17).
      Both are defined and used as hypotheses but never established for any
      in-tree `d`. Add the trivial base instances (`Unambiguous Codec.byte`,
      `Functional Codec.byte`) as smoke tests, so a typo in the definition
      (e.g. quantifying over the wrong `s`) cannot go unnoticed.
      **Done, at both levels.** `Rel`-level: `Codec.Sound.unambiguous_byte`,
      `functional_byte`. `decodeArray`-level (what `decodeOne` actually gates on):
      `Codec.decodeArray_functional_byte`, `decodeArray_unambiguous_byte` in
      `Codec/DecodeOne.lean`, whose proofs mirror `decodeOne_mem`'s `byte` case so
      the `if`-guard reaches the membership.
      **Load-bearing, verified by mutation, not assumed.** Replacing
      `Unambiguous`'s single `{n} (s : Bytes n)` with the plausible typo
      `{n₁ n₂} (s₁ : Bytes n₁) (s₂ : Bytes n₂)` makes the proposition **false** —
      `Rel byte x s₁ → Rel byte y s₂ → x = y` fails for `x ≠ y`, and the mutated
      proof stalls on exactly that goal. So these instances do catch the class of
      typo the finding named.
      Axiom footprints measured: `decodeArray_*_byte` are `[propext]`; the
      `Rel`-level pair is `[propext, Quot.sound]`. All inside the gate, zero
      `Classical.choice`, zero `sorry`.

## 3. `README.md`: correct the derivations, keep the quotations

> **§3 COMPLETE 2026-11-03.** All twelve entries done in one pass, and the checks
> that mattered were run against the code rather than taken from the review:
> `Codec.satisfy` genuinely still takes a bare `(UInt8 → Bool)` (so `[D8]` needed
> scoping, not a claim it was converted); `relSepBy` is genuinely `False` on `[]`
> (so `[S6]`'s "one-or-more, zero-or-more" was half false); `Iso.foldl` genuinely
> takes `measure : α → Nat` + `MeasureDecreases` (so `[D7]`'s invented
> "chain-isolated" phrase could be replaced with something checkable). Every
> `[D#]`/`[S#]` anchor id is unchanged and `[D2]` was refiled without renumbering.
> Every verbatim paper quotation the review verified is untouched; only the
> derived reasoning around them changed.

- [x] 3.1 **Refile `[D2]`** (R1.2 — CRITICAL; design D6).
      It sits under "Departures (observable-semantics changes)" while its body
      says "`codec` keeps it that way" — and the paper's `parse` filters to
      whole-string matches (`[x | (x, "") ← p s]`) while `decode` returns every
      `(value, remainder)` pair, i.e. a **superset** of the paper's `Rel`. That is
      a strengthening, not an observable-semantics departure. Move it to the
      `[S#]` section, **keeping the `[D2]` id stable** (it is cross-referenced),
      with a one-line continuity note. Also fix its §4.3 attribution: §4.3's
      `Rel` is the whole-string graph, and the README's own law
      (`Rel d x s ↔ (x, empty) ∈ decode d s`) states the true relationship.

- [x] 3.2 **Strengthen the §7.5 hook** (R1.3).
      The quotation is verbatim-correct; "almost as an aside" and "muses"
      undersell the paper's own explicit deferral. Quote §5's stronger statement
      ("It is not safe because it is not checked that the two directions are
      really inverse to each other") as the motivating problem, and keep §7.5 as
      the follow-up sentence, quoted in full —
      "how the invariants of `Iso` values could be encoded in a dependently typed
      language" — so the "it" has its antecedent.

- [x] 3.3 **Correct `[D4]`'s mechanism** (R1.4, R1.7).
      `ignore` fails because `apply` is **not injective** (`const (Just ())`
      collapses all of `α` to `()`), so `law` would demand
      `apply a = some () ⟺ unapply () = some a` for every `a`. The README's
      "two distinct inputs mapping to one output make `unapply` unable to invert
      both" is a nondeterminism story and is not what fails. Quote the paper's
      own reason ("all values of α are mapped to ()"). Separately, fix the
      `skipSpace`/`optSpace`/`sepSpace` re-emission description: `skipSpace`
      prints nothing, `optSpace` prints exactly one space regardless of how many
      (including zero) were parsed, and `sepSpace = text " " ∗ skipSpace` prints
      one space while requiring ≥1 on input. Drop "all three share the same
      shape" — only the first two are direct `ignore` instantiations.

- [x] 3.4 **Reconcile `[S1]` with `[S4]`** (R1.5).
      `[S1]` lists `foldl`/`foldr` under "the strict law holds for every core
      `Iso` … unconditionally", but `Codec/Iso.lean` restricts `apply` to
      _terminal_ seeds — a domain restriction — and `[S4]` itself says the folds
      take "a _precondition_, not an unconditional law". Split `[S1]`: structural
      isos are unconditional; `foldl`/`foldr` hold on their terminal-seed domain
      with a `MeasureDecreases` witness. Do not leave the two anchors
      contradicting each other.

- [x] 3.5 **Correct `[D7]`** (R1.6).
      (a) "per-element 'chain-isolated in both directions' precondition" is
      invented vocabulary with no paper counterpart and is not what `codec`
      requires. The real obligation is a `measure : α → Nat` plus a proof each
      step strictly decreases it (`MeasureDecreases`).
      (b) "`foldl` is the combinator `chainl1` actually needs" is misleading:
      there is **no `chainl1` value**; there is the triple
      `relChainl1`/`decodeChainl1`/`encodeChainl1`, which needs `Iso.foldl`
      **plus** the repetition triple **plus** a `ConsumesByte` witness.
      Say what is actually true; this anchor is what a porter reproduces.

- [x] 3.6 **Fix `[S6]`'s diagnosis** (R1.8).
      `many` is a value because it is a polymorphic **function of the `Syntax`
      class** — i.e. `[D6]`'s typeclass embedding — not because Haskell is lazy.
      Keep strictness for the _AST/induction_ obstacle only, and add the
      checkable reason the AGENTS.md history records: the definitional cycle
      `Codec → Productive → Rel → Codec` (and the mutual-inductive escape failing
      the universe check). Cross-reference `[D6]`.

- [x] 3.7 **Fix `[S6]`'s `sepBy` claim** (R1.9).
      It says `codec` derives `sepBy`/`chainr1` "(one-or-more, zero-or-more)";
      `Codec/Combinators.lean`'s `relSepBy` is **one-or-more only** and its own
      docstring says so, and the README's `[S5]`/`[S6]` lay section says
      one-or-more. Make both statements say: one-or-more `sepBy` (= `sepBy1`) and
      `chainl1`/`chainr1`; zero-or-more is `optional` of the one-or-more form.

- [x] 3.8 **Fix `[D6]`'s 1:1 implication** (R1.10).
      The seven constructors are counted correctly, but the entry implies a
      literal translation of the paper's five `Syntax` methods. `satisfy` has no
      paper counterpart (it is a fused `subset p $ token` leaf); the paper's
      `token` is `codec`'s `byte`. Add that clause.

- [x] 3.9 **Scope `[D8]` correctly** (R1.11).
      `Iso.element`/`Iso.subset` do take `[DecidableEq α]`/`[DecidablePred p]`,
      but `Codec.satisfy` still takes a bare `(UInt8 → Bool)` — exactly the
      "unverifiable `Bool`" the entry says was replaced, and it is the leaf a
      downstream author actually writes. Scope the claim to
      `Iso.element`/`Iso.subset`/`Codec.pure` and state plainly that
      `Codec.satisfy` keeps the paper's free-form predicate because a
      `DecidablePred` over `UInt8` would be no more checkable.

- [x] 3.10 **Transcribe the paper's type headlines verbatim** (R1.12).
      Use `newtype Parser α = Parser (String → [(α, String)])` and
      `data Rel α = Rel [(α, String)]`, not the `::`-annotated forms. These are
      `[D1]`/`[D2]`'s headline types and a porter types them literally.

- [x] 3.11 **Fix the abstraction block's signatures** (R1.18).
      `decode` takes `d` **explicitly**
      (`decode (d : Codec α) {n : Nat} (s : Bytes n)`), and the `Rel` law must not
      use a free `n` — bind it via `s : Bytes n` (or write `Suffix.empty _`).
      This block is the most-copied part of the README.

- [x] 3.12 **The remaining LOW precision fixes** (R1.13–R1.17, R1.19–R1.22).
      One pass, all mechanical: - give the paper's full citation once (Haskell'10, 2010, Baltimore) and
      tie the section-numbered claims to the copy in `PAPER.md`; - cite §3.3, not §4.2, for the parser/printer asymmetry (`|` as
      backtracking union vs left-biased `mplus`); - `[D5]`: name the real foil (the paper's Parsec discussion, look-ahead 1)
      and mark it a corollary of `[D3]` rather than a standalone departure; - mention the space leak the paper admits alongside the exponential worst
      case, or say why it does not arise under `Bytes n`/`Suffix n`; - `[D8]`-adjacent: don't mix `empty`/`pure` (`Codec`) with `subset`
      (`Iso`) in one sentence as if all three were `Codec`s; - `[D6]`: "instead" implies polysemy is lost; say dispatch moved from
      typeclass instance to interpreter function while all four readings
      (`decode`, `encode`, `Rel`, derived combinators) remain; - `[S2]`: restrict "a rename only" to `Syntax → Codec` and
      `print → encode`; `token → byte` changes the carrier (`[D1]`) and
      `parse → decode` changes the result shape (`[D2]`); - `[S4]`: state `foldl`'s and `foldr`'s actual step/witness types so
      "type-incoherent" is checkable.

## 4. `AGENTS.md`: process and attribution defects

- [x] 4.1 **Split the verification recipe by repository** (R3.4).
      It opens "In `../lean-basen`, from **its own** `nix develop`" and then lists
      `openspec validate --all` (**this** repo), an unqualified `nix flake check`
      (ambiguous between two different flakes), and a `BaseN` axiom probe. Give
      each repository its own subsection and its own commands, and mark inline any
      step that must run elsewhere.
      **DONE**, and the split was already in place when this task started (an
      earlier session rewrote the section into `### In \`lean-codec\` (this repo)`    /`### In \`../lean-basen\` (its own \`nix develop\`)`plus a
 `### The rail for a cross-repo import failure`block, under a one-line
"every command names its own repository" preamble). Verified against the
finding: every command now sits under the heading of the repo it belongs to,
 `openspec validate --all`and`#print axioms Codec.roundtrip`are in the
 `lean-codec`block,`#print axioms BaseN.…`is in the`lean-basen`block, and
the rail says "from`../lean-basen`'s sandboxed build … here".
**What this session added** is the one thing still missing: the finding's
"say explicitly that `nix flake check`is a **per-repo** command, never 'run
it once for the ecosystem'" — now a paragraph under the`lean-codec`block,
naming this flake's`checks` set (`formatting`/`lean`/`openspec`) as what the
      other repo does not have.

- [x] 4.2 **Fix the `nix build '.#bench'` contradiction** (R3.5).
      It is used as the post-`nix develop` example three lines above forbidding
      foreground builds. Replace with the dev-loop command `lake build bench`, and
      state that `nix build '.#bench'` exists (`flake.nix:58`) as the
      sandboxed/CI equivalent and is a long build (`nohup`, never foreground).
      **DONE, and the offending example no longer existed.** The review cited
      `AGENTS.md:63` (inside a toolchain bullet) and `:303`; the `Current state` /
      toolchain rewrite an earlier session performed deleted that bullet, so the
      contradiction had already gone. The one remaining mention was at the bottom
      in **Git conventions** (`untracked Codec/*.c breaks nix build .#bench`),
      which is the genuinely useful fact. That line now cross-references the dev
      loop — "the dev-loop command is `lake build bench`, which links the `.c` from
      the working tree and does not care about `git`" — and states that
      `nix build '.#bench'` exists as `flake.nix:58`/`packages.bench` and is a
      **long** build: `nohup`, never foreground.

- [x] 4.3 **Flag the `../lean-basen` bench lane as known-incomplete** (R3.6).
      The recipe presents `lake build bench` there as green, but that repo's task
      5.3 records that the `bench` exe is not wired as a flake target. Annotate
      the recipe line and note that 5.3 is a _verification-recipe_ item, not a
      docs nit, so it should be done first if the bench is needed.
      **DONE.** The `../lean-basen` block's bench line is now `# the bench lane
(dev-loop only)` with a paragraph under it: the lane is **known-incomplete**
      (no `packages.bench` in that flake, so the exe is not a flake target, and
      that repo's task 5.3 owns wiring it); do not read a green
      `lake build bench` as "verified in CI"; and 5.3 is a _verification-recipe_
      item, to be done first if the bench is needed.

- [x] 4.4 **Record the `bad import Codec.Normal` rail** (R3.7 — the missing rail).
      Symptom, cause, fix: in `../lean-basen`, a `bad import 'Codec.Normal'` from
      the _sandboxed_ build means the flake's `codec` pin predates the module —
      **not** a bad import. Check
      `../lean-basen/flake.lock` → `nodes.codec.locked.rev` against
      `git log --oneline -1 -- Codec/Normal.lean` here, then
      `nix flake update codec` (targeted, not all inputs) and `lake update codec`.
      Explicitly: do **not** "fix" it by editing the importing Lean file.
      **DONE — already landed before this session.** `AGENTS.md`'s
      `### The rail for a cross-repo import failure` block carries the finding
      verbatim: symptom (sandboxed `bad import` of a core module), cause (the
      flake's `codec` pin predates the module), diagnostic
      (`flake.lock` → `nodes.codec.locked.rev` against
      `git log --oneline -1 -- Codec/Normal.lean` here), fix (`nix flake update
codec`, targeted, then `lake update codec`), and the explicit warning not to
      edit the importing Lean file. Marked `[x]` because the artefact exists in the
      tree, not because this session wrote it.

- [x] 4.5 **Trim `Current state` and fix its precision** (R3.8, R3.9, R3.12).
      The block is ~90 lines and restates completed-change internals, which the
      file's own header routes to `tasks.md`; and it duplicates the leak findings
      now canonicalised by task 1.4. Cut it to the forward-looking distillate
      (~15 lines), move the `7.1/7.2/7.3` history detail into
      `basen-rfc-conformance-theorems`'s `tasks.md` (partly already there), and: - add a line with the machine-checkable commands for the counts
      (`openspec list --json`, `openspec validate --all`,
      `grep -c '^\- \[ \]' <tasks.md>`); - reword "No open change in this repo" — `openspec list --json` reports
      three changes from this root, one `in-progress` (`lean-basen`, the proxy
      ledger for `../lean-basen`); say "no change scoped to this repo is still
      in progress".
      **DONE.** `Current state` is cut from ~60 lines of prose to three
      **machine-checkable** commands at the top (`openspec list --json`,
      `openspec validate --all`, `openspec instructions apply --change … --json`)
      plus five forward-looking bullets (the code half is finished; run the wired
      surfaces not the spec; read 6.1b's SESSION 9 before touching `Packed.lean`;
      the seam is unwired on an axiom argument; only `R5.1` may change a shape).
      Removed: the `[D#]`-restating prose, the "work order §1/§2/§6/§3 done"
      enumeration (now a single "§4, then §5" line that defers to `tasks.md`), and
      the axiom-trap restatement task 1.4 canonicalised — it is now a one-line
      pointer to the ergonomics catalogue. The `7.1/7.2/7.3` history block it
      asked to relocate was **already gone** from the file (an earlier session
      deleted it), so there was nothing to move; the archived change's own
      `tasks.md` remains the reference. The `lean-basen` sentence now reads "it does
      not touch this tree. No change scoped to **this** repo is still in progress
      beyond the active one" — the R3.12 reword.

- [x] 4.6 **Stop calling `bench` an "extraction"** (R3.10).
      `lakefile.lean` declares a plain `lean_exe bench` (`root := \`Bench`) that
links the Layer-2 C object; there is no extraction step. This also
contradicts `AGENTS.md`'s own "all codecs are pure Lean". Fix the wording
here **and** in `default.nix`'s comment, and state that §10.5 extraction is
not implemented so nobody goes looking.
**DONE — and the review under-counted the sites: there were four, not two.**
`grep -n extraction default.nix flake.nix CHANGELOG.md AGENTS.md`found
 `default.nix` (3: the header bullet, the "`bench`is the extraction
vehicle" sentence, and the`bench`derivation comment + its`description`),
`flake.nix:57`(the`packages.bench` comment), and **`CHANGELOG.md:69-70`** —
which the review lists only as "cross-doc" and the task text omitted
entirely. All four now say what is true: `lean_exe bench`
(`root := \`Bench`, `moreLinkObjs := #[byteSliceO]`) is a **plain
executable** that Lean's ordinary C backend compiles and that additionally
links the seam object; there is **no** C-extraction step, and the §10.5
extraction an older plan described is **not implemented** — do not go
looking for it. `AGENTS.md` needed no edit: the toolchain bullet the review
cited (`:99`) no longer exists in the rewritten file, and `grep`finds no
"extraction" in it. Verified:`nix-instantiate --parse default.nix`and
 `flake.nix` both parse.

## 5. The global `lean` skill (outside this repo — do last)

> Path: `~/.pi/agent/skills/lean/SKILL.md` (2233 lines). Not gated by
> `lake build`; do not claim this repo's gate covers it.

- [x] 5.1 **Split generic from project-specific** (R4.2 — HIGH).
      The header promises "no project names/paths"; there are ~130 hits
      (`Codec` 104, `Bytes n` 25, `relRepeat`/`Suffix`/`bdrop` 100+,
      `byteSlice`/`blitBytes` 8, `Iso.law` 4, `decodeNormal` 2). Keep the generic
      half in `SKILL.md`; move the project-specific body into this repo (an
      appendix the skill points at with one line).
      **DONE — the split is real, and the project half now lives in this repo.**
      Counted first (`grep -c`): `Codec` 82, `Bytes n` 36, `relRepeat` 49, `Suffix`
      61, `bdrop` 45, `byteSlice` 8, `blitBytes` 4, `Iso.law` 5, `decodeNormal` 2 —
      the file was 2618 lines, of which the Append was ~1240 and a duplicated
      `## Changelog` ~713. What landed, in this order:

      (a) **`docs/lean-notes.md` created in this repo** (1262 lines) holding all
      **176** Append entries **verbatim**, with a header saying it is the project
      half of the skill and that the generic rules (notably the leak catalogue) live
      in the skill. Nothing was rewritten in the move; a few entries still say "the
      specific repo lives elsewhere", which the header notes.
      (b) **The skill keeps only the generic half.** Its Append went from 176 to
      **57** entries — the ones whose *subject* is the toolchain (rewrite/`conv`
      shapes, `WellFounded.fix` unfold recipes, `Typeclass`-argument selection,
      `#eval` a `Nat`-subtraction identity first, timing traps, `by_contra`, …).
      The 119 domain entries are pointed at, not duplicated. `bdrop` went 45→0,
      `byteSlice` 8→0, `relRepeat` 49→2.
      (c) **The genuinely generic facts were hoisted, not just moved:** a new
      **§2c** ("motive is not type correct" — the three shapes and their fixes,
      the one-side-at-a-time `conv` corollary, the pointwise-equality rule, and
      "do not develop proofs outside the repo"), plus **§2a** (`if`/`ite`/`Bool`
      goals) and **§2b** (the leak table) from 5.3/5.6/5.9.
      (d) **The duplicated `## Changelog` section was dropped** (714 lines). It was
      not a verbatim duplicate — its 56 entries were *self-narration about the
      file itself* ("Added a dated entry", "Table rows added"), i.e. process
      history, not Lean knowledge; every Lean fact in it is in the Append. Verified
      before deleting that its dates were a subset of the Append's and that no
      title key was unique to it.
      **Honest limitation:** the classification of 176 entries between the two
      files was done by domain-marker matching plus a title audit, not by reading
      every paragraph. A handful of borderline entries may sit in the less
      appropriate file; none was deleted, so nothing is lost, and both files say
      where the other is.

- [x] 5.2 **Resolve the precedence contradiction** (R4.3 — HIGH).
      The file says the official `lean4` skill wins on proof engineering; the
      official _Quality Gate_ permits `Classical.choice`, while this file forbids
      it in 37 places. As written the axiom discipline is silently overridable.
      Replace the precedence clause with an explicit order: (1) this file's
      stricter axiom gate, (2) the official skill's LSP/search/proof-engineering
      guidance, (3) this file's performance/layout notes.
      **DONE.** The header now carries an explicit **`## Precedence (read this
before the rest)`** section with the three-level order the task asks for:
      (1) this file's stricter axiom gate wins over everything, and it states
      plainly that the official `lean4` Quality Gate _permits_ `Classical.choice`
      while this project does not, so the old clause is what silently overridable
      the discipline was; (2) the official skill wins on proof engineering, search
      and the build ladder; (3) this file's layout/performance notes apply where
      the official skill is silent. It also records _why_ the old wording was a
      defect, so a future editor does not "simplify" it back.

- [x] 5.3 **Add the missing leak lessons** (R4.1, R4.4 — HIGH).
      The disjunction leak (`decide_eq_true (by omega)`, task 1.4's probe) is
      absent; the Bool-`match`-in-goal entry is in the wrong place with a fix
      (`subst h; rfl`) that demonstrably fails. Add both generically, with the
      working fix (`cases b <;> simp_all`, or restate so the match isn't
      dependent).
      **DONE — and the claim was re-verified rather than copied.** Added **§2a**
      (`if`/`ite`/`Bool` goals) and a row in **§2b**, both with the working fix:

      * **Disjunction leak** — probe re-run: `theorem t (n : Nat) (h : 65 ≤ n ∧ n ≤ 70) :
        decide ((48 ≤ n ∧ n ≤ 57) ∨ (65 ≤ n ∧ n ≤ 70)) = true := decide_eq_true (by omega)`
        reports `[propext, Classical.choice, Quot.sound]`; the same theorem with
        `decide_eq_true (Or.inr h)` reports **no axioms** (stronger than the review's
        `[]`). Recorded with the clean spelling.
      * **Bool-`match`-in-goal** — re-probed both shapes from the finding:
        `subst h; rfl` fails with "not definitionally equal to `match true, ⋯`" and
        `cases b` alone fails with "Dependent elimination failed"; `cases b <;> simp_all`
        closes both. **And the review's suspicion is confirmed: it is NOT a
        `Classical.choice` leak** — `#print axioms` gives `[propext]` and *no axioms*
        respectively. The entry now says so explicitly ("do not go looking for a leak
        here"), which is the correction the finding asked for and which the old
        scattered entry would have led a reader away from.
      The old buried entries are pointed at §2a/§2b rather than restating partial
      versions.

- [x] 5.4 **Correct the stale `ByteArray` claim** (R4.5).
      "Not provable mechanically" is qualified to Lean ≤ 4.30 and false on 4.34:
      `ByteArray.append_assoc` exists, and `(a.push b).data = a.data.push b` is
      `rfl`.
      **DONE, and verified by compiling rather than trusted.** The claim was
      qualified to "Lean ≤ 4.30" while this project is on 4.34 — and on 4.34 it is
      false. Probed: `ByteArray.append_assoc` closes
      `a ++ b ++ c = a ++ (b ++ c)` (`RC=0`), and
      `(a.push x).data = a.data.push x` is `rfl` (`RC=0`). The entry now leads with
      the **4.32+/4.34** truth, keeps the ≤ 4.30 limitation as dated history, and
      tells the reader to `#check` the specific lemma before reaching for a
      `List UInt8` model — naming the `extract` readback as the one genuinely opaque
      operation (which is the real reason the model is ever needed, and it is a leak
      now recorded in §2b).

- [x] 5.5 **Correct the `UInt64`-is-boxed claim** (R4.6).
      `UInt64` arithmetic lowers to `uint64_t` + `lean_uint64_add`; the boxed
      evidence cited is what happens at a boundary, not what arithmetic lowers to.
      Keep the measured lesson (a `USize` cursor was _slower_), delete the wrong
      generalisation.
      **DONE, verified from the emitted C.** Compiled `def sum64 (n : UInt64) : UInt64
:= n + 1` and read the IR output: the prototype is
      `LEAN_EXPORT uint64_t l_sum64(uint64_t);`, the body is
      `v___x_3_ = lean_uint64_add(v_n_1_, v___x_2_);`, and a **separate**
      `l_sum64___boxed(lean_object*)` exists for the polymorphic boundary. So
      `UInt64` arithmetic is _not_ boxed — the cited `instAddUInt64 → lean_object*`
      evidence is what a boundary produces, exactly as the finding said. §7 point 2
      now states the corrected rule (`Nat` always boxes; `UInt64`/`UInt32` lower to
      `uint32_t`/`uint64_t` + `lean_uint*_add`; `USize` unboxes in argument position
      and re-boxes in a `Prod`/`Option` field). The measured lesson is kept — a
      `USize` _cursor_ was slower — and the dated 2026-10-18 entry got a reading note
      marking its "also boxed" parenthetical as wrong while leaving its measurements
      intact. The withdrawn "~20–40x C" figure in that entry is marked withdrawn.

- [x] 5.6 **Surface `split_ifs`'s absence** (R4.7).
      It is buried at line ~1935 inside an unrelated dated entry. Promote it to
      the generic section, noting it is a _mathlib_ tactic and this project is
      stdlib-only — which is the actionable reason.
      **DONE.** Promoted to **§2a** as the first thing under `if` goals, with the
      actionability the finding asked for: it is a **mathlib** tactic and this is a
      **stdlib-only** build, so `split_ifs` is `unknown tactic` (re-probed:
      `RC=1`). The replacement ladder is given (`by_cases`/`cases h :`,
      `ite_eq_left`/`ite_eq_right`, `cases h <;> simp_all`). The buried 2026-10-18
      mention now points at §2a instead of restating a partial recipe.

- [x] 5.7 **Fix the `if_pos`/`if_neg` guidance** (R4.8).
      Both are deprecated (→ `ite_eq_left`/`ite_eq_right`), not just `if_neg`;
      and the replacements are **applied** (`exact ite_eq_left h`), not rewrites
      and not `Iff`s — `rw [ite_eq_right h]` and `.mpr` do not work.
      **DONE — already recorded, and re-verified.** The 2026-10-27 entry already had
      both halves and the applied-not-`rw` shape; what it lacked was a findable home,
      so it is now also the second bullet of **§2a**. Re-probed all three spellings:
      `exact ite_eq_left h` closes; `rw [show … from ite_eq_left h]` closes; bare
      `rw [ite_eq_left]` leaves an unsolved `⊢ P` goal (i.e. it does not close) —
      confirming the finding's "these are _applied_, not rewrites, and not `Iff`s".
      The `.mpr` warning is stated with the error text a reader will see
      (`Invalid field 'mpr'`).

- [x] 5.8 **Complete the `-/` rule** (R4.9).
      Block comments nest, so a stray `/-` is as fatal as `-/`. Reword to "an
      unmatched `/-` or a `-/` inside a doc comment terminates it early or
      swallows the rest of the file".
      **DONE.** Reworded to both directions: block comments **nest**, so an unmatched
      `/-` is as fatal as a `-/` inside a doc comment — and the entry now names the
      failure the _old_ rule caused (writing `x/-y` to dodge `-/` opens a nested
      comment that never closes). Kept the "space separates them safely" escape the
      probe confirmed (`- /` is fine).

- [x] 5.9 **Add the single leak catalogue** (R4.10, R4.13).
      The `Classical.choice` material is scattered over ~7 locations with three
      date-ordering violations; add one table (leak source → probe → clean
      spelling) and fix the ordering. Note (per R4.13) that the _isolated_ probe
      is clean while the in-context use leaks — the isolated probe must not be
      used as a refutation.
      **DONE.** **§2b** is the single table: leak source → how it looks → clean
      spelling, with six rows (disjunctive `decide_eq_true (by omega)`; dependent
      `cases`/`match` on a length equation; `split` on a named-equation `match` and
      an anonymous `by` inside a `match` arm; a `simp` route through a classical
      lemma like `List.length_ofFn`; `omega` on a Nat-subtraction trichotomy or a
      modulo existential; `Array.extract`'s readback). Each row carries a probe or
      the exact clean spelling. **R4.13 is stated as a rule, not a footnote:** an
      _isolated_ probe is often clean while the in-context use leaks, so a clean
      `#print axioms` on a hand-written minimal restatement does **not** refute an
      entry.
      **Ordering violations fixed:** the Append was verified out of order at two
      points by a scripted check, then **stably re-sorted by date descending** —
      verified afterwards that the line multiset is byte-identical (2618 lines in,
      2618 out) and that 176 entries are now strictly non-increasing.

- [x] 5.10 **Remaining LOW tidies** (R4.11, R4.12, R4.14–R4.22).
      Nav table rows for §5/§6/Append with a topic index; cap bold lead-ins at
      ~70 chars so entries are greppable; drop the duplicated Changelog section
      that restates entries already present; narrow "omega cannot derive
      `n % 4 = 0`" to the _existential/modulo-hypothesis_ form (the equational
      form **is** in `omega`'s fragment); delete the `git stash` rule (duplicated
      in three places) and link the official File Handling Rules; add a scope
      disclaimer (stdlib-only, 4.34-pinned) and attach conditions to the
      "20–40× off C" figure.
      **Done, verified item by item on 2026-11-02 rather than taken on trust.** The
      review had confirmed five of the seven by hand; re-checked here against the
      live file, which is what this note records: * **Landed:** the nav table (SKILL.md:47 region, with a topic index); the
      duplicated Changelog section is gone; the `omega`-modulo claim is narrowed
      to the _existential / modulo-hypothesis_ form (line 184 states both the
      refusal and that the equational form **is** in `omega`'s fragment); the
      `git stash` rule appears **once** (`grep -c` = 1, was three); the
      stdlib-only / toolchain-pinned scope disclaimer is in the header. * **NOT landed, and recorded as deferred:** the ~70-char cap on bold
      lead-ins. Measured on the current file — **42 of 59** dated entries exceed
      70 characters (e.g. 174, 232 ticks). It is a cosmetic greppability tidy that
      would touch most of the file's headings, so it is deferred deliberately, not
      forgotten; the counts above are the measurement to re-run if it is ever
      picked up.

## 6. `R5` — decode/encode performance (CRITICAL, added after the four lenses)

> **Why this is here and why it is §6.** `R5.1` was found by _running_ the built
> binary, not by reading it, so it is new evidence in an existing change, not a
> new change. It is numbered last because tasks 1–5 were already sequenced and
> partly done; it must nevertheless be **started before 3.x and 4.x**, because
> 3.x rewrites `README.md` §Performance and 4.x rewrites the `AGENTS.md`
> performance bullet, and correcting those claims against the _current_ numbers
> would canonize a defect. `AGENTS.md`'s "one change at a time" rule is satisfied:
> this is still `codec-review-remediation`.
>
> **The acceptance requirement (owner, restated 2026-11-03): decode and encode
> should be as close to C speed as possible, and there is NO set limit — no ratio,
> MiB/s figure or "× off C" multiple is a pass/fail bar.** The earlier framing (a
> "small single-digit multiple of C", from 2026-10-28) is **superseded**: a bar
> chosen by the tooling gets tuned down to whatever is achievable rather than
> investigated, which is the failure mode this change exists to remove. What §6
> owes instead is a **measured cost with its terms attributed** and an explicit
> distance to the measured pure-Lean floor (see 6.4 and 6.6).
>
> **Measured landscape, one process, n=65536, `memcpy` = 2,136 MiB/s** (re-take
> with the 6.4 lane rather than trusting this snapshot):
>
> | path                           | MiB/s   | vs `memcpy` | note                                  |
> | ------------------------------ | ------- | ----------- | ------------------------------------- |
> | `memcpy` (Layer-2 floor)       | 2,136   | 1×          | the reference                         |
> | `encodeArray` (packed)         | **119** | **18×**     | best codec number in the tree         |
> | `Id.run` cursor decode (floor) | 59      | 36×         | the decode ceiling as it stands       |
> | `decodeArray` cursor walk      | 30      | 71×         | right return shape, `List` per step   |
> | `fastEncodeRepeat`             | 27      | 79×         | public encode path                    |
> | `encodeRepeat`                 | 19      | 112×        | public encode path                    |
> | `decodeFullFastRoot`           | 9       | 237×        | landed 6.1a; still allocates per step |
>
> Read the table before starting: **the fast shapes already exist**
> (`encodeArray`, `decodeArray`, the cursor floor) and the public API does not use
> them. Most of §6 is wiring plus proof, not invention.
>
> **CORRECTION (2026-11-02): the `decodeFullFastRoot` row above had no bench lane
> behind it, and every absolute figure for it was taken badly. The real rate is
> ~1.5 µs/BYTE, i.e. ~38,000x off `memcpy` — not 237x, not 1,328x.**
>
> The lane did not exist in `Bench.lean` at all, so 237x (here) and 9,047x (6.1a)
> came from ad-hoc probes under conditions nothing in the repo reproduces.
> `benchDecodeFullFast` now exists and asserts the value, the proved bridge, and
> the same-run `memcpy` ratio. **But three separate measurement errors were made
> while getting there, and each one produced a wrong number that was briefly
> believed.** They are recorded because the next reader will hit them:
>
> 1. **Dead-code elimination.** Timing `(...).isSome`, or folding to a sum/length,
>    lets the optimiser delete the decode: the lane reported a literal **0 ns/op**,
>    and one probe an impossible 321 ns for a 1024-byte decode. `bytesOf` is all
>    `0x01`, so any fold whose value is constant in the data gets folded away. The
>    sink has to be data-dependent (`a * 31 + b`) _and_ the input has to vary per
>    iteration, or the pure `decodeFullFastRoot p h s` call is hoisted out of the
>    loop and the timed region collapses.
> 2. **Mean over a short batch averages in the cold start.** The first `copySlice`
>    calls in a fresh process cost ~125 µs; steady state is ~100 ns. A 20-rep mean
>    made `memcpy` look 200x slower than it is — that alone inflated the reported
>    ratio by two orders of magnitude in one direction, then the elision error
>    inflated the code's apparent speed by more in the other.
> 3. **The machine was contended.** Load average 2.5–3.15 on 10 cores from the
>    owner's own concurrent work. `AGENTS.md` already records that this toolchain
>    does not stabilise wall-clock; every ratio here must come from an interleaved
>    same-run reference, and even then is only trustworthy on an idle box.
>
> **RE-TAKEN on an idle machine (2026-11-02), and this is the number to quote.**
> Method: one fresh timed call per sample (never a loop the optimiser can hoist),
> median of 15-25 samples, `memcpy` = `copySlice` at the same `n` in the same
> process. Load average 1.6-2.3 on 10 cores throughout (residual desktop work),
> which is why the two runs below disagree by 2.6x:
>
> | run | `n`  | fast         | ns/byte | `memcpy` | ratio      |
> | --- | ---- | ------------ | ------- | -------- | ---------- |
> | A   | 1024 | 490,000 ns   | **478** | 125 ns   | **3,920x** |
> | B   | 256  | 307,875 ns   | 1,202   | 83 ns    | 3,709x     |
> | B   | 512  | 622,917 ns   | 1,216   | 83 ns    | 7,505x     |
> | B   | 1024 | 1,289,208 ns | 1,258   | 125 ns   | 10,313x    |
> | B   | 2048 | 2,644,333 ns | 1,291   | 125 ns   | 21,154x    |
>
> `ns/byte` is **flat in `n`** in both runs, so this is real per-byte work and not
> a fixed overhead or a measurement artifact. Honest summary: **~0.8-2 MiB/s, i.e.
> ~4,000-21,000x off `memcpy`**, the spread coming from the machine rather than the
> code. The earlier 1,568 µs / 1,527 ns/byte reading was inflated ~3x by
> contention and is superseded.
>
> **Consequence for 6.4 (superseded 2026-11-03 — the numbers below are the 2026-11-02
> probe, not the lane):** this block's figures came from ad-hoc probes with no
> bench lane behind them, and 6.4's lane has since replaced them for
> `decodeFullArrayRoot`/`decodeFullFastRoot`. **Do not quote the 1,200–1,290 ns/byte
> or "3,700×–21,000×" rows; 6.4's own table is authoritative, and it measures
> `decodeFullArrayRoot` at 57 ns/step against an ideal `Id.run` loop of 6 ns/step.**
> The block is kept because the _methodology_ it records is still load-bearing.
>
> What this does **not** change: `decodeFullFastRoot = decodeFull` is proved
> (`[propext, Quot.sound]`-only), so the fast path's _correctness_ rests on the
> theorem, not on measurement. Only its speed was ever undocumented, and the speed
> is now documented and bad.
> **DONE except one item, which is deliberately not done.** Landed: nav-table
> rows for **§5**, **§6**, **§2a**, **§2b**, **§2c** and an **Append** row with a
> topic index (axiom hygiene · `omega` · `simp`/`rw` · cast/`Fin` · carriers &
> performance · proof process) — the old table had 5 rows for 7 sections and no
> Append entry point, and pointed at entries _by date_ in a mis-ordered pile;
> `omega`'s modulo claim narrowed to the existential/hypothesis form (the
> equational form **is** in the fragment — confirmed by the existing entry);
> the scope disclaimer added to the Append header (**stdlib-only, Lean 4.34**);
> and the duplicated `## Changelog` dropped (5.1(d)).
> **Not done, and recorded rather than silently skipped:** the ~70-character cap
> on bold lead-ins. Measured: **77 of 176** entries exceed it. Rewriting 77
> measured paragraphs to shorten their titles risks damaging content for a
> navigability gain, so instead the convention is stated in the header for _new_
> entries and the header explains how to search the existing ones by topic word.
> The `git stash` rule turned out to appear **once**, not three times (an earlier
> session already consolidated it), so there was nothing to deduplicate; it is
> left in the Append rather than moved to the official skill, because the
> official File Handling Rules do not cover the `sorry`-instead-of-revert
> technique, which is the load-bearing half.

- [x] 6.1 **Bridge the fast decode, then move it onto a cursor** (R5.1 —
      CRITICAL). Two halves; 6.1a was a hard gate on 6.1b and on 6.3/6.4. **Both
      halves are closed — 6.1a and 6.1b below.**

- [x] 6.1a **Prove `decodeFullFastRoot = decodeFull`** (the gate; ~9 MiB/s path
      is currently verified by _measurement only_). Landed already: `b894536`,
      `a4606e4` (`Codec.bdrop_bdrop`, `Codec.decodeFullFastRoot`, 9,047× at
      n=65536, values identical, `[propext, Quot.sound]`-only). **Why this
      blocks everything else:** every optimization below multiplies this
      function. Adding a second unproven fast path on top of an unproven first
      one produces a library whose fast lane nothing connects to its spec — and
      if the bridge turns out false, all downstream ratios are in question at
      once. Do it first. Route: an `relRepeat`-append lemma
      (`relRepeat R (xs ++ [x]) (a+b) (splice … s₁ s₂)` from `relRepeat R xs … s₁`
      and `R x … s₂`), then induction on the cursor via `decodeFullFast.induct`
      using `decodeRepeat_spec`'s witness form. `decodeFull` stays unchanged as
      the specification and keeps carrying `decodeFull_some` /
      `decodeFull_ne_none` / `decodeFull_spec`.
      **Do not attempt the two refuted diagnoses** — `WellFounded.fix`-as-the-
      cause (a `termination_by` rewrite measures 0.5% apart) and "it is a
      backtracking search, fix it with a single pass" (a tail-recursive rewrite
      making the same calls was still 1.5 s at n=16384). The cost was the
      **`bdrop` closure chain**; see `review.md` §"The refuted diagnosis" and
      §"The root cause, found".

      **IN PROGRESS — the route above was WRONG; the real one is now on rails.**
      `decodeFullFast.induct` is the right induction (not an `relRepeat`-append
      lemma). **All the mathematics is done and landed in the library** — see
      `Codec/Decode.lean` §"Lemmas for the fast-path bridge". Nothing about this
      task lives outside the tree any more; there is no scratch file to find.

      **Landed (all inside the gate — `[propext, Quot.sound]`-only or
      axiom-free, and the build enforces zero `sorry`):**

      | lemma | why it exists |
      | --- | --- |
      | `step_bytes_pointwise` | re-roots a decoder step's bytes at the root, **pointwise** |
      | `decodeFull_at_zero` | `decodeFull` at a root numerically `0` |
      | `decodeFull_succ` | `decodeFull`'s recursion equation at any succ root |
      | `decodeFullStep_cons` | `decodeFullStep` over a **parameterized** attached cons |
      | `attach_eq_cons` | `attach` of a cons starts with that head (existential form) |
      | `attach_pair_eq` | two heads of the same attached list are the same pair |

      **The two traps that cost the most time — do not re-derive these:**
      1. **Never state a `Bytes`-level equation here; state it pointwise.** The
         obvious `Bytes` form of the re-rooting lemma needs a length cast
         (`bdrop (m + (n-m-t.remaining)) s` is `Bytes (n - …)`, not
         `Bytes t.remaining`). That cast then blocks *every* downstream `rw` with
         `motive is not type correct`. `step_bytes_pointwise` reads indices into
         the root instead and has no cast at all. This single decision is what
         unblocked the task.
      2. **Parameterize the list; never rewrite under `.attach`.** Rewriting
         `p.decode s` inside a term whose type mentions `(x',t') ∈ p.decode s`
         fails on the dependent motive. `decodeFullStep_cons` and
         `attach_pair_eq` both take the list as a *parameter* and `cases` on it —
         the same shape `decodeFullStep_some` already used.
      Also worth knowing: `t.hle` must be restated as
      `have h : t.remaining ≤ n - m := t.hle` before `omega` — the `Suffix.drop`
      in `t.hle`'s own type does not reduce.

      **The confirmed route to the finish (`decodeFullFast.induct` case 3).**
      State the core lemma's conclusion with the specification's length index
      written **`(Suffix.drop m s).remaining`** — the type the recursor actually
      produces — rather than `n - m`:

          decodeFullFast p h s m acc =
            (decodeFull p h (Suffix.drop m s).remaining (Suffix.drop m s).bytes).map
              (fun tail => acc.reverse ++ tail)

      Verified to work: the motive elaborates and `refine_1` (the `n - m = 0`
      case) **closes outright**. This removes the `Suffix`-index mismatch at the
      source — `t0 : Suffix (Suffix.drop m s).remaining` and the induction
      hypothesis then live at the same type. A direct attempt to keep the spec at
      `Suffix (n - m)` fails because the two are numerically equal but *not*
      definitionally equal in the `Suffix (·)` position (checked).

      **The rewrite that makes the spec side reachable** — rewrite **only the
      RHS**, so the fast side's dependent `have hmem :=` is never touched:

          conv => rhs; rw [decodeFull_succ p h ((Suffix.drop m s).remaining) j hk']

      What remains after that is ordinary branch plumbing in `refine_2` and
      `refine_3`: `.attach` of `[]` (dispatch via
      `have hatt : (…).attach = [] := by rw [hz]; exact List.attach_nil`), then
      the pair unification via `attach_pair_eq`.

      **CORRECTION (2026-11-01): "No new mathematics is left" was FALSE.** The
      work is now landed in `Codec/Decode.lean` (not in a scratch file), and two
      things were genuinely missing:

      1. **`drop_trans_eq` — a lemma the ledger never named.**
          `Suffix.drop (m + ((n-m) - t.remaining)) s = Suffix.trans (Suffix.drop m s) t`.
          Without it the fast side re-roots at `s` while the spec side is nested, so
          the two `decodeFull` calls are *not* the same call and no rewrite can join
          them. LANDED, `[propext, Quot.sound]`-only. It cost exactly the two
          documented traps: state it **pointwise** (a `Bytes`-level form hits the
          length cast and blocks every downstream `rw`), and apply
          `step_bytes_pointwise` **before any `dsimp`** (`dsimp [Suffix.drop]` rewrites
          the root to `n - m`, breaking `t`'s `Suffix (Suffix.drop m s).remaining`
          index so the lemma no longer applies).
      2. **`decodeFullStep_nil`** — the empty-`attach` companion of
          `decodeFullStep_cons`, parameterized for the same reason. LANDED, axiom-free
          in effect (`[propext, Quot.sound]`).

      **What is actually still open (the single `sorry`, `Codec/Decode.lean:816`,
      which fails `lake build` by design):** only the `cons` case's two branches in
      `decodeFullFast_eq_aux`. The `some`/`none` split on the tail's recursion is not
      an `.attach` question at all — it needs a **`decodeFullStep`-all-fail lemma**:
      if every candidate in `lrest` has a failing recursion, then
      `decodeFullStep … lrest = none`. That is a real induction on the remaining
      list, not branch plumbing. The `some` branch additionally needs the
      accumulator reassociation `acc.reverse ++ (x :: xs) = (x :: acc).reverse ++ xs`
      (`List.reverse_cons` + `List.append_assoc` + `singleton_append`), already
      worked out.

      The base case (`n - m = 0`) and the decode-empty case are **closed**.

      **REFUTED (2026-11-01): the theorem 6.1a targets is FALSE.**
      `decodeFullFastRoot = decodeFull` does not hold, and no amount of transport
      closes it — the two functions search differently. Measured, reproducible:

      * `decodeFullFast` **commits to the head** of `decode p (Suffix.drop m s)`
        (`| (x, t) :: _rest => …`, recursing on `t` and never looking at `_rest`).
        If that recursion returns `none`, the *whole* call is `none`.
      * `decodeFullStep` (the specification) **backtracks**: `| none =>
        decodeFullStep p h s ih rest`. It tries the next candidate.

      They separate whenever the head consumes a different number of bytes than a
      later candidate. Witness (`Codec/Decode.lean`'s `decodeFullFast_eq_aux`
      docstring records it in full): `d = alt A B` at `UInt8 × UInt8` with
      `A = iso diag (satisfy (· == 0))` (consumes 1) and `B = seq byte byte`
      (consumes 2), input `[0,1]` (`[0]` then `[1]`):

      | expression | result |
      | --- | --- |
      | `decode d [0,1]` | `[((0,0), 1), ((0,1), 2)]` |
      | `decodeRepeat d hd 2 [0,1]` | `[([],0), ([(0,0)],1), ([(0,1)],2)]` |
      | `decodeFull d hd 2 [0,1]` | **`some [(0, 1)]`** — backtracks to B |
      | `decodeFullFastRoot d hd [0,1]` | **`none`** — commits to A, dead-ends |

      `decodeFull` is right per `decodeRepeat`; `decodeFullFastRoot` is wrong.

      **What this changes downstream.** (a) 6.1b's requirement "(a) prove it equal
      to `decodeFullFastRoot` so 6.1a's bridge composes" **inherits the defect**
      and must not be attempted as written. (b) The correct target is a fast
      decoder that **backtracks over the candidates while keeping the flat
      re-rooted cursor** — i.e. `decodeFullStep`'s search with `decodeFullFast`'s
      input discipline. The measured 6.1a win (9,047× at n=65536) was the *flat
      cursor*, not the head-commit, so that win survives; only the commit must go.
      (c) Two lemmas landed this session and stay, because the corrected
      direction needs exactly them: `decodeFullStep_none_of_forall_none` (the
      all-fail lemma this task named, now in the library) and
      `reverse_cons_append` (the accumulator reassociation).

      This is a findings-recorded-in-place refutation, not a narrowing: the
      requirement ("the fast path is proved equal to the spec, not merely
      measured") is kept; it is the *candidate implementation* that was wrong.

      **RE-DERIVED, per the owner's decision (2026-11-01): route rewritten, proof
      still open.** `decodeFullFast`/`decodeFullFastSearch` now **search** (the
      flat cursor is kept, the head-commit is gone), and both terminate — the
      mutual block's measure is `Prod.Lex` on
      `((Suffix.drop m s).remaining, cands.length)`, with the fast→search edge
      going `right` (same length, `decode len+1 > decode len`) and the
      search→fast edge going `left` (`ConsumesByte` gives the strict decrease).

      **Landed and proved:** `decodeFullFastSearch_eq` — the search corresponds
      to `decodeFullStep` exactly, by induction on the candidate list, using
      `decodeFullStep_cons`, `reverse_cons_append`, and the step hypothesis for
      each candidate. This is the substantive half of the bridge.

      **Still open:** the top-level bridge `decodeFullFastRoot = decodeFull`
      (`Codec/Decode.lean` has one `sorry`). The obstacle is *index alignment*, not
      mathematics: the fast decoder's recursive call is at cursor
      `m + ((n - m) - t.remaining)` over the **root** `s`, while the specification
      lives over `t.bytes`; the two are related by `drop_trans_eq`'s pointwise
      form, and `Suffix.drop (0 + ((n - 0) - t.remaining)) s`'s `.bytes` is not
      definitionally `t.bytes`, so every attempt to `rw` the index hits the
      recorded dependent-`Bytes` motive failure. The clean next step is a
      **cursor re-rooting lemma** (`decodeFullFast p h s m acc =
      decodeFullFast p h (Suffix.drop m s).bytes 0 acc`, by the same `Prod.Lex`
      induction) so the bridge can induct on the suffix alone and the index
      never has to be rewritten.

      **SESSION 2 RESULT (2026-11-01): the lemma is in the tree, base case closed,
      open half diagnosed.** `Codec.decodeFullFast_reroot` is stated in
      `Codec/Decode.lean` with its docstring carrying the full state; `lake build`
      fails there (plus the bridge) by design.

      * **Closed:** the `n - m = 0` case — unfold `decodeFullFast`, `cases` the
        cursor length with the equation in context, and the re-rooted side's own
        condition `(Suffix.drop m s).remaining - 0` is *definitionally* `n - m`, so
        it reduces in the same step.
      * **Open:** the `n - m = j + 1` case. **Structural induction on the candidate
        list cannot close it** — the search's recursive step calls
        `decodeFullFast` at the *advanced* cursor, so the goal becomes this very
        theorem at a smaller measure. It needs a **mutual measure induction**
        carrying the search congruence alongside it:
        `decodeFullFastSearch p h s m acc cs = decodeFullFastSearch p h
        (Suffix.drop m s).bytes 0 acc cs'` over the same list, ranked by the same
        `Prod.Lex ((Suffix.drop m s).remaining, cands.length)`. State the two
        together (a `mutual`-shaped `have` pair, or one lemma with the search as a
        conjunct per measured state) — do not state them separately, because
        either alone needs the other at a smaller measure.
      * **Dead end 1 (do not re-attempt): the `Suffix`-typed form does not
        elaborate in a goal.** `Suffix.drop 0 (Suffix.drop m s)` infers its first
        argument from `(Suffix.drop m s).bytes`, and `(·).bytes`'s dot notation
        binds to the `Suffix` **structure** — so the inferred index is the third
        *component* of the `Suffix` value, not its first, and in a *goal* (where
        the expected type fixes the index) elaboration fails with "expected
        `Suffix n`, got `Bytes n`". It also defeats `Suffix.drop 0 (Suffix.drop m
        s).bytes` **inside any function argument**, including under `decode` and
        under `match` branches — reproduced with a minimal `let` probe. Write the
        `.bytes` forms; an equality of the `Suffix`-typed term *is* accepted as a
        hypothesis (which is why the dead end is invisible until the goal needs it).
      * **Dead end 2:** length rewrites on the index (`Nat.sub_zero`,
        `Nat.sub_sub_self`) fail on the dependent-`Bytes` motive, `rfl`-true or not;
        `cases` on the length (equation in context) is the reduction that works.

      **SESSION 3 (2026-11-01): the re-rooting lemma alone is not enough — the
      `j + 1` case needs the *search* congruence too, and the ranking blocks it.**
      What is in the tree now is `Codec.decodeFullFast_pairwise` (with a `sorry`),
      stated as the pair of congruences over one measured state, plus
      `candsAt`/`candsRoot`/`retypeCands` naming the candidate list at the two
      roots. **Both `n - m = 0` branches are closed, and both live-cursor branches
      unfold correctly**; what fails is the hand-off.

      * **The coupling matters.** The search congruence must be stated with **one**
        candidate list, re-indexed between the two roots (`retypeCands`), not with
        two independent lists. With two, the `nil` branch is *false*: `cs = []` no
        longer constrains `cs'`. Recorded because it looks like a free choice.
      * **REFUTED (2026-11-02): the obstacle is NOT the `termination_by`
        ranking.** The previous session recorded "`Prod.Lex` has no reflexive
        case, so the fast congruence cannot reach the search congruence at the
        same key", and proposed a `mutual` statement or re-ranking the
        definition (a D9 shape carve-out). **That diagnosis is false and neither
        remedy is needed.** `@decodeFullFast.induct` was inspected directly: it
        takes `motive1 : (n s m acc) → Prop` and `motive2 : (n s m acc cs) →
        Prop`, one predicate per side, and its recursive hypotheses supply the
        fast congruence (inside `motive2`'s two cons cases) and the search
        congruence at a *shorter candidate list* (inside `motive2`'s `ihL`). The
        search congruence therefore needs **no hypothesis at the same key** — its
        cons case is `rw [hfast]; rw [reroot-unfold]`, then `ihL` for the `none`
        branch and `rfl` for the `some` branch. Nothing touches `Prod.Lex`.
        **Do not re-attempt the `mutual` restatement or re-rank the definition on
        this theory.**

      * **The actual obstacle: `Membership` instance selection on the re-rooted
        list.** `candsRoot` spells the re-rooted list at
        `decode p (Suffix.drop 0 (Suffix.drop m s).bytes).bytes`; the search's own
        signature demands `decode p (Suffix.drop m s).bytes`. Those two are
        `rfl`-equal (verified) but are **not the same syntactic head**, so
        `List.instMembership` unifies against the wrong one and every
        `rw [decodeFullFastSearch.eq_def]` in the re-rooted position fails with
        `Application type mismatch: List.instMembership … expected Membership (α ×
        Suffix (Suffix.drop m s).remaining)`. This is the *mechanism* behind the
        already-recorded `Suffix.drop 0` dead end; the earlier note blamed dot
        notation on `.bytes`, and the real trigger is the `Membership`
        typeclass argument-fact, which does not look through a definitional
        equality.
        **The workaround that works:** name the re-rooted list type as an alias on
        the **search's own return type** (a `Cands0 p r := List {pr : α × Suffix
        (Suffix.drop 0 r).remaining // pr ∈ decode p (Suffix.drop 0 r).bytes}`),
        and state the search congruence's re-rooted side at that alias. All four
        re-rooted reduction lemmas (`[]` at both roots, cons at both roots) and the
        whole search congruence then close.

      * **Third trap (still true):** `rw [decodeFullFastSearch.eq_def]` does
        **not** fire on an applied `decodeFullFastSearch` while its argument is
        still a variable (`match`-in-`match` body). `cases` the candidate list
        first, or state the unfolding as an explicit `have` and `rfl` it inside the
        branch.
      * **Fourth trap:** `obtain hk : n - m = j + 1 := hsucc` must precede
        `split`/`cases` on a subtraction; and `split`'s case tags are `h_1`/`h_2`,
        **not** the `_h` binder name. Bare `omega` cannot see the equation `split`
        introduces on the *re-rooted* side (`(Suffix.drop m s).remaining - 0`), so
        each branch needs its own `have : … - 0 = j + 1 := by dsimp only
        [Suffix.drop]; omega` supplied first.

      * **Progress (2026-11-02): cases 1–3 of the pairwise induction are closed**
        and the whole search congruence is proved, in a throwaway probe. Nothing
        has been folded into `Codec/Decode.lean` yet — it still carries both
        `sorry`s. **Remaining:** one step, `step at the re-rooted cursor`, to
        transport the recursor's fast congruence from the **home** advanced cursor
        `m + ((n - m) - r)` to the **re-rooted** cursor
        `0 + (((Suffix.drop m s).remaining - 0) - r)`; then the two cons cases
        (4, 5) fall from it. `drop_trans_eq` does **not** apply directly, because
        an `n`-indexed `Suffix` and a cursor-`0` `Suffix` differ in index — the
        step has to be stated **pointwise on `.bytes`**, by the same
        "read indices into the root" trick that made `step_bytes_pointwise` work
        (and for the same reason: a `Suffix`-typed or `Bytes`-typed statement hits
        the index mismatch).

      * **SOLVED (2026-11-02): the arithmetic is `r`, not `n - m - r`.** An
        earlier entry in this ledger claimed the transport step needed

            n - (m + (n - m - r)) = n - m - r

        and that it was "false without `m ≤ n`". **The identity was simply the
        wrong one.** Verified by exhaustive `#eval` over `n, m, r < 8`:

            (m ≤ n ∧ r ≤ n - m)  ->  n - (m + (n - m - r)) = r         -- TRUE
            (m ≤ n ∧ r ≤ n - m)  ->  n - (m + (n - m - r)) = n - m - r -- FALSE

        The remaining length after advancing the cursor by `r` **from** position
        `m` is `r` itself — the cursor's target is that suffix's own length, which
        is obvious in hindsight and cost two wrong attempts. **Both** true forms
        are now proved:

            probe_rem_eq  : r ≤ n - m -> n - (m + (n - m - r)) = r
            probe_rem_eq' : r ≤ n - m -> n - m - (0 + (n - m - r)) = r

        each by `rcases Nat.le_total m n` (the `m > n` branch forces `n - m = 0`
        and hence `r = 0`), then `splice_add` + `Nat.add_sub_assoc` +
        `Nat.sub_sub_self`. The pointwise transport (`probe_transport`) and the
        `Suffix`-level `probe_suffix_eq` are proved too, so **the transport step is
        closed**; what remains is only the two `cons` branches (cases 4, 5) of the
        pairwise induction.

      * **Methodology lesson (recorded because it burned two attempts).** Do not
        state a `Nat`-subtraction identity from intuition and then fight `omega`.
        `#eval` it exhaustively over small values first. When `omega` reported a
        counterexample it was **correct every time** — the stated identity was
        false, not the tactic inadequate. `omega` also cannot derive `m ≤ n` from
        `n - m` under truncation (both `n ≤ m` and `m > n` collapse `n - m` to
        `0`), so any identity mentioning `n - m` must be case-split on
        `Nat.le_total m n` first.

      * **Toolchain note:** this Lean has **no `conv_lhs`/`conv_rhs`** (`unknown
        tactic`), and `conv => lhs; rw [...]` is not available. Use `calc`,
        `nth_rewrite`, or a named `have` instead.

      * **Tactics that do NOT work here** (all tried, recorded so they are not
        retried): bare `omega` on a goal containing `n - (m + …)`; `Nat.sub_sub_self`
        on the wrong pairing; `Nat.sub_add_cancel` (its implicit arg order binds the
        wrong `n`); `splice_add` called **without** naming `n` and `m` (its
        implicits bind to the first `Nat.sub` in sight).

      * **SESSION 4 (2026-11-02) — landed in `Codec/Decode.lean`, gate still red at
        two `sorry`s (by design).** Four lemmas are now **in the library**, each
        proved (no `sorry`), and the docstring on `decodeFullFast_pairwise` has been
        rewritten to carry the confirmed shape and drop the refuted ranking story:

        | lemma | statement |
        | --- | --- |
        | `remaining_at_cursor` | `r ≤ n - m → n - (m + (n - m - r)) = r` |
        | `remaining_at_reroot` | `r ≤ n - m → n - m - (0 + (n - m - r)) = r` |
        | `search_nil_left` | the search over `[]` at a cursor is `none` |
        | `search_nil_right` | the same at a re-rooted cursor-`0` root |

        **Axiom check is NOT run** — `#print axioms` needs `Codec.Decode.olean`, which
        the gate refuses to produce while the `sorry` remains. They are `omega`/`rfl`
        derived, so expected `[propext, Quot.sound]`-only, but **that is unverified
        until the gate goes green**; run it as the first step after 6.1a closes.

      * **SESSION 7 (2026-11-02) — `Suffix.drop_zero` landed; the root bridge's
        `zero` case closed; the successor case reduced to one well-identified
        obligation, with two routes refuted.** Landed: `Suffix.drop_zero`
        (`Suffix.drop 0 s = Suffix.id n s`), proved and in the library.
        `decodeFullFastRoot_eq`'s `zero` case now closes
        (`decodeFullFast_zero` + `decodeFull_zero` + `rfl`).

        **The successor case is now exactly:**

            decodeFullFastSearch p h s 0 [] (decode p (Suffix.drop 0 s).bytes).attach
              = decodeFullStep p h s (fun m s' _ => decodeFull p h m s') (decode p s).attach

        `decodeFullFastSearch_eq` applies to it **directly** (its cands argument is
        spelled `Suffix.drop m s`, and `m = 0` is the goal's own spelling — so the
        feared `Membership` trap does **not** fire here; the earlier note about it
        applies to rewriting the head *afterwards*, which this route never does).
        What is left after applying it is its **step hypothesis**: for each
        candidate `(x, t)`,

            decodeFullFast p h s (m + (n - m - t.remaining)) (x :: acc) = …

        — the same statement at an advanced cursor with a **non-empty accumulator**.

        **Two routes REFUTED this session (do not retry):**
        1. **`decodeFull_reroot_cursor` does not apply.** It is stated for
           `decodeFull`, not `decodeFullFast`, so it cannot relate the fast side at
           the advanced cursor to `decodeFullFastRoot t.bytes`. (It remains the
           right tool for the *specification* side, which is what it was proved for.)
        2. **`Nat.strongRecOn` on `n` cannot reach the step hypothesis.** The step is
           at the *same* `n` and the *same* `s`, so the induction hypothesis is not in
           scope. This is the concrete reason the ledger has said all along that the
           statement must be **cursor-measured, not `n`-measured** — now demonstrated
           rather than asserted.

        **The confirmed next shape** (written into the obligation's own comment in
        `Codec/Decode.lean`): prove

            decodeFullFast p h s m acc
              = (decodeFull p h (Suffix.drop m s).remaining (Suffix.drop m s).bytes).map
                  (fun tail => acc.reverse ++ tail)

        by well-founded induction on the **fast decoder's own cursor measure**
        `((Suffix.drop m s).remaining, cands.length)` — the same `Prod.Lex` its
        `termination_by` uses — and take the root bridge as its `m = 0` case. The
        `n - m = 0` case of that general statement is already worked out
        (`decodeFullFast_zero` + `decodeFull_at_zero` + `List.append_nil`); only the
        successor case's step is genuinely open.

        **`decodeFullFast_pairwise` is now optional, not the route.** It was written
        to serve the re-rooting lemma, which turned out not to need it (SESSION 6).
        Its docstring records that, so nobody finishes it before the root bridge.

      * **SESSION 6 (2026-11-02) — the re-rooting lemma is PROVED, and the root
        bridge is reduced to one step hypothesis.** Landed in `Codec/Decode.lean`
        (all proved, no `sorry`):

        | lemma | statement |
        | --- | --- |
        | `decodeFullFast_succ` | the fast decoder's unfold **at a known successor cursor** |
        | `decodeFullFast_zero` | the same at a known zero cursor |
        | `Suffix.drop_zero` | `Suffix.drop 0 s = Suffix.id n s` |
        | — (`reroot_bytes_eq`) | the two cursors read the same bytes at length `r` |
        | — (`decodeFull_reroot_cursor`) | **the 6.1a blocker**: spec at cursor `m` over `s` = spec at the re-rooted cursor over `bdrop m s` |

        **The unfold recipe is now a named lemma, not folklore.**
        `decodeFullFast_succ` is
        `conv => lhs; rw [decodeFullFast.eq_def]; dsimp only; rw [hm]`, and the
        `dsimp only` is load-bearing: the definition compiles to
        `match n, s, m, acc with`, so without it `rw [hm]` reports "did not find an
        occurrence of the pattern `n - m`" and looks like a type error. It is not.
        This closes the blocker four sessions could not name. **Do not re-derive it.**

        **`decodeFull_reroot_cursor` needed no `ih` congruence — confirmed.** After
        stepping both sides (`decodeFull_succ`), the two `decodeFullStep` calls differ
        **only in their root**, and the step is discharged by `reroot_bytes_eq` in one
        rewrite. The `0` case is `decodeFull_zero` on both sides. This settles the
        question the SESSION 3 entry left open: `candsAt`/`candsRoot`/`retypeCands`
        and every `Membership` workaround are **not needed** for the re-rooting
        lemma, and the earlier "the search congruence must be stated over one
        re-indexed list" framing was an artefact of the route now abandoned.

        **The cast wall is real and `reroot_bytes_eq` is how to get around it.** The
        lemma's two `decide`-style statements were provable only **pointwise**
        (`funext` + `cast_bytes_val'`/`cast_bytes_val_symm`), because the two casts
        carry equal-but-different width proofs and no `rw` can abstract them ("motive
        is not type correct"). Stating the re-rooting lemma **at `r` on both sides,
        with the two casts written out in the statement**, is what made it typecheck;
        every simpler spelling fails in the thesis (`decodeFull p h r` demands
        `Bytes r`).

        **A false lemma was asserted and refuted this session, recorded so it is not
        retried:** `n - (m + (n - m - 0)) = n - m` is **FALSE** (it is `0`). An
        exhaustive `#eval` over `n, m < 10` refuted it after several failed `omega`
        attempts; `omega` was right and the stated identity was wrong. The true
        facts are `n - (m + (n - m - r)) = r` (`remaining_at_cursor`, already landed)
        and the `r = 0` instance evaluates to `0`. This is the ledger's existing
        "`#eval` the identity first" lesson biting again.

        **What is left: `decodeFullFastRoot_eq`'s successor case only.** `zero`
        closes (`decodeFullFast_zero` + `decodeFull_zero` + `rfl`). `succ` is
        `decodeFullFast_succ` then `decodeFull_succ`, leaving

            decodeFullFastSearch p h s 0 [] (decode p (Suffix.drop 0 s).bytes).attach
              = decodeFullStep p h s (fun m s' _ => decodeFull p h m s') (decode p s).attach

        which `decodeFullFastSearch_eq` was built for. **The one obstacle is the
        `Membership` trap the ledger already records**: `Suffix.drop 0 s` is `rfl`-equal
        to `s` but is not the same syntactic head, so rewriting it into the
        `decodeFullFastSearch` cands argument fails with
        `Application type mismatch: List.instMembership`. `Suffix.drop_zero` (landed)
        makes the two heads **equal**, not identical, which is not enough for `rw`.
        **The next move is to state the cands type at the search's own spelling
        first** — i.e. prove the goal with `s` substituted for `Suffix.drop 0 s` in
        the *statement* (`decodeFullFast_succ` can be restated at the `s`-rooted
        cands type, since `Suffix.drop 0 s` and `s` are interchangeable there) rather
        than trying to rewrite afterwards. Do not attempt `rw` into an applied
        `decodeFullFastSearch`'s `attach` argument.

      * **SESSION 5 (2026-11-02) — two mechanical breakthroughs, and the cast is a
        real wall.** Landed in `Codec/Decode.lean` (both proved, no `sorry`):

        | lemma | why it exists |
        | --- | --- |
        | `bdrop_seg` | `bdrop (b - a) (bdrop a s) = cast _ (bdrop b s)` for `a ≤ b`, with the cast proved by `omega` in the `Bytes` index |
        | `decode_congr_bdrop` | `decode` invariant under it — the step's rewrite |

        **Breakthrough 1: the unfold recipe is `conv => lhs; rw [decodeFullFast.eq_def]`,
        then `dsimp only`, then `rw [hk]`.** The `dsimp only` was the step every
        previous session was missing: without it `rw [hj]` fails with "did not find
        an occurrence of the pattern `n - m`" because the body is still wrapped in
        `match n, s, m, acc with`. With it, both `decodeFullFast` unfoldings
        (`n - m = 0` → `some acc.reverse`, `n - m = j + 1` → the search) close
        outright. Reproduced, then removed as probes. **This removes the "get one
        arm to close by hand" blocker the last entry left open — it is closed.**

        **Breakthrough 2 (the structural one): `decodeFull`'s recursor step does NOT
        need a congruence over the WellFounded `ih`.** The previous route assumed
        `decodeFull_reroot_cursor` must compare two `decodeFullStep` calls and hence
        transport `ih` across roots. It does not: `decodeFull_succ` rewrites the
        successor side into `decodeFullStep … (decode p s).attach`, and that
        recursor is applied to `fun m s' _ => decodeFull p h m s'` — **the same
        lambda on both sides**. So the step needs only statements about `bdrop`
        (which is what `bdrop_seg` is for), never about the recursor's hypothesis.
        Stating the re-rooting lemma as an **`ih`-carrying strong induction on the
        remaining length** is now the confirmed shape; the `decodeFullStep_none`
        machinery stays for 6.1b, not for this lemma.

      * **The wall (do not re-litigate, but do design around): a `Bytes` term whose
        length is only *knowably* equal cannot be passed to `decodeFull`.**
        `bdrop (m + (n - m - r)) s : Bytes (n - (m + (n - m - r)))`, and
        `decodeFull p h r` demands `Bytes r`. Bridging those needs
        `cast (congrArg Bytes (remaining_at_cursor hr))`, and that cast **cannot be
        elaborated** where `r` is a free variable: the cast's own length argument
        is `r` but the target is the opaque expression `n - (m + (n - m - r))`, so
        `cast` rejects the argument ("has type `Bytes (n - …)` but is expected to
        have type `Bytes r`") *before* `omega` is ever consulted. Verified in both
        directions and with the equality supplied as a hypothesis; also verified
        that `remaining_at_cursor` itself is true on all `n, m, r < 12` (`#eval`).
        **The working spelling is `bdrop_seg`'s: keep every cursor length
        syntactically identical between the two sides**, i.e. state the recursive
        hypothesis at `bdrop (a + (n - a - r))` and only ever translate
        `(b - a)`-shaped differences. That is why `decode_congr_bdrop` takes
        `a`/`b` and no `r`.

      * **This is also a direct answer to the ledger's old "index alignment"
        framing:** the obstacle was never that the fast side re-roots at `s` while
        the spec nests — `drop_trans_eq` already handles that, and (see above) the
        spec does not nest once `decodeFull_succ` is used. It is purely that a
        `Bytes` value at a merely-equal length may not cross into a
        length-indexed redex. `remaining_at_cursor`/`remaining_at_reroot` are
        therefore **not** on the critical path for 6.1a; `bdrop_seg` is.

      * **What is left in 6.1a, precisely.** `decodeFullFast_pairwise`'s body is a
        single `sorry` in `Codec/Decode.lean`, with the recursor's five case arms
        already sketched as `intro`-lines. Two of them (the `[]` halves) are now
        discharged by the landed lemmas; the open work is **only** the two
        `decodeFullFast`-unfolding arms:
        - `n - m = 0`: both sides must reduce to `some acc.reverse`;
        - `n - m = j + 1` with an empty candidate list: both sides must reach the
          search at `[]`.
        **The blocker is mechanical, not mathematical:** `rw [decodeFullFast.eq_def]`
        leaves the body as a `match _hm : n - m with …` and neither `rfl` nor
        `simp only [hk]` discharges it, because the named equation `_hm` blocks the
        ι-reduction. `split` produces case tags that do not match (`h_1` alone, or a
        `List α` binder named `heq`), and `cases n - m` renames the equation so the
        hypothesis is no longer the one in context. **Next step: get one arm to
        close by hand** — most likely by stating the unfolding as an explicit
        `have … : decodeFullFast p h s m acc = (match _hm : n - m with …)` with
        `rfl`/`congr 1` inside, then rewriting with it (the shape
        `decodeFull_succ` already uses upstream in this file, and it works there).

      **CLOSED (2026-11-02).** `decodeFullFastRoot_eq` is **proved** — zero `sorry`
      in `Codec/Decode.lean`, `lake build` green (13 jobs), and `#print axioms`
      reports `[propext, Quot.sound]`-only / zero `Classical.choice` on all four
      new declarations. The gate is gone; 6.1b and 6.3/6.4 are unblocked.

      **The two decisions that closed it** (after seven sessions and three
      refuted routes — none of the refutations is re-litigated here, they stand):

      1. **State the specification side at the root spelling `bdrop m s`, never at
         the projection `(Suffix.drop m s).bytes`.** They are `rfl`-equal
         (`Suffix.drop` *is* `{remaining := n - m, bytes := bdrop m s}`), but
         `decodeFull` is `Fin`-indexed by its root's length, and a projection's
         `bytes` field is not *syntactically* at the index the recursor's motive
         wants — which is exactly why every earlier `generalize`/`rw` on that
         length died on "motive is not type correct". The `bdrop` spelling makes
         the index a literal `n - m`, so `decodeFull_succ`/`decodeFull_at_zero`
         consume it directly. **This single spelling choice was the whole gate.**
      2. **Induct on the cursor measure `(Suffix.drop m s).remaining` carrying
         BOTH congruences as one conjunction.** Neither half is provable alone:
         the search congruence's step calls the fast decoder at an *advanced*
         cursor, so it needs the fast congruence at a strictly smaller measure.
         This is the `cursor_bridge` statement, and `decodeFullFastRoot_eq` is
         just its `m = 0` case (`bdrop 0 s`/`n - 0`/`[].reverse` are all
         definitional). No `decodeFullFast.induct`, no `Membership` alias, no
         re-ranking, no `mutual` — those were all real obstacles of *refuted
         routes*, not of this one.

      **Landed:** `cands_eq_nil_of_zero` (no candidate exists at a zero cursor —
      the `[]` case of the search congruence, and the reason the search is well
      founded rather than merely structural), `spec_at_advance` (re-roots the IH
      onto the candidate's own bytes via `drop_trans_eq`, stated as a **`Suffix`
      equality** so the dependent-`Bytes` motive accepts it where a length rewrite
      does not), `cursor_bridge`, `decodeFullFastRoot_eq`.

      **Deleted, not left as a second `sorry`:** `decodeFullFast_pairwise`. The
      route it served is proved without it, and its own docstring said not to
      finish it before the root bridge. Nothing in the tree references it.

      **Runtime agreement re-checked** on the very witness that refuted the
      previous head-committing `decodeFullFast`: `decode` returns
      `[(0,1), (9,0)]` (head `A` consumes 1 byte, sibling `B` consumes 2);
      `decodeFull` and `decodeFullFastRoot` both now return `some [9]`, where the
      committed version returned `none`. So the theorem is not vacuous and the
      backtracking is intact.

- [x] 6.1b **Move the fast decode onto an `Array UInt8` + `Nat` cursor**

      **DONE 2026-11-03: proof closed (session 9) and the numeric re-measurement
      landed via 6.4's `benchDecodeShapes` lane.** Measured: `decodeFullArrayRoot`
      at **57 ns/step** vs `decodeFullFastRoot`'s 69 and an ideal `Id.run` loop's
      **6**. The `[~]` this task carried existed only because no lane printed a
      number; one does now, and `tasks.md` 6.4 holds its table.

      **THE PROOF IS DONE (session 9); the re-measurement is not, and it is not
      this task's to run.** `array_bridge` and `decodeFullArrayRoot_eq` are proved
      (`[propext, Quot.sound]`-only, zero `sorry`), a `bench` lane
      (`benchDecodeFullArray`) asserts the bridge at run time, and the numeric
      ratio belongs to **6.4** — it needs an idle machine and an interleaved
      `memcpy` reference, which this session did not have (load average 2.4 on a
      10-core machine). Do **not** quote a number for the packed path until 6.4's
      lane prints one; see MEASUREMENT RULES below.

      **PLAN FOR NEXT SESSION (2026-11-02, written after reading the code — not
      from the ledger's memory of it). This is the whole task; nothing in it is
      speculative.**

      *What exists.* Two things, both proved, `[propext, Quot.sound]`-only:

      | in | name | what it gives |
      |---|---|---|
      | `Codec/Packed.lean:59` | `decodeArray d a i : List (α × Nat)` | the cursor decoder: `Array UInt8` + `Nat` consumed-count, no `Suffix`, no `bdrop` |
      | `Codec/Packed.lean:397` | `decodeArray_eq` | `decodeArray d a i = (decode d (bdrop i (arrayToBytes a))).map (x,t) ↦ (x, consumedAbs a i t)` |
      | `Codec/Packed.lean:495` | `decodeArray_consumes` | `(x,c) ∈ decodeArray d a k → k < a.size → k < c` — the strict-advance fact the search's well-foundedness needs |
      | `Codec/Packed.lean:144` | `consumedAbs a i t = i + ((a.size - i) - t.remaining)` | the cursor advance, as a `Nat` |

      and, in `Codec/Decode.lean`, the *whole* 6.1a apparatus that 6.1b mirrors:
      `decodeFullFast`/`decodeFullFastSearch` (the mutual pair, `:221`–`:268`),
      `decodeFullStep` (`:180`), `decodeFullFastSearch_eq` (`:837`),
      `decodeFullStep_none_of_forall_none` (`:793`), `reverse_cons_append`
      (`:816`), `spec_at_advance` (`:1141`), `cands_eq_nil_of_zero` (`:1113`),
      `decodeFull_at_zero`/`decodeFull_succ` (`:655`/`:669`), and `cursor_bridge`
      (`:1180`).

      **`decodeFullArray` must NOT be used.** It is `| (_, c) :: _ => some (…)` —
      it commits to the head, and `decodeFullArray_spec` honestly proves it equal
      to `head?` of `decode`. True theorem, wrong decoder. Anything built on it
      inherits the defect 6.1a fixed in `decodeFullFast`.

      ---

      **Step 1 — the mutual pair, in `Codec/Packed.lean` (after
      `decodeArray_consumes`, which it needs).** Mirror `decodeFullFast` +
      `decodeFullFastSearch` with `Suffix` plumbing replaced by a `Nat` cursor.
      Copy the *shape*, do not invent:

          mutual
          def fullArray {α} (d : Codec α) (h : ConsumesByte d) (a : Array UInt8)
              (k : Nat) (hk : k < a.size) (acc : List α) : Option (List α) :=
            match _ : a.size - k with
            | 0 => some acc.reverse
            | _ + 1 => fullArraySearch d h a k hk acc (decodeArray d a k).attach
          termination_by a k _ acc => (a.size - k, (decodeArray d a k).length + 1)

          def fullArraySearch {α} (d : Codec α) (h : ConsumesByte d) (a : Array UInt8)
              (k : Nat) (hk : k < a.size) (acc : List α)
              (cands : List { pr : α × Nat // pr ∈ decodeArray d a k }) : Option (List α) :=
            match cands with
            | [] => none
            | ⟨(x, c), _⟩ :: rest =>
                match fullArray d h a c (by have := decodeArray_consumes d h a k x c _ hk; omega) (x :: acc) with
                | none => fullArraySearch d h a k hk acc rest
                | some xs => some xs
          termination_by a k _ _ cands => (a.size - k, cands.length)
          decreasing_by
            · exact Prod.Lex.left _ _ (by
                have hc := decodeArray_consumes d h a k x c ‹_› hk
                omega)
            · exact Prod.Lex.right _ (Nat.le_refl _)
          end

      Four things that are *not* free, each already proved to bite:

      1. **Thread `hk : k < a.size` as an explicit parameter.** The `if hk :`
         binder is not reliably in scope inside `decreasing_by`. This is also why
         the recursive `fullArray` call can discharge its own `hk` at `c`
         (`decodeArray_consumes` + `omega`) with no `rename_i` at all — the
         `rename_i`/"too many variable names" trap (15 dead attempts in an earlier
         session) disappears once the hypothesis is a parameter.
      2. **Both `termination_by` measures must have the same type** (`Prod.Lex`
         in both) or Lean errors "termination measures must have the same return
         type".
      3. **`k = a.size` terminates via `acc.reverse`, not via an empty candidate
         list.** `a.size - k = 0 → k = a.size` from `hk`, so the base case is the
         *end of input*; the candidate list is never consulted. This is the one
         structural difference from `decodeFullFast`, which branches on `n - m`
         with no `hk` side condition. Do not add a `cands = []` base case — it is
         unreachable and would be a second, weaker exit.
      4. **Do NOT substitute the search by an explicit `WellFounded.fix`.** It
         avoids `decreasing_by` but changes the reduction equation to
         `WellFounded.fix_eq` — precisely the trap 6.1a lost seven sessions to.
         Every downstream proof would need `unfold; rw [WellFounded.fix_eq]`
         instead of `rw [….eq_def]`.

      **Step 2 — the two unfolder lemmas, mirroring `decodeFullFast_zero`/
      `decodeFullFast_succ` (`:1088`/`:1079`).** The recipe is the recorded one and
      the `dsimp only` is load-bearing (the definition compiles to
      `match a, k, hk, acc with`, so without it `rw [hk']` reports "did not find an
      occurrence of the pattern `a.size - k`" and looks like a type error):

          conv => lhs; rw [fullArray.eq_def]; dsimp only; rw [hk']

      State them at a *known* `a.size - k` (`= 0` and `= j + 1`), exactly as 6.1a
      does.

      **Step 3 — the bridge.** `cursor_bridge` (`Codec/Decode.lean:1180`) is the
      template and its two decisions transfer verbatim:

      - **Measure:** `Nat.strongRecOn` on `a.size - k`, carrying **both**
        congruences as one conjunction (fast and search). Neither half is provable
        alone: the search's step calls the decoder at an advanced cursor, so it
        needs the decoder congruence at a strictly smaller measure.
      - **Specification side spelling:** state it at the root
        `bdrop k (arrayToBytes a)`, never through a projection, for the reason
        `cursor_bridge`'s docstring records (a projection's `bytes` field is not
        syntactically at the index the recursor's motive wants).

      Target:

          fullArrayRoot d h a = decodeFull d h a.size (arrayToBytes a)

      where `fullArrayRoot d h a := fullArray d h a 0 (by ...) []`. The
      specification side is `decodeFull` — **not** `decodeFullFastRoot`, which
      6.1a already proved equal to `decodeFull`; going through it would add a
      second bridge for no gain.

      **The bridge's step, and the one place it differs from 6.1a.** 6.1a's
      `spec_at_advance` re-roots the IH from cursor `m + ((n-m) - t.remaining)`
      onto `t.bytes` via `drop_trans_eq`. Here the *specification* never moves: it
      lives on `bdrop k (arrayToBytes a)` throughout and the cursor advances by
      `c = consumedAbs a k t`. So the analogue of `spec_at_advance` is the
      pointwise identity

          bdrop c (arrayToBytes a) = t.bytes            (c = consumedAbs a k t)

      which is `decodeArray_eq`'s membership + the `Suffix`/`bdrop` correspondence
      `decode p (bdrop k …)` already carries — state it as a **`Suffix` equality**
      (`Suffix.drop k`-shaped), because a `Bytes`-level or length-level statement
      hits the "motive is not type correct" wall that `spec_at_advance`'s docstring
      and `AGENTS.md` both record. Budget a session's worth of fiddling here; it is
      the only genuinely new mathematics in the task.

      **Step 4 — measure, then stop.** Add the bench lane only after the bridge is
      green. Read the MEASUREMENT RULES below first: they cost a full day.

      ---

      **SESSION 8 (2026-11-02) — steps 1 and 2 LANDED, step 3 is half done, and four
      plan corrections. `lake build` green (13 jobs), zero warnings, zero `sorry`.**

      Landed in `Codec/Packed.lean`, each proved, `[propext, Quot.sound]`-only:

      | commit | what |
      | --- | --- |
      | `b468f28` | `decodeFullArrayFast` / `decodeFullArraySearch` — **step 1**, the mutual pair |
      | `f3bc5f4` | `decodeFullArrayFast_succ` / `_zero` — **step 2**, the unfolder lemmas |
      | `d033799` | `packedCands`, `length_packedCands_le`, `mem_packedCands`, `packedCands_mem`/`_consumes`, `decodeFullArraySearch_cons`/`_nil` |
      | (this one) | `consume_lt` — a `ConsumesByte` step strictly advances the packed cursor |

      **Four things the plan got wrong — do not re-derive them:**

      1. **`termination_by` takes no binders here.** The plan's
         `termination_by a k _ acc => (…)` is a parse error: `Array.size` is not a
         bound variable, so `a.size` is unknown in the binder list. Use the bare
         tuple `termination_by (a.size - k, (packedCands d h a k).length + 1)`.
         (6.1a's `Bytes`-indexed version *does* need binders because the measure
         mentions `s`, which is a bound variable there.)

      2. **`hk` must be dischargeable from a NAMED field, so the candidate type
         carries it.** The plan says "thread `hk : k < a.size` as a parameter so
         `decreasing_by` needs no `rename_i`". That is necessary but not
         sufficient: discharging the recursive call's `hk` from a `ConsumesByte`
         *application* inside a `match` arm **fails**, because the arm's hypotheses
         are not in scope for the argument's `by` block (`omega` then sees `k < c`
         nowhere). The fix is `PackedCand`: a candidate subtype holding
         `pr ∈ decodeArray d a k ∧ k < pr.2 ∧ pr.2 ≤ a.size`, built by
         `packedCands` with a **`filterMap` over `attach`** (never a `List.map`, so
         the membership witness survives). The recursive call then reads `hk` off a
         field.

      3. **The candidate bound is `≤ a.size`, NOT `< a.size`.** `pure x` yields
         `c = i`, so `decodeArray_bounded_upper`'s `≤` is the honest fact and `<`
         is simply false. That is why `PackedCand`'s third component is `≤`.

      4. **The 6.1a `conv`/`dsimp only` unfold recipe does NOT transfer.** For this
         `mutual`-defined search, `dsimp only` makes no progress ("`dsimp` made no
         progress") and `split` generates fresh binders (`x✝`, `c✝`, `rest✝`) that
         do not align with the stated ones. The working recipe for
         `decodeFullArraySearch_cons` is
         `conv => lhs; rw [decodeFullArraySearch.eq_def]; simp only; split;
         · simp at *; · rename_i heq; injection heq with h1 h2; simp_all`
         (`injection` is what re-aligns `split`'s binders).

      **Step 3, the bridge — the statement is fixed and the base case is CLOSED.**
      The target is the pair congruence, `Nat.strongRecOn` on `a.size - k`:

          array_bridge : ∀ K a k hk, a.size - k ≤ K →
            (∀ acc, decodeFullArrayFast d h a k acc
               = (decodeFull d h (a.size - k) (bdrop k (arrayToBytes a))).map
                   (fun tail => acc.reverse ++ tail)) ∧
            (∀ acc cs, decodeFullArraySearch d h a k hk acc cs
               = (decodeFullStep d h (bdrop k (arrayToBytes a))
                    (fun m s' _ => decodeFull d h m s')
                    ((decode d (bdrop k (arrayToBytes a))).attach)).map
                   (fun tail => acc.reverse ++ tail))

      Two decisions that are **load-bearing and verified**:

      * **The measure must be `a.size - k ≤ K`, not `= K`.** The recursive calls sit
        at the *child* cursor, so the IH is consumed at a smaller remaining length;
        with `=` the IH is unusable (`a.size - k < a.size - k`). The child's
        remaining length is `t.remaining` exactly, by `consumedAbs_remaining`.
      * **The spec side is spelled at the root `bdrop k (arrayToBytes a)`**, never
        through a projection — the same reason `cursor_bridge` records. It makes the
        index the recursor's motive wants.

      **The base case (`a.size - k = 0`) is fully closed in a probe** and its two
      halves are: `decodeFullArrayFast_zero` + `decodeFull_at_zero` + `List.append_nil`
      for the fast half; and, for the search half, `cs = []` (no candidate exists —
      `PackedCand`'s `k < pr.2` contradicts `a.size - k = 0`) followed by
      `decode d (bdrop k …) = []` (same contradiction against `ConsumesByte`),
      `List.attach_nil`, `decodeFullStep.eq_def`, `rfl`.

      **The ONE open obligation (the successor case, and only this).** What is left
      is the two congruences at `a.size - k = j + 1`:

      * **fast half**: `decodeFullArrayFast_succ` + `decodeFull_succ`, then hand the
        search congruence its **step hypothesis** — for each `PackedCand` `⟨(x,c),…⟩`,
        `decodeFullArrayFast d h a c (x :: acc) = (decodeFull d h t.remaining t.bytes).map (…)`
        where `(x, t)` is the *same* candidate seen by `decode`. This needs the
        candidate-list correspondence: `packedCands` is a `filterMap` of
        `(decodeArray d a k).attach`, and `decodeArray_eq` maps that list onto
        `decode d (bdrop k …)`'s results. **That `PackedCand` ↔ `Suffix`
        bijection is the genuinely new mathematics** — a `filterMap`/`attach`
        correspondence lemma, plus re-rooting the IH at `consumedAbs a k t` via
        `bdrop_consumedAbs_eq` + `consumedAbs_remaining`.
      * **search half**: `decodeFullArraySearch_cons` case-by-case over the
        candidate list, using the fast half at each candidate (this composes once the
        fast half exists — the shape `decodeFullFastSearch_eq` uses).

      The probe lived in `/tmp` and is deleted to the analysis above; nothing
      partially-proved was left in the tree, so the build is green. **Next session
      starts here**, at the `packedCands` ↔ `decode`-candidate bijection.

      ---

      **THE PLAN FOR NEXT SESSION (written from the code, 2026-11-02). Work only
      the successor case of `array_bridge`. Nothing else in 6.1b is open.**

      What exists and is proved (`Codec/Packed.lean` unless noted):
      `decodeFullArrayFast`/`decodeFullArraySearch`, `decodeFullArrayFast_succ`/
      `_zero`, `decodeFullArraySearch_cons`/`_nil`, `packedCands`,
      `mem_packedCands`, `packedCands_mem`/`_consumes`, `length_packedCands_le`,
      `consume_lt`, `decodeArray_eq`, `bdrop_consumedAbs_eq`,
      `consumedAbs_remaining`, and (in `Codec/Decode.lean`) `decodeFullStep_cons`,
      `decodeFullStep_nil`, `decodeFullStep_none_of_forall_none`,
      `decodeFull_succ`, `decodeFull_at_zero`, `reverse_cons_append`.

      **Step A — the candidate bijection (the only new mathematics).** Prove the
      list-level correspondence between the two candidate lists at cursor `k`:

          packedCands d h a k   ↔   (decode d (bdrop k (arrayToBytes a))).attach

      with the element map `⟨(x, t), _⟩ ↦ ⟨(x, consumedAbs a k t), _⟩`. Two
      directions, and **neither is an `attach`/`filterMap` `rw`** — the ledger
      already records that rewriting under `.attach` fails on the dependent motive
      (6.1a trap 2), so state both **with the list as an explicit parameter** and
      prove by induction on it, exactly as `decodeFullStep_cons`/
      `decodeFullStep_none_of_forall_none` do:

      * `packedCands_eq_filterMap` — `packedCands d h a k` equals the `filterMap`
        of `(decodeArray d a k).attach` by the `if hp / if hq` predicate, i.e. an
        *unfold-and-prove-the-`dif`s* lemma (both conditions are decidable and,
        under `ConsumesByte`, always `true` — `decodeArray_consumes` gives
        `hp`, `decodeArray_bounded_upper` gives `hq`). This kills the `filterMap`
        without any membership reasoning, and is the piece that makes the list
        *equal* to `(decodeArray d a k).attach` element-for-element.
      * `decodeArray_eq_attach` — `(decodeArray d a k).attach` corresponds to
        `(decode d (bdrop k (arrayToBytes a))).attach` under the `consumedAbs` map,
        by `decodeArray_eq` + `List.attach_map`-shaped reasoning. Do **not** try to
        `rw` inside `.attach`; destructure both with `List.attach_eq_cons`-shaped
        existential lemmas (the `Codec/Decode.lean` pattern) if the direct route
        stalls.

      **Step B — the fast congruence's step hypothesis.** With Step A in hand, for
      each candidate `⟨(x, c), _⟩` of `packedCands d h a k`, the fast call
      `decodeFullArrayFast d h a c (x :: acc)` must equal
      `(decodeFull d h t.remaining t.bytes).map (fun tail => (x :: acc).reverse ++ tail)`
      where `c = consumedAbs a k t`. Route: the IH at the child cursor
      `(a.size - c) = t.remaining` (via `consumedAbs_remaining`), which is `< a.size - k`
      by `consume_lt`, so it is in the strong induction's range; then
      `bdrop_consumedAbs_eq` casts `bdrop c (arrayToBytes a)` to `t.bytes`.

      **Step C — compose.** Fast half = `decodeFullArrayFast_succ` +
      `decodeFull_succ` + `decodeFullArraySearch_eq`-shaped search congruence fed
      Step B. Search half = `decodeFullArraySearch_cons` by `induction` on the
      candidate list, calling the fast half at each head. This is the
      `decodeFullFastSearch_eq`/`cursor_bridge` composition shape, which is already
      proved for the `Suffix` version and transfers.

      **Step D — the root bridge.** `array_bridge` at `K := a.size`, `k := 0`;
      `bdrop 0`/`a.size - 0`/`[].reverse` are all definitional, exactly as
      `decodeFullFastRoot_eq` takes `cursor_bridge`'s `m = 0` case.

      **Three known traps, inherited and confirmed — do not re-derive:**
      1. `Array.size` is not a `termination_by` binder; use the bare tuple.
      2. The candidate bound is `≤ a.size` (from `decodeArray_bounded_upper`), never `<`.
      3. `conv`/`dsimp only` does **not** unfold this `mutual` definition; use `split`
         (and `injection` on the discriminant equation to realign `split`'s binders).

      **If Step A stalls, do not force it** — record the refutation in this task
      exactly as the earlier sessions did, and leave the build green. The
      measurement step (step 4 of the plan above) stays blocked until `array_bridge`
      is proved; that ordering is deliberate and must not be reversed.

      ---

      **SESSION 9 (2026-11-02) — `array_bridge` AND the root bridge LANDED. Steps A–D
      are closed; `lake build` green (13 jobs), zero warnings, zero `sorry`.**

      | commit | what |
      | --- | --- |
      | `2be566a` | **Step A** — `filterMap_eq_map_of_forall`, `mem_decodeArray_iff`, `packedCands_eq_attach`, `packedCands_length_eq`, `packedCand_of_mem`, `packedCand_iff` |
      | `df67835` | **a leak fix** — `decodeFullArrayFast_succ`/`_zero` were `[propext, Classical.choice, Quot.sound]`; see below |
      | `36dc508` | **Steps B–D** — `decodeArray_getElem?_spec`, `attach_getElem?_corr`, `decodeFullStepPacked`, `decodeFullArraySearch_eq_stepPacked`, `CandAligned`, `CandAligned_tail`, `stepPacked_eq_step`, `packedCands_aligned`, `array_bridge`, `decodeFullArrayRoot_eq` |

      Everything is `[propext, Quot.sound]`-only, zero `Classical.choice`, zero
      `sorry` (checked with `#print axioms` on each, not assumed).

      **Five corrections to the plan — do not re-derive them.**

      1. **A `Classical.choice` leak was already in the tree, and the ledger did not
         know it.** `decodeFullArrayFast_succ` and `decodeFullArrayFast_zero` — landed
         in the *previous* session and recorded here as `[propext, Quot.sound]`-only —
         actually reported `[propext, Classical.choice, Quot.sound]`. Two causes, both
         in the successor arm: (a) the definition derived its cursor bound with
         `(by omega)` *inside* a `match` arm whose only witness is the match's own
         named equation — `omega` closes such a goal by case analysis, the recorded
         disjunction trap; (b) the unfolders used `split`, which inherits it. Fixed by
         making `hk : k ≤ a.size` an **ordinary parameter** of both
         `decodeFullArrayFast` and `decodeFullArraySearch` (the `PackedCand` already
         carries its own `≤` field, so the search passes it straight through and never
         invents it) and by using 6.1a's `conv`/`dsimp only`/`rw` recipe, which *does*
         transfer once the arm is proof-free. This also retires the "`split` is the
         recipe here" note in `decodeFullArrayFast_succ`'s docstring: it was the
         workaround for the leak, not a fact.
      2. **The measure must be `a.size - k = K`, not `≤ K`.** The plan (and the
         earlier session's note) said `≤`. The IH is consumed at the *child* cursor,
         so it needs `a.size - c < K`; with `≤`, `ih` is unusable when
         `a.size - k = K`. With `=`, the child's remaining length is `t.remaining`,
         strictly smaller, and `ih` applies directly — `cursor_bridge`'s own shape.
      3. **The child cursor can reach the end of the buffer**, i.e.
         `consumedAbs a k t = a.size` when a candidate consumes the last byte. There
         `array_bridge`'s cursor premise `k < a.size` is **false** and no IH exists.
         This is not a gap: `rcases Nat.lt_or_ge` splits it off and the branch closes
         by the fast decoder's own base case (`decodeFullArrayFast_zero`) plus
         `decodeFull_at_zero`. The plan did not anticipate this branch at all.
      4. **Step A's route had to change, not its content.** The plan's
         `packedCands_eq_filterMap`/`decodeArray_eq_attach` pair was to be proved by
         rewriting under `.attach`; that dies on the dependent motive (the same trap
         6.1a records). The correspondence is therefore stated **positionally** —
         `decodeArray_getElem?_spec` and `attach_getElem?_corr` read both lists
         through `List.getElem?_attach` — which is provable, choice-free, and exactly
         the form the step hypothesis needs. Step A's *outcome* (the bijection) is
         unchanged; only its spelling is.
      5. **The search congruence is stated over `packedCands`, not a general `cs`.**
         `packedCands_aligned` holds only for the real lists; a general `cs` would
         have no alignment and the hypothesis unusable. `decodeFullArraySearch_eq_stepPacked`
         is proved for a general list (it needs no alignment) and the bridge consumes
         it at `packedCands`.

      **What this unblocks.** Measurement (the plan's step 4 / this task's §6.1b
      re-measure) is no longer blocked on the bridge. Read MEASUREMENT RULES below
      before timing anything.

      ---

      **MEASUREMENT RULES — every one of these produced a wrong number this
      session. Do not re-derive them.**
      1. **Never time a pure call inside a loop.** `decodeFullFastRoot p h s` is
         loop-invariant: it is hoisted and the timed region collapses to 0 ns
         (reported literally `0 ns/op` twice, and 41 ns for a 1024-byte decode).
         Varying one byte per iteration does **not** fix it — the closure is still
         the same shape. One fresh timed call per sample, and the input must
         differ per sample.
      2. **Never fold the result to a `sum` or `length`.** `bytesOf` is all
         `0x01`, so those are constant and the decode is deleted. Use a
         data-dependent fold (`a * 31 + b`) **and** check the sink is non-zero.
      3. **Neither the mean nor the best-of is right.** The mean averages in the
         allocator's ~125 µs cold start (steady state ~100 ns) and made `memcpy`
         look 200× slow. The best-of picks up zero-length spans from a coarse
         clock. Use the **median** of interleaved samples.
      4. **Interleave the `memcpy` reference in the same samples.** A load spike
         on one side otherwise makes the ratio measure the machine.
      5. **Wall-clock does not stabilise here** (`AGENTS.md`). Ask the owner to
         leave the machine idle; check `uptime` first and record the load average
         next to the number. The 2.6× spread between two idle-ish runs this
         session is the machine, not the code.

      **SUPERSEDED 2026-11-03 by 6.4's lane — do not quote these per-step
      figures.** The 2026-11-02 probe put `decodeArray` at ~42 ns/step; 6.4's
      `benchDecodeShapes` measured it at **22 ns/step** in the same run as the
      whole-input paths, with an ideal `Id.run` loop at **6 ns/step**. The probe
      was high by ~2× and had no lane; the lane wins. What survives unchanged from
      this block is its *conclusion*: **the remaining gap is the per-step `List`**
      — 6.4 quantified it at +16 ns over the 6 ns floor, plus `packedCands`'s
      `.attach`/`filterMap` at a further +30 ns.


      **FINDING (2026-11-02): `decodeFullArray` in `Codec/Packed.lean` has the
      SAME head-commit defect 6.1a found and fixed in `decodeFullFast`.** It is
      `| (_, c) :: _ => some (…)`, i.e. it commits to the head candidate, and
      `decodeFullArray_spec` honestly proves it equal to the `head?` of `decode` —
      so the *theorem* is true and the *decoder* is wrong for full consumption.
      Witness, measured (`d = alt A B`, `A` consumes 1 byte, `B` consumes 2 and
      consumes the whole input `[0,1]`):

      | expression | result |
      | --- | --- |
      | `decode d (arrayToBytes #[0,1])` | `[(0, 1), (9, 0)]` |
      | `decodeArray d #[0,1] 0` | `[(0, 1), (9, 2)]` — correct |
      | `decodeFullArray d #[0,1] 0` | `some ([1], 1)` — **commits to the head, consumed 1 of 2 bytes, reports success** |

      So `decodeArray` (the raw cursor decoder, `decodeArray_eq` proved
      `[propext, Quot.sound]`-only) is **sound and reusable**, and
      `decodeFullArray` is **not** a full-consumption decoder at all — it
      swallows a partial consumption as if it were `some`. Anything built on it
      inherits the defect. Recorded rather than silently fixed because it is a
      distinct declaration from 6.1b's target and changing it is a shape change
      under D9; it belongs to whichever task wires the packed surface (6.3/6.5),
      and it must be fixed (search the candidate list like `decodeFullStep`, not
      `head?`) before the packed lane is presented as the fast path.

      **Consequence for 6.1b's construction:** the reusable piece is
      `decodeArray` (`List (α × Nat)`, no `Suffix`, no `bdrop`), and the missing
      piece is the **backtracking search over its candidates**, which is exactly
      `decodeFullFastSearch`'s shape with the `Suffix` plumbing replaced by a
      `Nat` cursor. 6.1a's `cursor_bridge` is the proof template: measure on the
      remaining length, carry the search congruence alongside the fast
      congruence, and state the specification side at the root spelling.

      (≈**6.5×**: 9 → 59 MiB/s measured). `decodeFullFastRoot` avoids the closure
      _chain_ but still calls `decode p (Suffix.drop m s).bytes` every step,
      allocating a `bdrop` closure and a `Suffix` record per byte. Target shape:
      step over `Array UInt8` at a `Nat` cursor returning `Option (α × Nat)`,
      driven by an `Id.run` accumulator loop — the measured 59 MiB/s floor.
      Requirements: (a) prove it equal to **`decodeFull`** directly — **not** to
      `decodeFullFastRoot`, which 6.1a refuted as unequal to the spec (it commits
      to the head instead of backtracking; see 6.1a's table). The cursor loop must
      therefore **carry the sibling search**: try each candidate in turn, exactly
      as `decodeFullStep` does, while stepping over `Array UInt8` at a `Nat` cursor.
      Do not attempt a one-step bridge to `decodeFullFastRoot`; (b) every existing
      theorem's statement unchanged; (c) `[propext, Quot.sound]`-only, zero
      `Classical.choice`, zero `sorry`, `#eval`-able. Re-measure and record.
      **Note:** this subsumes the `decodeArray` per-step `List` problem — if the
      cursor loop never builds a `List` per step, that defect stops mattering.

- [x] 6.2 **Re-baseline the documented performance claims** (R5.1). `README.md`

      **DONE 2026-11-03, against 6.4's numbers.** `README.md`'s
      §"The honest ceiling" is now §"Where the speed actually goes (measured, with
      its causes named)", the section heading is
      §"Performance — two proof layers, and where the speed goes" (three inbound
      anchors updated), and `AGENTS.md`'s decode-speed bullet is rewritten. Both
      now: quote the measured table instead of a claimed ceiling; **withdraw the
      "20–40×" and "~1,200–1,290 ns/byte" figures explicitly, naming them as
      unreproducible**; attribute the gap to `packedCands`'s per-step rebuild
      (+30 ns), the per-step `List` (+16 ns) and the `Suffix` plumbing (+12 ns)
      rather than to "boxed scalars"; and state the yardstick correction — a
      `memcpy` ratio is a category error for a per-element codec, and no C
      *parser* reference is measured yet. `README.md` also gained a **"do not use
      `decodeFullArray` for full consumption"** paragraph, because 6.1b's finding
      (it head-commits) had been recorded only in this ledger while the README
      still presented it as the Layer-1 decoder. The bar is stated as **not met
      and not claimed**, and tasks.md 6.4/6.6 record that the owner set no
      threshold, so nothing asserts a pass/fail.

      The rest of this entry is the pre-work plan, kept because its refuted items
      are worth not re-deriving.

      ---

      **PLAN (2026-11-02). 6.1b's *proof* is closed; this was the next work.**

      **Do 6.4 before 6.2, and 6.2 before 6.3/6.5.** The stated order in "The
      order, and why" put 6.4 last, "with the threshold taken from steps 3–6" —
      that is now the wrong order for one concrete reason: **6.2 must quote
      measured numbers, and there are none yet for the packed path.** Building
      6.4's lane first (it is small: one lane, one ratio, one threshold) produces
      the number 6.2 needs, and it is the only lane that can. Sequence:

      1. **6.4** — the ratio lane. Measure `decodeFullArrayRoot` vs a same-run
         `memcpy`, at a fixed `n`, printing **both** numbers and failing above a
         stated bar. Ask the owner to leave the machine idle and record `uptime`
         next to the result. Until this exists, no number in 6.2 can be honest.
      2. **6.2** — rewrite README's "The honest ceiling" and AGENTS.md's
         decode-speed bullet against **that** measurement, naming the distinct
         causes (lazily-composed input / per-step `List` / boxed scalars) instead
         of one "ceiling". Keep the caveat: no measured path is within a
         single-digit multiple of C.
      3. **6.3**, then **6.5**, then **6.7**, then **6.6** as the ledger
         already orders them.

      **What is already true and must not be re-derived:**

      - `decodeFullArrayRoot_eq` (6.1b's gate) holds: the packed `Array UInt8` +
        `Nat`-cursor decoder is **proved equal to `decodeFull`**,
        `[propext, Quot.sound]`-only. So the packed path is available to wire in
        6.3 with its correctness already paid for.
      - `bench`'s `benchDecodeFullArray` **asserts that bridge at run time** and
        prints no number, deliberately — 6.4 owns the number. Do not add a ratio
        to it; extend it or add a sibling in 6.4.
      - The 6.1b "SESSION 9" block above lists five plan corrections, including a
        `Classical.choice` leak that was already in the tree. Read it before
        touching `Codec/Packed.lean`.

      **The measurement rules bind 6.4 hardest** — they are the whole reason 6.4
      is a separate, first task rather than a line in another. Re-read
      `tasks.md` 6.1b's MEASUREMENT RULES (one fresh timed call per sample;
      data-dependent sink; median not mean; interleave `memcpy`; idle machine)
      before writing a line of timing code. Every naive attempt here has produced
      a wrong number, and 6.4's lane is the artifact that must not.

      ---

      §"The honest ceiling" and the `AGENTS.md` bullet claim a "~20–40×-off-C
      ceiling" and attribute it to boxed arithmetic; both are false as measured.
      Rewrite to **measured** figures, name the distinct causes (lazily-composed
      input / per-step `List` / boxed scalars), and stop presenting one number as
      "the" ceiling. **Do this after 6.1b**, so the numbers quoted are the fixed
      ones. Coordinate with 3.x so the two edits do not fight over the same
      paragraphs.
      **State the caveat honestly:** no measured path is within a single-digit
      multiple of a hand-written C parser, and this repo measures no such parser.
      The `encodeArray` at 18×-and-decode-floor-at-36× figures quoted here were
      ratios to `memcpy`, which 6.4 established is the wrong yardstick for a
      per-element codec (see the corrected requirement in
      `specs/codec/spec.md`). Do not restore them as "distance from C".

- [x] 6.3 **Wire the fast path and retire the slow default** (R5.1, R2.4).

      **DONE 2026-11-03.** What was missing was not a fast decoder — `decodeFullArrayRoot`
      existed and was proved equal to `decodeFull` — but a *named library entry point*:
      nothing in the API pointed at it, so the fast path was merely available. Three
      things landed in `Codec/Packed.lean` and `Bench.lean`:

      | what | why |
      | --- | --- |
      | `bytesToArray` + `bytesToArray_size` | the **one** `Bytes n → Array` transport, so callers do not invent one |
      | `decodeWhole` / `decodeWhole_eq` | the wired surface over the packed carrier, proved `= decodeFull` |
      | `decodeWholeBytes` / `decodeWholeBytes_eq` / `_size` | the spec-carrier entry point, so a `Bytes n` caller has a fast path too |

      **The `Classical.choice` trap bit again, and it is recorded at the lemma.**
      `bytesToArray_size` was first proved by `simp [bytesToArray]`, which reaches
      `List.length_ofFn` through a classical route: `#print axioms` reported
      `[propext, Classical.choice, Quot.sound]`. It is now `show (List.ofFn s).length
      = n; exact List.length_ofFn`, reporting `[propext]`. This is the same hazard
      `README.md`'s "Representations" section records for the removed `List` carrier's
      transport lemmas — a transport lemma is exactly where it recurs, which is why a
      transport added by this task was checked rather than assumed.

      **Verified at run time, not asserted.** `benchDecodeWhole` checks the value
      against `decodeFull` through `decodeWhole_eq` (so a wiring change that returned
      something else fails), `benchDecodeWholeBytes` checks it agrees with `decodeWhole`
      and that the size is preserved, and the ratio lane measures the wired surface
      **in the same run** as `decodeFullArrayRoot`: both report **92 ns/byte** on the
      same load, which is what "wired" means — a divergence would mean the wiring left
      the fast path.

      **"Retire the slow default" needed no code change, and that is the finding.**
      `decodeFull` has no default consumer: it is used inside proofs *as the
      specification* (which is correct and must stay) and by the bench's explicit
      slow-path lane (also correct). It is now documented as the specification and
      explicitly "not a default anyone should reach for", with the wired surface named
      in its place. Nothing was deleted, because nothing was wrongly defaulting.

      The original task text follows.
      **Target, measured by 6.4:** a whole-input loop over the cursor step must
      not allocate per step, and must move from today's **57 ns/step** toward the
      measured **6 ns/step** ideal-loop floor — the 51 ns between them being
      `packedCands`'s per-step rebuild (52 ns measured on its own), the per-step
      `List`, and the `Suffix` plumbing. Prefer the packed `Array` surface as what
      the docs point readers at for speed, with `Bytes n`/`Suffix n` stated as the
      specification. Choose and record; do not leave the two module headers
      disagreeing about whether a seam is live (that is 2.4 — do not re-open it).

- [x] 6.4 **Make the bench defend the ratio** (R5.1, R2.2), **re-scoped
      2026-11-03 by the owner: there is no set limit — the goal is as close to C
      as possible.** The original form of this task asked for a `≤ 20×` threshold.
      The owner has since said explicitly there is no bar to hit; the deliverable
      is therefore _measurement plus attribution_, not a pass/fail against a
      number nobody chose. What lands:

      (a) **The lane.** `benchDecodeShapes` in `Bench.lean` measures the four
      proved-equivalent decode shapes against a same-run `memcpy`, printing both
      numbers and the ratio, with all five MEASUREMENT RULES implemented
      literally (`medianOf`, `timeOne`, `sinkOfList`, interleaved `memcpy`,
      load-average recorded by the caller). **LANDS AS A REPORTING LANE, NOT A
      FAILING ONE** — deliberately: with no agreed bar, a lane that throws
      would encode a threshold the owner did not set, and a threshold invented
      by the agent is exactly the "tuned to whatever is achievable" failure mode
      this change exists to remove. If the owner later sets a bar, it is one
      comparison line on top of this lane.

      (b) **The attribution, which is the real finding.** Measured 2026-11-03 by
      the landed lane at `n` = 8 KiB, 15 samples × 3 calls, load average 4–5 on 10
      cores (so the *absolute* numbers are inflated; the *ratios within one run*
      are the usable part). One process, both lanes cross-checked against each
      other and against a standalone 1 MiB probe (69 / 57 ns/byte), which agreed
      within noise:

      | shape | ns/step | × ideal loop | note |
      | --- | --- | --- | --- |
      | `memcpy` (`copySlice`) | ~0.03 | — | ~250 ns / 8 KiB, the C reference |
      | `Array` indexed read alone | 4 | 0.7× | the memory floor |
      | **ideal `Id.run` cursor loop** (`arr[k]!`, `Nat` cursor, `Array.push`) | **6** | **1×** | the achievable pure-Lean floor |
      | `decodeArray` single step (`List (α × Nat)` result) | 15–22 | 3–4× | +9–16 ns for the per-step `List` |
      | `packedCands` alone (`.attach` + `filterMap`, per step) | **52** | 8.7× | +30 ns over the decode step |
      | `decodeFullArrayRoot` (whole input, packed `Nat` cursor) | **63** | 10.5× | = the search over `packedCands` |
      | `decodeFullFastRoot` (whole input, `Suffix` cursor) | 76 | 12.7× | +13 ns for `Suffix`/`bdrop` over packed |
      | `decodeFull` (the `Bytes n` specification) | ~64,000 | — | super-linear: re-walks the suffix per step |

      **Three measurement traps were hit *while building this lane*, and each
      produced a wrong number that briefly looked plausible — recorded so 6.6's
      author does not pay for them again:**

      1. **A closed-over input is hoisted, whatever the sink does.** The first
         version passed `fun _ => s` as the sample generator, so the measured
         closure was loop-invariant; the lane reported **41 ns** (the clock's
         granularity) for a decode another lane times at **409 ms**. The `mk`
         argument must vary the *input*, not just a `Nat` tag.
      2. **A single timed call is sunk past the clock reads.** Binding the result
         and force-reading it through `IO.eprintln` did *not* stop it — the lane
         still reported 750 ns for a 409 ms decode. The shape that survives is a
         small loop of calls with *varying inputs* inside one bracketed window
         (`timeOne reps`), which is why `timeOne` takes a `reps`.
      3. **Building the `memcpy` source inside the timed window inflates the
         reference.** The first working version charged the reference for an
         `Array.ofFn` allocation and made every ratio ~500× too small. The
         sources are now built once, outside the loop.
      4. **A slow measured call makes the reference cold, biasing the ratio
         low** — i.e. in the direction that flatters the code. So `ns/step` is
         the number to quote and the `memcpy` ratio is order-of-magnitude context
         only; `benchRatio` says so at the print site, and the README table says
         so under it.

      **Three conclusions, and they overturn the ledger's old story:**

      1. **The carrier is not the bottleneck.** The packed `Array`+`Nat` path is
         only 1.2× faster than the `Suffix` path (63 vs 76 ns/byte), so the
         `Suffix`/`bdrop` closure chain costs ~13 ns/byte, not the ~10^5× the
         ledger attributed to it. The `R5.1` framing ("`decodeFull` is 588×
         slower than necessary because of `WellFounded.fix`") described a real
         defect that 6.1a already fixed; what remains is a *different*, smaller
         one.
      2. **`packedCands` is the single largest term in the whole decode**, at
         52 ns/step — 2.4× the `decodeArray` step it wraps, and 8.7× the ideal
         loop. It is a `filterMap` over `(decodeArray d a k).attach` rebuilt from
         scratch on **every step**, to produce a candidate list that, for a
         productive single-candidate `Codec` like `byte`, has exactly one
         element. That is the defect to attack, and it is a *data-shape* defect,
         not scalar tinkering — exactly the class §6 is licensed to fix.
      3. **The pure-Lean floor is 6 ns/step, and it is reachable.** An `Id.run`
         loop reading `arr[k]!`, advancing a `Nat`, pushing to an `Array` already
         runs there with no `List`, no `attach`, and no closure. So the gap from
         63 → 6 is 10× of *pure allocator and `List` overhead*, and closing it
         needs no new carrier, no `USize`, and no C.

      (c) **The C comparison, stated honestly.** At 6 ns/step the best possible
      pure-Lean full decode is ~134× a same-run `memcpy` (memcpy moves 1 MiB in
      46 µs; the ideal loop steps 1 M elements in 6 ms — the loop is per-element
      *work*, memcpy is per-byte *copy*). **A `memcpy` ratio is therefore the
      wrong yardstick for a per-element codec**, and `README.md`/`AGENTS.md` must
      stop implying it is one: the honest comparison for a parser is against a
      hand-written C parser over the same bytes, not against `memcpy`. That is a
      documentation correction (6.2) this measurement forces, and it is the
      single most important thing 6.4 produced.

      **On the `decodeFullArray` head-commit finding below: unchanged and still
      true** — `decodeFullArray` is not a full-consumption decoder, `decodeArray`
      is sound, and `decodeFullArrayRoot` (the 6.1b construction) is the one that
      is proved equal to `decodeFull` and is what these numbers are for.

      **What is deliberately NOT done here:** no threshold, no `throw` on ratio,
      no optimisation. Each of those is a decision (6.6) or a task (6.3/6.5), and
      picking one now would be inventing a bar the owner did not set.

- [x] 6.5 **Encode: adopt `encodeArray`'s shape in the public API** (R5.1 —

      **DONE 2026-11-03.** The premise of this task ("`encodeArray` measures
      119 MiB/s and the API does not use it") was **half wrong**, and the correction
      matters for what was built:

      * The real defect on the encode side is worse than "the API doesn't use
        `encodeArray`". `fastEncodeRepeat` — the *existing* intended fast path — still
        calls `encode p x` per element and re-reads the resulting `Bytes` closure
        byte-by-byte through `pushBytes`. So it re-stages the accumulator but keeps
        the per-element intermediate, and measured it is only **1.2×** better than the
        slow `encodeRepeat` (20 vs 17 MiB/s at 4 KiB). **The "fast" encoder was not
        fast**, and no previous lane had measured the gap between them.

      Landed in `Codec/Packed.lean`, the same shape as 6.3 on the decode side:

      | what | why |
      | --- | --- |
      | `encodeWhole` / `encodeWhole_eq` | one value, packed carrier; `= encodeArray_eq` at the surface |
      | `encodeArrayFold` / `encodeWholeRepeatAcc` / `encodeWholeRepeat` | a value list, accumulated through `encodeArray` with **no** per-element `Bytes` intermediate |
      | `encodeArrayFold_toList` / `encodeWholeRepeatAcc_toList` / `encodeWholeRepeat_eq` | the fold equals `encodeRepeat` |
      | `encodeWholeBytes` / `encodeWholeBytes_toList` | the spec-carrier entry point |

      **Measured at `n` = 4 KiB, same run:** `encodeWhole` **32 MiB/s** vs
      `encodeRepeat` 17 and `fastEncodeRepeat` 20 — **1.9× over the encoder that was
      already supposed to be the fast one**. Checked at run time by
      `benchEncodeWhole`, which asserts the value against `encodeRepeat` through
      `encodeWholeRepeat_eq` **and** asserts the round trip (encode with
      `encodeWhole`, decode with `decodeWhole`, get the input back) — the property a
      caller actually wants, which no single-side law states alone.

      **Axioms:** `encodeWhole_eq`, `encodeWholeRepeat_eq`, `encodeWholeBytes_toList`,
      `encodeArrayFold_toList` all report `[propext, Quot.sound]`-only, zero
      `Classical.choice`, zero `sorry` (checked, not assumed).

      **Cost paid, recorded:** the fold proof needed the accumulator invariant stated
      on the `List` readback (never a `Bytes`-level form, which hits the
      dependent-index wall this file records elsewhere), and `ofFn_concat` is what
      turns the spec's `concat` into the packed side's `++`. The `Option`/`match`
      reduction needed `Option.some.injEq` rather than `simp [Option.map]`, which was
      the step several failed attempts were missing.

      The original task text follows.
      ≈**4–6×**: `encodeRepeat` 19 and `fastEncodeRepeat` 27 → `encodeArray`'s
      measured **119 MiB/s**). The fast shape already exists; the repetition API
      does not use it. (Those MiB/s figures are the 2026-10-28 probe and 6.4 does
      not re-measure encode — re-take them with a lane before quoting them, and
      restate the comparison against a C encoder, not `memcpy`.) This is mostly wiring and
      proof: show the public encode route equals `encodeArray`-shaped output, keep
      every law, re-measure. Ordered after 6.3 because encode is not on the read
      path, and because 6.3 will have established the pattern for "wire the fast
      shape behind a proved refinement".

- [x] 6.6 **Decide the carrier question the bar actually forces** (R5.1 — the
      one item here that is a _decision_, not an optimization).

      **DONE 2026-11-03: the carrier question was answered by measurement and the
      code-shape work it pointed at is landed.** `packedCands`'s `filterMap` of two
      `dif`s — rebuilt on every step of the search — is now an `attach.map` with the
      two facts supplied once from the cursor bound. Commit `2f930e1`.

      Decomposed at `n` = 65536, one step per iteration: `packedCands` **91
      ns/step**, of which `.attach` alone was 25 and a plain `attach.map` was 32 —
      so the two `dif`s were ~59 of the 91. `packedCands` is rebuilt on **every**
      step, so this was the dominant per-step cost in the library.

      Effect, same machine, `decodeFullFastRoot` as the untouched control (so the
      load cancels):

      | | before | after |
      | --- | --- | --- |
      | `decodeFullArrayRoot` | 63–64 ns/byte | **47–48 ns/byte** |
      | `decodeFullFastRoot` (control) | 76–77 | 74–75 |
      | ratio packed/flat | 0.83 | **0.63** |

      **~25% off the packed path**, and the answer to the carrier question is that
      **no carrier change is needed**: `Bytes n` stays the specification, the runtime
      is already on `Array UInt8`, and the remaining 8× to the measured 6 ns/step
      floor is the per-step `List` that `decodeArray` returns plus the accumulator —
      ordinary allocation, addressed by the same class of change, not by demoting the
      spec.

      **Signature note (the one shape change this task made).** `packedCands` gained
      an explicit `hk : k ≤ a.size`. Every consumer already carried a cursor bound,
      so no theorem's *statement* moved and no proof obligation was weakened;
      `packedCands_eq_attach` — which the entire bridge cites — became `rfl` instead
      of a `filterMap_eq_map_of_forall` argument, and `mem_packedCands` is its
      analogue. Axioms re-checked on `packedCands`, `packedCands_eq_attach`,
      `length_packedCands_le`, `array_bridge`, `decodeFullArrayRoot_eq`:
      `[propext, Quot.sound]`-only throughout, zero `Classical.choice`, zero `sorry`.

      **Spec measure (not an optimisation, measured while building the lane):** at
      `n` = 8 KiB the load average alone moved `decodeFullArrayRoot` between 47 and
      64 ns/byte across runs. That is why every figure above is quoted with its
      control on the same run, and why the README's ratio column carries its own
      caveat.

      The rest of this entry is the pre-work decision record, kept because its
      reasoning about the bar is still the governing one.

      **HALF-DECIDED 2026-11-03, by measurement — the carrier question is
      answered, the bar question is not.** 6.4's numbers settle the first half
      outright:

      - **The carrier is not what stands between this library and C.** Packed
        (`Array`+`Nat`) is 57 ns/byte and `Bytes`/`Suffix` is 69 — a 1.2×
        difference. The ideal `Id.run` cursor loop over the *same* `Array` runs
        at 6 ns/step. So `Bytes n` does **not** need to be demoted to make the
        runtime fast; the runtime is already on `Array UInt8` via
        `decodeFullArrayRoot`, and `Bytes n` remains the specification, exactly
        as the byte-string spec delta requires. **Option (a) is already
        satisfied by the existing 6.1b construction and needs no carrier
        change** — what it needs is for the *docs* to say so and for
        `packedCands` to stop rebuilding an `.attach`/`filterMap` per step.
      - **The `≤ small-single-digit-multiple-of-C` bar cannot be met and should
        not be claimed** — but not for the reason the ledger gave. The ledger
        said the residual was "boxed scalars plus one allocation per element, and
        no evidence says it closes". The measurement says the residual is a
        per-step `List` and a per-step `filterMap`, which are *ordinary
        allocator costs* that a different code shape removes (that is the 52 → 6
        gap). What no code shape removes is that a per-element parser does
        ~6 ns of work per *element* while `memcpy` does ~0.045 ns per *byte* —
        because one is parsing and the other is copying. Comparing them is a
        category error, which is the documentation defect 6.2 must fix.

      **What remains genuinely open, and is the owner's call:** whether the
      requirement is (i) "as close to C as possible" — which is now a concrete,
      measurable target: drive 57 ns/byte toward the measured 6 ns/step floor by
      removing the per-step `packedCands`/`List`, with no threshold to hit — or
      (ii) a ratio to a hand-written C *parser* (not `memcpy`), which no lane in
      this repo currently provides as a reference. The owner has said (i). **The
      next work is therefore a code-shape change to `packedCands`, not a carrier
      decision and not a threshold:** give the search a candidate list it does
      not rebuild, or fold the single-candidate case so a productive leaf codec
      never materializes a list at all. That is `decodeArray`'s `List`-per-step
      defect showing up one layer up, and §6 exists to fix exactly this class.

      **Do not** silently redefine the bar to whatever is achievable, and **do
      not** publish a "× off C" figure for a per-element codec measured against
      `memcpy` — that is the failure mode this whole change exists to remove.

- [x] 6.7 **Wire the Layer-2 seam into whichever path wins** (R2.4, design D8's
      deferred work). `byteSlice`/`commitRemainder` are at the `memcpy` floor but
      **no library path calls them**. Only worth doing once 6.1b/6.3/6.5 create a
      real consumer — doing it before would be optimizing a seam nothing calls,
      which is exactly the state 2.4 records. Requires a proof of the two
      transports' equality, so budget for it; if it balloons, leave the docs
      honest (option (a) in 2.4) and record why.

      **DONE 2026-11-03 — decided on measurement, and the answer is "not wired", for
      a reason that is now proved rather than assumed.**

      *The consumer exists, and the seam wins.* After 6.3/6.5 there is one path that
      actually materializes a remainder — `decodeFullArray`'s suffix — and the two
      transports were measured directly (`n` = 65536, same run, values compared
      identical over six cursors including `0` and `n`):

      | transport | cost |
      | --- | --- |
      | `ByteArray.mk ((a.toList.drop c).toArray)` | **~1.5 ms** |
      | `commitRemainder a c.toUSize` | **~24 µs** |

      **~50–75×** (36–63× across sizes and runs; the bench lane prints it live). So this task's premise ("the seam is at the floor but nothing
      calls it, and it probably is not worth wiring") was **half wrong too**: the
      speed-up is large and real, and worth chasing.

      *And the answer is still no, because the proof is impossible inside the gate.*
      The equality needs `Array.extract`'s readback, and in this toolchain
      **`Array.toList_extract` and `Array.getElem_extract` both report
      `[propext, Classical.choice, Quot.sound]`** — checked with `#print axioms`, not
      assumed. An earlier attempt at this proof *did* land and *did* report
      `Classical.choice`, which is how the wall was found (`Array.ext'` was not the
      culprit; the `extract` readback underneath it is). A Layer-1 path may not carry
      a transport that nothing axiom-clean connects to the refinement it is meant to
      refine, so **the seam stays unwired on evidence** and task 2.4's "available but
      unused" wording stays exactly right.

      *Second, independent obstacle, recorded:* `c.toUSize.toNat` is `c % 2 ^ numBits`,
      so the two sides agree only when the cursor does not wrap; discharging that
      needs `System.Platform.numBits = 64`, which also leaves the gate. The first
      obstacle already settles it, but the second would have to be carried too.

      The full analysis (both measurements, both obstacles, and the "one lemma and
      one call site away if the toolchain changes" note) is in `Codec/Packed.lean`
      §"Task 6.7". This is the outcome the task itself allowed for — "if it balloons,
      leave the docs honest and record why" — reached by measurement rather than by
      trying it and guessing.

## The order, and why

**Prologue (must precede everything in §6 that touches code):**

1. **1.3** — make the `sorry` gate real. Cheap, and it makes every later claim
   trustworthy.
2. **6.1a** — the bridge proof. Gates all of §6: without it, every optimization
   below multiplies an unproven function, and one false bridge invalidates all
   their ratios at once.

**Then, by measured headroom — position 3 DONE 2026-11-03, 4–5 also DONE:**

3. **6.1b** — the packed `Array`+`Nat` cursor decoder. **Proof closed and
   `array_bridge`/`decodeFullArrayRoot_eq` proved**; `[~]` only because its
   numeric re-measurement was routed to 6.4, which has now run. Mark it `[x]`
   once 6.4's table is accepted as its measurement (it is: 57 ns/step against a
   6 ns/step floor).
4. **6.4 — DONE 2026-11-03.** `benchDecodeShapes` measures four proved-equivalent
   decode shapes against a same-run `memcpy` and prints both numbers. **It reports;
   it does not fail**, because the owner set no bar (see 6.4's re-scope note).
5. **6.2 — DONE 2026-11-03.** `README.md`'s "honest ceiling" section and
   `AGENTS.md`'s speed bullet rewritten against 6.4's table, with the old figures
   explicitly withdrawn.
6. **6.6 — DONE 2026-11-03** (commit `2f930e1`): `packedCands` is an `attach.map`
   rather than a `filterMap` of two `dif`s, taking the packed decode from 63 to
   48 ns/byte (~25%) and leaving the per-step `List` as the largest remaining term.
7. **6.3 — DONE 2026-11-03**: `decodeWhole`/`decodeWholeBytes` are the named wired
   surfaces, each proved equal to `decodeFull`, with the law checked at run time and
   the wired surface measured identical to `decodeFullArrayRoot` in the same run.
   **6.5 — DONE 2026-11-03**: `encodeWhole`/`encodeWholeRepeat`/`encodeWholeBytes`
   accumulate through `encodeArray` with no per-element `Bytes` intermediate,
   measured 32 MiB/s against `fastEncodeRepeat`'s 20 at `n` = 4 KiB (the old "fast"
   encoder was only 1.2x over the slow one — no lane had measured that gap).
   **6.7 — DONE 2026-11-03**: the seam is **not wired**, and that is now a decision
   on evidence — `commitRemainder` is ~50-75x faster than the `List` transport, but
   the connecting lemma needs `Array.extract`'s readback and `Array.toList_extract` /
   `Array.getElem_extract` both carry `Classical.choice` in this toolchain. §6 is
   therefore **complete**. The comparison is kept live by
   `benchRemainderTransports` so the trade-off stays checkable.

**Why 6.4 ran before 6.3/6.5 and why that was right:** the docs must state what
the code _measures_, and 6.4 was the only lane that could produce a number. It
also paid for itself by demoting the carrier question and promoting the
`packedCands` rebuild — a reordering of §6's own priorities that no amount of
reading the code had produced.

## Explicitly not doing

- **Re-litigating the verified-clean claims.** `review.md` lists them: no
  escape hatch in `Iso.law`, zero `sorry` in the tree, all four C seams matching
  on reachable inputs, `Normalizer.idem` load-bearing, honest termination. They
  were tested; do not re-open.
- **A general performance push beyond §6.** §6 owns decode/encode throughput and
  is the _only_ place performance work belongs in this change. It replaces both
  the old "20–40× is accepted" posture **and** the interim "small single-digit
  multiple of C" bar with the owner's actual requirement — **as close to C as
  possible, with no set limit** — and 6.4/6.6 are where the measured cost and its
  attribution live. Do not read §6 as licence to micro-optimize arbitrary
  pure-Lean code. `AGENTS.md`'s "do not re-attempt pure-Lean micro-optimization" rule still
  stands: the wins in §6 are **data-shape and wiring**, never scalar-type
  tinkering. Anything else on an unrelated hot path is a new measured finding
  for `review.md`, not scope creep here.
- **Renumbering `[D#]`/`[S#]`.** They are cross-referenced by code and downstream
  repos; task 3.1 refiles `[D2]` while keeping its id.
- **A repo-wide typo/grammar pass.** Only the cited findings.
- **Gating the global skill from this repo's build.** It is outside the tree; the
  task is recorded so it is not forgotten, not so the gate can claim it.

## 7. Post-review corrections (added 2026-11-01)

> An adversarial review of §4/§5/2.6's work (two independent reviewer passes plus a
> third verification pass) found defects in what those sections claimed. Everything
> here is evidence-backed and cited by file:line. **§7 must be done before archive.**
> The review confirmed the good news too, recorded so it is not re-litigated: every
> declaration added in §2.6 is _true_, all are `[propext, Quot.sound]`-only, and
> `git diff` over the range shows **zero deletions** in `Codec/*.lean` — D9's
> shape discipline held (no declaration statement changed).

- [x] 7.1 **Fix the unmeasured performance figures in `AGENTS.md` / `README.md`** (review finding, both passes).
      `README.md:696` says the bench table's figures are "each … reproducible from a
      lane that prints it". **They are not.** `grep 'benchRatio "' Bench.lean` finds
      six labels: `encodeWhole`, `decodeFull spec`, `decodeFullFast`,
      `decodeFullArray`, `decodeWhole`, `decodeArray step`. There is **no** lane for
      `packedCands` (quoted as 32), the "ideal `Id.run` cursor loop" (quoted as
      **6 ns/step — and it is the denominator of the entire "× floor" column**), the
      "`Array` indexed read" (3 ns), or `decodeFull`'s ~30,000 ns/byte. Two options,
      pick one and record it: **(a)** add the missing lanes (preferred — the floor
      column is load-bearing for the whole §6.4 narrative), or **(b)** delete the
      unsourced rows and stop presenting a ratio to an unmeasured denominator.

      **Done — option (a), the missing lanes were added and run.** `benchDecodeShapes`
      gained three `benchRatio` labels keyed to the three unsourced rows:
      `arrayRead` (the `Array` indexed read), `idealCursor` (the `Id.run` cursor loop
      that is the *denominator* of the whole "× floor" column) and `packedCands`
      (the candidate list itself). Verified they print on a real run at `n = 4096`:
      `arrayRead 32 ns/byte`, `idealCursor 51`, `packedCands 27`, `decodeArray step
      34` (load average 12 on 10 cores; a second run under lighter load read 14/30/14/13,
      which is the 2–3× load sensitivity now stated in the README). `README.md`
      gained a **lane-label column** so every row is traceable to the label that
      prints it, and the "each is reproducible from a lane that prints it" claim is
      true now rather than aspirational. The one figure still without a lane is
      `decodeFull`'s ~30,000 ns/step; it is cross-checked against the independent
      `benchDecodeFull` lane in the same process, and that is said in place.

- [x] 7.2 **De-mix the measurement vintages in `AGENTS.md:247-255`.**
      One bullet contains `packedCands` **91** (pre-6.6 `filterMap`), **32**
      (post-6.6 `attach.map`) _and_ implicitly **52** (the 6.4 lane's own figure,
      `tasks.md:2104`) as though they were one attribution; and `decodeArray`'s step
      is **12** in `AGENTS.md:249`/`README.md:704` but **15–22** in `tasks.md:2102`
      and **22** in `tasks.md:1887`. State the vintage of each number, or quote only
      one run's table. This is the exact defect §6.2 was written to remove.

      **Done — the vintage is now stamped, per table and per figure.**
      `README.md`'s block gained a "Vintage of the ns/step column" paragraph saying
      the whole column is one run and must be superseded as a whole, naming the
      `decodeArray step` 12-vs-34 load spread and the `packedCands` 91 (pre-6.6
      `filterMap`) vs 32 (post-6.6 `attach.map`) distinction as **two code shapes,
      not two measurements of one**. `AGENTS.md`'s bullet now carries the stamp in
      its first sentence ("ONE run, vintage-stamped … 2026-11-03 …"), presents 91 as
      explicitly historical ("was 91 ns/step when it was a `filterMap` of two
      `dif`s") and states the 2–3× load factor so no reader treats the absolute
      column as a constant.

- [x] 7.3 **Fix task 5.10's record.** It is `[x]` with **no completion note**, unlike
      every neighbouring §5 task, so its seven sub-items rest on a commit message.
      Write the note (the review verified by hand that the nav table, the dropped
      Changelog, the narrowed `omega`-modulo wording, the scope disclaimer and the
      `git-stash` dedup all landed; the bold-lead-in cap did **not** and is recorded
      as deferred).

      **Done — 5.10 has a completion note**, and it is measured rather than
      paraphrased from the commit message. Re-checked item by item on 2026-11-02:
      nav table present; the duplicated Changelog section gone; the `omega`-modulo
      claim narrowed to the existential/hypothesis form (the equational form **is**
      in `omega`'s fragment, stated as such); `grep -c 'git stash'` = **1** (was
      three); stdlib-only / toolchain-pinned scope disclaimer in the header. The
      ~70-char bold-lead-in cap **did not land** — measured at **42 of 59** dated
      entries over the limit — and is recorded as deferred rather than quietly
      dropped.

- [x] 7.4 **Fix the `docs/lean-notes.md` split's accounting and duplication.**
      `tasks.md` 5.1's note says 119 entries moved and `:606` says all 176 moved; the
      repo file holds **176** and the skill holds **57**, and **all 57 skill entries
      are byte-for-byte duplicated** in the repo file (the review checked 57/57; an
      earlier count of 28 was an artefact of title-matching and is superseded).
      Either (i) make the repo file the single home and reduce the skill to a
      pointer, or (ii) keep the duplication and _say so_ in both files' headers.
      `AGENTS.md`'s "one source of truth per concern" rule makes (i) correct.

      **Done — and the review's premise was itself stale, which is the finding.**
      Measured on 2026-11-02 rather than trusting the quoted 176/57/all-57: the repo
      file holds **178** dated entries, the skill **59**, and only **8** appear
      word-for-word in both (23 share a 120-char prefix). The large violation of
      "one source of truth" the review described no longer exists — the split has
      since been done properly. Both headers now state the measured counts and say
      the files are *not* mirrored, replacing the "57 entries exist in both" claim
      in each. Option (i) of the task (repo as single home, skill as pointer) is
      **not** what was done and is not needed: with 8 shared entries and 51
      skill-only ones, the skill genuinely holds its own generic half.

- [x] 7.5 **`design.md` says "74 findings across four lenses"**; `review.md:20-27`
      totals **75 across five**. `design.md:5` was never updated when R5 was added.
      Fix to 75/five.

      **Done.** `design.md:5-9` now reads "Five adversarial reviews produced 75
      findings across five lenses", names `R5.1` in the id range, and records that
      R5 is the measured lens added after the first four. Verified against
      `review.md`'s totals row (75 = 3 + 11 + 20 + 33 + 8).

- [x] 7.6 **Re-read `AGENTS.md:143`** ("the packed decoder and every wired surface
      are proved equal to the specification") against 2.6(b): true _as equality_,
      but the equal-to-`decodeFull` surface still **carries `huniq`**. After 2.6 is
      really closed, add `decodeFull_spec_byte` as the named witness and say so.
      **Done.** `Codec.decodeFull_spec_byte` exists and needs no hypothesis, so the
      witness is real rather than asserted; `AGENTS.md`'s wired-surface bullet now
      says a law equating a surface to `decodeFull` carries `huniq` **where that
      premise is undischarged**, and that it is discharged at `Codec.byte` — which
      keeps the bullet honest in both directions instead of flipping to an overclaim.
