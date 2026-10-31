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

- [ ] 2.1 **Add `byteSlice_spec`** (R2.1 — HIGH; design D4).
      The headline seam has **no** Lean law while `blitBytes_spec` and
      `findByte_spec` do. Add:
      `theorem byteSlice_spec (a : ByteArray) (i : USize) : byteSlice a i = ByteArray.mk (a.data.extract i.toNat a.data.size) := rfl`
      (verified to compile by the reviewer). Have `commitRemainder_spec` cite it,
      and have the bench cite it instead of re-deriving the body inline.

- [ ] 2.2 **Make the seam value-checks reachable** (R2.2 — HIGH; design D5).
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

- [ ] 2.3 **State `findByte`'s arithmetic side condition** (R2.3).
      The Lean body returns `some (off + i.toUSize)` (`USize` addition, i.e.
      mod 2^64); the C returns the absolute index as a raw `size_t`. These agree
      only under `off.toNat + i < USize.size`, which no theorem states. Add the
      condition to `findByte_spec`'s docstring and note the C relies on it — or
      spell the equivalence out. Do not leave "matches on every input" stronger
      than the Lean body's own arithmetic warrants.

- [ ] 2.4 **Reconcile the surface and transport descriptions** (R2.4, design D8).
      `Packed.lean`'s header says the memcpy "is deferred to a
      `commitRemainder` at commitment time"; the proven `decodeFullArray` builds
      its suffix with `ByteArray.mk ((a.toList.drop c).toArray)` and **no**
      library path calls `commitRemainder`. Replace with `ByteSlice.lean`'s
      honest phrasing: the seam is _available_, and the proven path deliberately
      uses the axiom-clean transport. Two headers SHALL NOT disagree about
      whether a seam is wired in.

- [ ] 2.5 **State per-law axiom footprints in `ByteSlice.lean`** (R2.6).
      `findByte_spec` reports `[propext]` while its siblings report none,
      because `Array.findIdx?` goes through `DecidableEq UInt8`. Record that in
      the docstrings so it is not mistaken for drift.

- [ ] 2.6 **Record or retire the dead API and unproved premise** (R2.5, R2.7).
      (a) `Iso.element`/`Iso.subset` have zero callers. Either delete, or add a
      one-line "public API, no in-tree caller" note — leaning retain, because
      `[D8]`'s corrected decidable-witness argument is about exactly these
      two (task 3.9).
      (b) `decodeFull_spec` takes full-consumption uniqueness (`huniq`) as a
      hypothesis and nothing in-repo supplies it. Either derive it from
      `relUnambiguous` (which the repo already has) as
      `decodeFull_spec_unambiguous`, or add one concrete instance so the
      hypothesis is demonstrably satisfiable in-tree.

- [ ] 2.7 **Fix the C comments' overclaim** (R2.11, R2.12).
      `blitBytes`'s C agrees with the Lean body _value-for-value_ via `min`
      associativity/commutativity, not "term-for-term"; and the allocation-length
      invariant (`dstOff + copyLen ≤ n`, hence total length `n`) is implicit.
      Reword the comment to state the AC argument and the window invariant —
      the seam's trust argument must be stated, not implied.

- [ ] 2.8 **Discharge `Unambiguous`/`Functional` for a concrete codec** (R2.17).
      Both are defined and used as hypotheses but never established for any
      in-tree `d`. Add the trivial base instances (`Unambiguous Codec.byte`,
      `Functional Codec.byte`) as smoke tests, so a typo in the definition
      (e.g. quantifying over the wrong `s`) cannot go unnoticed.

## 3. `README.md`: correct the derivations, keep the quotations

- [ ] 3.1 **Refile `[D2]`** (R1.2 — CRITICAL; design D6).
      It sits under "Departures (observable-semantics changes)" while its body
      says "`codec` keeps it that way" — and the paper's `parse` filters to
      whole-string matches (`[x | (x, "") ← p s]`) while `decode` returns every
      `(value, remainder)` pair, i.e. a **superset** of the paper's `Rel`. That is
      a strengthening, not an observable-semantics departure. Move it to the
      `[S#]` section, **keeping the `[D2]` id stable** (it is cross-referenced),
      with a one-line continuity note. Also fix its §4.3 attribution: §4.3's
      `Rel` is the whole-string graph, and the README's own law
      (`Rel d x s ↔ (x, empty) ∈ decode d s`) states the true relationship.

- [ ] 3.2 **Strengthen the §7.5 hook** (R1.3).
      The quotation is verbatim-correct; "almost as an aside" and "muses"
      undersell the paper's own explicit deferral. Quote §5's stronger statement
      ("It is not safe because it is not checked that the two directions are
      really inverse to each other") as the motivating problem, and keep §7.5 as
      the follow-up sentence, quoted in full —
      "how the invariants of `Iso` values could be encoded in a dependently typed
      language" — so the "it" has its antecedent.

- [ ] 3.3 **Correct `[D4]`'s mechanism** (R1.4, R1.7).
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

- [ ] 3.4 **Reconcile `[S1]` with `[S4]`** (R1.5).
      `[S1]` lists `foldl`/`foldr` under "the strict law holds for every core
      `Iso` … unconditionally", but `Codec/Iso.lean` restricts `apply` to
      _terminal_ seeds — a domain restriction — and `[S4]` itself says the folds
      take "a _precondition_, not an unconditional law". Split `[S1]`: structural
      isos are unconditional; `foldl`/`foldr` hold on their terminal-seed domain
      with a `MeasureDecreases` witness. Do not leave the two anchors
      contradicting each other.

- [ ] 3.5 **Correct `[D7]`** (R1.6).
      (a) "per-element 'chain-isolated in both directions' precondition" is
      invented vocabulary with no paper counterpart and is not what `codec`
      requires. The real obligation is a `measure : α → Nat` plus a proof each
      step strictly decreases it (`MeasureDecreases`).
      (b) "`foldl` is the combinator `chainl1` actually needs" is misleading:
      there is **no `chainl1` value**; there is the triple
      `relChainl1`/`decodeChainl1`/`encodeChainl1`, which needs `Iso.foldl`
      **plus** the repetition triple **plus** a `ConsumesByte` witness.
      Say what is actually true; this anchor is what a porter reproduces.

- [ ] 3.6 **Fix `[S6]`'s diagnosis** (R1.8).
      `many` is a value because it is a polymorphic **function of the `Syntax`
      class** — i.e. `[D6]`'s typeclass embedding — not because Haskell is lazy.
      Keep strictness for the _AST/induction_ obstacle only, and add the
      checkable reason the AGENTS.md history records: the definitional cycle
      `Codec → Productive → Rel → Codec` (and the mutual-inductive escape failing
      the universe check). Cross-reference `[D6]`.

- [ ] 3.7 **Fix `[S6]`'s `sepBy` claim** (R1.9).
      It says `codec` derives `sepBy`/`chainr1` "(one-or-more, zero-or-more)";
      `Codec/Combinators.lean`'s `relSepBy` is **one-or-more only** and its own
      docstring says so, and the README's `[S5]`/`[S6]` lay section says
      one-or-more. Make both statements say: one-or-more `sepBy` (= `sepBy1`) and
      `chainl1`/`chainr1`; zero-or-more is `optional` of the one-or-more form.

- [ ] 3.8 **Fix `[D6]`'s 1:1 implication** (R1.10).
      The seven constructors are counted correctly, but the entry implies a
      literal translation of the paper's five `Syntax` methods. `satisfy` has no
      paper counterpart (it is a fused `subset p $ token` leaf); the paper's
      `token` is `codec`'s `byte`. Add that clause.

- [ ] 3.9 **Scope `[D8]` correctly** (R1.11).
      `Iso.element`/`Iso.subset` do take `[DecidableEq α]`/`[DecidablePred p]`,
      but `Codec.satisfy` still takes a bare `(UInt8 → Bool)` — exactly the
      "unverifiable `Bool`" the entry says was replaced, and it is the leaf a
      downstream author actually writes. Scope the claim to
      `Iso.element`/`Iso.subset`/`Codec.pure` and state plainly that
      `Codec.satisfy` keeps the paper's free-form predicate because a
      `DecidablePred` over `UInt8` would be no more checkable.

- [ ] 3.10 **Transcribe the paper's type headlines verbatim** (R1.12).
      Use `newtype Parser α = Parser (String → [(α, String)])` and
      `data Rel α = Rel [(α, String)]`, not the `::`-annotated forms. These are
      `[D1]`/`[D2]`'s headline types and a porter types them literally.

- [ ] 3.11 **Fix the abstraction block's signatures** (R1.18).
      `decode` takes `d` **explicitly**
      (`decode (d : Codec α) {n : Nat} (s : Bytes n)`), and the `Rel` law must not
      use a free `n` — bind it via `s : Bytes n` (or write `Suffix.empty _`).
      This block is the most-copied part of the README.

- [ ] 3.12 **The remaining LOW precision fixes** (R1.13–R1.17, R1.19–R1.22).
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

- [ ] 4.1 **Split the verification recipe by repository** (R3.4).
      It opens "In `../lean-basen`, from **its own** `nix develop`" and then lists
      `openspec validate --all` (**this** repo), an unqualified `nix flake check`
      (ambiguous between two different flakes), and a `BaseN` axiom probe. Give
      each repository its own subsection and its own commands, and mark inline any
      step that must run elsewhere.

- [ ] 4.2 **Fix the `nix build '.#bench'` contradiction** (R3.5).
      It is used as the post-`nix develop` example three lines above forbidding
      foreground builds. Replace with the dev-loop command `lake build bench`, and
      state that `nix build '.#bench'` exists (`flake.nix:58`) as the
      sandboxed/CI equivalent and is a long build (`nohup`, never foreground).

- [ ] 4.3 **Flag the `../lean-basen` bench lane as known-incomplete** (R3.6).
      The recipe presents `lake build bench` there as green, but that repo's task
      5.3 records that the `bench` exe is not wired as a flake target. Annotate
      the recipe line and note that 5.3 is a _verification-recipe_ item, not a
      docs nit, so it should be done first if the bench is needed.

- [ ] 4.4 **Record the `bad import Codec.Normal` rail** (R3.7 — the missing rail).
      Symptom, cause, fix: in `../lean-basen`, a `bad import 'Codec.Normal'` from
      the _sandboxed_ build means the flake's `codec` pin predates the module —
      **not** a bad import. Check
      `../lean-basen/flake.lock` → `nodes.codec.locked.rev` against
      `git log --oneline -1 -- Codec/Normal.lean` here, then
      `nix flake update codec` (targeted, not all inputs) and `lake update codec`.
      Explicitly: do **not** "fix" it by editing the importing Lean file.

- [ ] 4.5 **Trim `Current state` and fix its precision** (R3.8, R3.9, R3.12).
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

- [ ] 4.6 **Stop calling `bench` an "extraction"** (R3.10).
      `lakefile.lean` declares a plain `lean_exe bench` (`root := \`Bench`) that
links the Layer-2 C object; there is no extraction step. This also
contradicts `AGENTS.md`'s own "all codecs are pure Lean". Fix the wording
here **and** in `default.nix`'s comment, and state that §10.5 extraction is
      not implemented so nobody goes looking.

## 5. The global `lean` skill (outside this repo — do last)

> Path: `~/.pi/agent/skills/lean/SKILL.md` (2233 lines). Not gated by
> `lake build`; do not claim this repo's gate covers it.

- [ ] 5.1 **Split generic from project-specific** (R4.2 — HIGH).
      The header promises "no project names/paths"; there are ~130 hits
      (`Codec` 104, `Bytes n` 25, `relRepeat`/`Suffix`/`bdrop` 100+,
      `byteSlice`/`blitBytes` 8, `Iso.law` 4, `decodeNormal` 2). Keep the generic
      half in `SKILL.md`; move the project-specific body into this repo (an
      appendix the skill points at with one line).

- [ ] 5.2 **Resolve the precedence contradiction** (R4.3 — HIGH).
      The file says the official `lean4` skill wins on proof engineering; the
      official _Quality Gate_ permits `Classical.choice`, while this file forbids
      it in 37 places. As written the axiom discipline is silently overridable.
      Replace the precedence clause with an explicit order: (1) this file's
      stricter axiom gate, (2) the official skill's LSP/search/proof-engineering
      guidance, (3) this file's performance/layout notes.

- [ ] 5.3 **Add the missing leak lessons** (R4.1, R4.4 — HIGH).
      The disjunction leak (`decide_eq_true (by omega)`, task 1.4's probe) is
      absent; the Bool-`match`-in-goal entry is in the wrong place with a fix
      (`subst h; rfl`) that demonstrably fails. Add both generically, with the
      working fix (`cases b <;> simp_all`, or restate so the match isn't
      dependent).

- [ ] 5.4 **Correct the stale `ByteArray` claim** (R4.5).
      "Not provable mechanically" is qualified to Lean ≤ 4.30 and false on 4.34:
      `ByteArray.append_assoc` exists, and `(a.push b).data = a.data.push b` is
      `rfl`.

- [ ] 5.5 **Correct the `UInt64`-is-boxed claim** (R4.6).
      `UInt64` arithmetic lowers to `uint64_t` + `lean_uint64_add`; the boxed
      evidence cited is what happens at a boundary, not what arithmetic lowers to.
      Keep the measured lesson (a `USize` cursor was _slower_), delete the wrong
      generalisation.

- [ ] 5.6 **Surface `split_ifs`'s absence** (R4.7).
      It is buried at line ~1935 inside an unrelated dated entry. Promote it to
      the generic section, noting it is a _mathlib_ tactic and this project is
      stdlib-only — which is the actionable reason.

- [ ] 5.7 **Fix the `if_pos`/`if_neg` guidance** (R4.8).
      Both are deprecated (→ `ite_eq_left`/`ite_eq_right`), not just `if_neg`;
      and the replacements are **applied** (`exact ite_eq_left h`), not rewrites
      and not `Iff`s — `rw [ite_eq_right h]` and `.mpr` do not work.

- [ ] 5.8 **Complete the `-/` rule** (R4.9).
      Block comments nest, so a stray `/-` is as fatal as `-/`. Reword to "an
      unmatched `/-` or a `-/` inside a doc comment terminates it early or
      swallows the rest of the file".

- [ ] 5.9 **Add the single leak catalogue** (R4.10, R4.13).
      The `Classical.choice` material is scattered over ~7 locations with three
      date-ordering violations; add one table (leak source → probe → clean
      spelling) and fix the ordering. Note (per R4.13) that the _isolated_ probe
      is clean while the in-context use leaks — the isolated probe must not be
      used as a refutation.

- [ ] 5.10 **Remaining LOW tidies** (R4.11, R4.12, R4.14–R4.22).
      Nav table rows for §5/§6/Append with a topic index; cap bold lead-ins at
      ~70 chars so entries are greppable; drop the duplicated Changelog section
      that restates entries already present; narrow "omega cannot derive
      `n % 4 = 0`" to the _existential/modulo-hypothesis_ form (the equational
      form **is** in `omega`'s fragment); delete the `git stash` rule (duplicated
      in three places) and link the official File Handling Rules; add a scope
      disclaimer (stdlib-only, 4.34-pinned) and attach conditions to the
      "20–40× off C" figure.

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
> **The acceptance bar (owner requirement, 2026-10-28): decode and encode must
> run within a _small single-digit multiple_ of C, or the effort has no value.**
> See `review.md` R5.1 §"The feasibility answer" for the numbers, and the honest
> caveat at the end of §6.2 below: **no measured path reaches single digits yet**,
> and closing the last order of magnitude is an architecture decision, not an
> optimization (6.6).
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

- [ ] 6.1 **Bridge the fast decode, then move it onto a cursor** (R5.1 —
      CRITICAL). Two halves; **6.1a is a hard gate on 6.1b and on 6.3/6.4.**

- [ ] 6.1a **Prove `decodeFullFastRoot = decodeFull`** (the gate; ~9 MiB/s path
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

- [ ] 6.1b **Move the fast decode onto an `Array UInt8` + `Nat` cursor**
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

- [ ] 6.2 **Re-baseline the documented performance claims** (R5.1). `README.md`
      §"The honest ceiling" and the `AGENTS.md` bullet claim a "~20–40×-off-C
      ceiling" and attribute it to boxed arithmetic; both are false as measured.
      Rewrite to **measured** figures, name the distinct causes (lazily-composed
      input / per-step `List` / boxed scalars), and stop presenting one number as
      "the" ceiling. **Do this after 6.1b**, so the numbers quoted are the fixed
      ones. Coordinate with 3.x so the two edits do not fight over the same
      paragraphs.
      **State the caveat honestly:** no measured path is within a single-digit
      multiple of C. The best is `encodeArray` at 18×; decode's achievable floor
      is 36×. Either the bar applies to bulk operations and per-element codecs
      sit at a few tens of MiB/s, or the packed carrier must become primary
      (6.6). Do not claim the bar is met.

- [ ] 6.3 **Wire the fast path and retire the slow default** (R5.1, R2.4).
      **Target, measured:** a whole-input loop over the cursor step must not
      allocate per step and must land near the 59 MiB/s floor. Prefer the packed
      `Array` surface as what the docs point readers at for speed, with
      `Bytes n`/`Suffix n` stated as the specification. Choose and record; do not
      leave the two module headers disagreeing about whether a seam is live
      (that is 2.4 — do not re-open it).

- [ ] 6.4 **Make the bench defend the ratio** (R5.1, R2.2). No lane fails if
      decode regresses 200×, because `benchDecodeFull` asserts the _value_, not a
      bound. Add a lane measuring decode **against `memcpy` in the same run** and
      failing when the ratio exceeds a stated bar (**`≤ 20×`** at a fixed `n`,
      threshold chosen from the post-6.3 measurement with margin), **printing
      both numbers**. A ratio, not an absolute MiB/s: an absolute floor is
      machine-dependent and gets tuned down the first time CI is slow; the ratio
      to same-run `memcpy` is the property actually meant. Keep
      `benchSeamBoundaries` first in `main` (2.2(a)) — a bound that runs after a
      slow lane is unreachable evidence. **Set the threshold from 6.1b/6.3's
      numbers, not today's**, which is why this is 6.4 and not 6.0.

- [ ] 6.5 **Encode: adopt `encodeArray`'s shape in the public API** (R5.1 —
      ≈**4–6×**: `encodeRepeat` 19 and `fastEncodeRepeat` 27 → `encodeArray`'s
      measured **119 MiB/s**). The fast shape already exists and already measures
      18× off C; the repetition API does not use it. This is mostly wiring and
      proof: show the public encode route equals `encodeArray`-shaped output, keep
      every law, re-measure. Ordered after 6.3 because encode is not on the read
      path, and because 6.3 will have established the pattern for "wire the fast
      shape behind a proved refinement".

- [ ] 6.6 **Decide the carrier question the bar actually forces** (R5.1 — the
      one item here that is a _decision_, not an optimization). If "small
      single-digit multiple of C" is the real requirement, no pure-`Bytes n` path
      meets it: the residual from 59 MiB/s to 2,136 is boxed scalars plus one
      allocation per element, and no evidence says it closes. The choice:
      (a) make the packed `ByteArray`/`Array` surface the primary runtime
      carrier with `Bytes n` retained as the specification `Rel`/laws are stated
      over; or (b) narrow the bar to **bulk** operations and record that
      per-element codecs sit at tens of MiB/s. **Record the decision and its
      rationale here**, then propagate to `README.md` and `AGENTS.md`. Do not
      silently redefine the bar to whatever is achievable — that is the failure
      mode this whole change exists to remove.

- [ ] 6.7 **Wire the Layer-2 seam into whichever path wins** (R2.4, design D8's
      deferred work). `byteSlice`/`commitRemainder` are at the `memcpy` floor but
      **no library path calls them**. Only worth doing once 6.1b/6.3/6.5 create a
      real consumer — doing it before would be optimizing a seam nothing calls,
      which is exactly the state 2.4 records. Requires a proof of the two
      transports' equality, so budget for it; if it balloons, leave the docs
      honest (option (a) in 2.4) and record why.

## The order, and why

**Prologue (must precede everything in §6 that touches code):**

1. **1.3** — make the `sorry` gate real. Cheap, and it makes every later claim
   trustworthy.
2. **6.1a** — the bridge proof. Gates all of §6: without it, every optimization
   below multiplies an unproven function, and one false bridge invalidates all
   their ratios at once.

**Then, by measured headroom:**

3. **6.1b** (≈6.5×) — biggest win, directly attacks the bar, subsumes
   `decodeArray`'s per-step `List`.
4. **6.5** (≈4–6×) — cheapest big win; the fast shape already exists and
   measures 18×.
5. **6.2** — re-baseline the docs against the _fixed_ numbers.
6. **6.3**, then **6.7** — wire the fast path; wire the seam once there is a
   consumer.
7. **6.4** — assert the ratio, with the threshold taken from steps 3–6.
8. **6.6** — the carrier decision, which only becomes urgent once the numbers
   above make the residual explicit.

## Explicitly not doing

- **Re-litigating the verified-clean claims.** `review.md` lists them: no
  escape hatch in `Iso.law`, zero `sorry` in the tree, all four C seams matching
  on reachable inputs, `Normalizer.idem` load-bearing, honest termination. They
  were tested; do not re-open.
- **A general performance push beyond §6.** §6 owns decode/encode throughput and
  is the _only_ place performance work belongs in this change. It replaces the
  old "20–40× is accepted" posture with the owner's bar (**a small single-digit
  multiple of C**), but the bar is **not met** and 6.6 is where that gets
  resolved — do not read §6 as licence to micro-optimize arbitrary pure-Lean
  code. `AGENTS.md`'s "do not re-attempt pure-Lean micro-optimization" rule still
  stands: the wins in §6 are **data-shape and wiring**, never scalar-type
  tinkering. Anything else on an unrelated hot path is a new measured finding
  for `review.md`, not scope creep here.
- **Renumbering `[D#]`/`[S#]`.** They are cross-referenced by code and downstream
  repos; task 3.1 refiles `[D2]` while keeping its id.
- **A repo-wide typo/grammar pass.** Only the cited findings.
- **Gating the global skill from this repo's build.** It is outside the tree; the
  task is recorded so it is not forgotten, not so the gate can claim it.
