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
> **Consequence for 6.4:** the `≤ 20×` bar is unmet by roughly **two to three
> orders of magnitude** on the only path that claims to be fast. No threshold can
> be chosen until 6.1b lands, and **no number in this block may reach
> `README.md`.** 6.1b is not an optimization to schedule after the docs work — it
> is the difference between the claim being off by 20x and off by ~10,000x.
>
> What this does **not** change: `decodeFullFastRoot = decodeFull` is proved
> (`[propext, Quot.sound]`-only), so the fast path's _correctness_ rests on the
> theorem, not on measurement. Only its speed was ever undocumented, and the speed
> is now documented and bad.

- [ ] 6.1 **Bridge the fast decode, then move it onto a cursor** (R5.1 —
      CRITICAL). Two halves; **6.1a is a hard gate on 6.1b and on 6.3/6.4.**

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

- [ ] 6.1b **Move the fast decode onto an `Array UInt8` + `Nat` cursor**

      **PLAN FOR NEXT SESSION (2026-11-02). Start here. Nothing below is
      speculative — every fact is proved or measured, and the one open item is
      named exactly.**

      *State.* `decodeArray` (`Codec/Packed.lean:59`) is the reusable cursor
      decoder: `List (α × Nat)`, no `Suffix`, no `bdrop`, proved equal to `decode`
      by `decodeArray_eq` (`[propext, Quot.sound]`-only). `decodeFullArray` must
      **not** be used — it commits to the head (see the FINDING above). The only
      missing piece is the **backtracking search over `decodeArray`'s candidates**,
      which is `decodeFullFastSearch` with `Suffix` replaced by a `Nat` cursor.
      In probe form it already returns the right values (`some [9]` on the
      backtracking witness, `some [1,2,3]`, `some []`); what does not compile is
      its `decreasing_by`.

      **Step 1 — `Codec.decodeArray_consumes`: DONE, in `Codec/Packed.lean`.**
      Proved, `[propext, Quot.sound]`-only, `lake build` green. It sits **after**
      `decodeArray_eq` (which it uses), so a later addition near the top of the
      file will not see it. Statement and proof for reference:
      The strict-decrease fact, without which the search is not well founded:

          theorem decodeArray_consumes {α} (d : Codec α) (h : ConsumesByte d)
              (a : Array UInt8) (k : Nat) :
              ∀ (x : α) (c : Nat), (x, c) ∈ decodeArray d a k → k < a.size → k < c

      Proof: `rw [decodeArray_eq]` at the membership, `simp only [List.mem_map]`,
      `obtain ⟨⟨y, t⟩, hmem', heq⟩`, inject `heq`, then
      `show k < consumedAbs a k t; unfold consumedAbs`, take
      `hroot : t.remaining < a.size - k` from `h y (bdrop k (arrayToBytes a)) t hmem'`
      and close with `hk' : k ≤ a.size` + `omega`. **Copy it from this
      description — it is 10 lines and it is the whole mathematical content.**

      **Step 2 — the mutual pair, MIRRORING `decodeFullFast`. Next action.** Do not invent a
      variant. `Codec/Decode.lean:219-268` is the same construction (decoder ⇄
      candidate search, `Prod.Lex` measure, cursor advanced by what a candidate
      consumed) and it elaborates. Copy its shape exactly:

      - equation-style bodies (`| k, acc, cands => …`), not named parameters;
      - `termination_by` naming those **pattern variables**
        (`termination_by a k _ cands => (a.size - k, cands.length)`);
      - both functions' `termination_by` must have the **same type**
        (`Prod.Lex` in both), or Lean errors "termination measures must have the
        same return type";
      - the two `decreasing_by` tails are then literally: `search → decoder` =
        `Prod.Lex.left _ _ (by have hc := decodeArray_consumes … hk; omega)` and
        `search → search` = `exact Prod.Lex.right _ (Nat.le_refl _)`.

      **The one place the shapes genuinely differ — expect to think here.** The
      wrapper branches on `k < a.size` where `decodeFullFast` branches on
      `n - m = 0`. That guard is what supplies `hk` to `decodeArray_consumes`.
      Thread it as an **explicit hypothesis parameter** on the search
      (`(hk : k < a.size) → …`): the `if hk :` binder is not reliably in scope
      inside `decreasing_by`, and **`rename_i` will not recover it** — 15 attempts
      this session died on `rename_i`/`too many variable names provided`. With
      `hk` explicit, the obligation is one `omega`.

      **Do NOT** substitute the search by explicit `WellFounded.fix`. It avoids
      `decreasing_by` but changes the reduction equation to `WellFounded.fix_eq`,
      which is precisely the trap 6.1a lost seven sessions to; every downstream
      proof would need `unfold; rw [WellFounded.fix_eq]` instead of
      `rw [….eq_def]`.

      **Step 3 — the bridge.** `cursor_bridge` (6.1a, in the tree) is the
      template: measure on the remaining length, carry the search congruence
      alongside the fast congruence in one conjunction, and state the
      specification side at the root spelling. Target:

          fullArrayRoot d h a = decodeFull d h a.size (arrayToBytes a)

      `[propext, Quot.sound]`-only, zero `Classical.choice`, zero `sorry`.

      **Step 4 — measure, then stop.** Add the timing lane only after the bridge
      is proved. Read the measurement rules below first; they cost this session
      most of a day.

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

      **Baseline to beat, measured on an idle-ish machine (`ns/byte` flat in `n`
      ⇒ real per-byte work, not overhead):**

      | path | ns/byte | vs `memcpy` |
      | --- | --- | --- |
      | `decodeFullFastRoot` | 1,200–1,290 | 3,700×–21,000× |
      | `decode` at a cursor, single step | ~42 (per step) | — |
      | `decodeArray` single step | ~42 (per step) | — |

      So a correct cursor loop that pays ~42 ns/step would land near **24 MiB/s**
      — a 20–30× win over today — and would still be well short of the `≤ 20×`
      bar. **The remaining gap after this task is the per-step `List` that
      `decodeArray` allocates**, which is what 6.6's carrier decision is about.
      Record the measured number; do not tune the bar to it.


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
