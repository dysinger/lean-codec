# Tasks

> **Surface (read first).** This change **REOPENS
> `codec-normal-form-case-quotient` (16/16) and `basen-rfc-conformance-theorems`
> (31/31)**. Those changes were marked complete on the strength of their own
> authored tasks; the review found 2 CRITICAL defects in that same work, so their
> completion claims are withdrawn. Both carry a `DO NOT ARCHIVE` banner, and
> **nothing is archived until §1–§4 below are green.** The 41 tasks are the
> remainder of the previous changes' work, not polish on finished work.
>
> This change is **remediation of an adversarial review**, recorded verbatim in
> `review.md`. Each task cites findings as
> `R<lens>.<n>`, matching that file's index. Anchors `[D#]`/`[S#]` are **not**
> renumbered — only the text under them changes (design D6).
>
> **What must NOT change.** No theorem, proof, or declaration shape. No anchor
> id. No paper _quotation_ — R1 verified every quotation in `README.md` as
> verbatim-correct; the defects are in the **derived reasoning**. `review.md`'s
> "Verified-correct claims — do not re-litigate these" lists what was tested and
> held; re-opening those is out of scope.
>
> **Ordering.** §1 is the three findings that more than one lens reached
> independently (substrate type, unenforced gate, incomplete leak catalogue) —
> they are the ones that can cause a _wrong implementation_ or a _false sense of
> assurance_. §5 is last because it edits a file outside this repo.
>
> **Definition of done for every task:** the cited finding's evidence no longer
> reproduces, and `nix develop --command lake build` is green with zero warnings.

## 0. Correct the completion record (done — this is the mutual understanding)

- [x] 0.1 Both reopened changes carry a `STATUS: NOT COMPLETE — DO NOT ARCHIVE`
      banner at the top of their `tasks.md`.
- [x] 0.2 `AGENTS.md`'s `Current state` says **NOTHING IS COMPLETE**, explains
      that ticked counts are not completion claims, and records that
      `openspec validate --all` checks schema conformance, not truth.
- [x] 0.3 `AGENTS.md`'s archive section is retitled **BLOCKED** and states why
      archiving now would freeze the defective spec text into `openspec/specs/`.
- [x] 0.4 This change's `proposal.md` and `design.md` state that it REOPENS the
      two changes rather than adding a workstream beside them.

## 1. The three cross-lens defects (do these first)

- [ ] 1.1 **Correct `CHANGELOG.md`'s `Bytes` entry** (R1.1, R3.1 — CRITICAL).
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

- [ ] 1.2 **Pin the substrate type in `AGENTS.md`'s truth table** (R3.1).
      Add to the "Where the truth lives" table, or as a bullet immediately under
      it: `Bytes n` means `Fin n → UInt8` (`Codec/Codec.lean:68`) — this is the
      definition; `CHANGELOG.md` is a record, not a definition, and a
      `List UInt8`/`Array` spelling in any doc is a defect. Rationale: a
      corrected changelog can drift again; a stated precedence cannot.

- [ ] 1.3 **Make the zero-`sorry` proof gate real** (R3.2 — HIGH; design D2).
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

- [ ] 1.4 **Complete the `Classical.choice` trap catalogue, in one place**
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

- [ ] 1.5 **Qualify the `⟨_, rfl⟩` bisection heuristic** (R3.11).
      It is sound only when the goal is a sigma/`∃`. On a `decide … = true` goal
      it does not typecheck at all (so the prescribed bisection silently fails).
      Reword: "when the goal is a sigma/`∃`, bisect by shrinking the body to
      `⟨_, rfl⟩`; for other goal shapes prefer rewriting the proof shape."

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

## Explicitly not doing

- **Re-litigating the verified-clean claims.** `review.md` lists them: no
  escape hatch in `Iso.law`, zero `sorry` in the tree, all four C seams matching
  on reachable inputs, `Normalizer.idem` load-bearing, honest termination. They
  were tested; do not re-open.
- **Rewiring `commitRemainder` into the packed path.** That needs an equality law
  between two transports — a proof/perf change, its own change. Task 2.4 only
  corrects the header's claim.
- **Renumbering `[D#]`/`[S#]`.** They are cross-referenced by code and downstream
  repos; task 3.1 refiles `[D2]` while keeping its id.
- **A repo-wide typo/grammar pass.** Only the cited findings.
- **Gating the global skill from this repo's build.** It is outside the tree; the
  task is recorded so it is not forgotten, not so the gate can claim it.
