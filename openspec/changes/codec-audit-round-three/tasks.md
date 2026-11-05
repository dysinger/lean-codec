# Tasks

Evidence base: `/tmp/r3-a-codec.md`, `/tmp/r3-b-basen.md`, `/tmp/r3-c-cross.md`.
Order is strict. **Part 1** makes the laws exist and makes their absence a build
failure. **Part 2** fixes prose and the two remaining gate asymmetries. Part 2's
claims would be worthless before part 1, because there would be no laws to
describe.

Everything marked **measured** in the design was re-run before being recorded here.
One reviewer finding was refuted and is deliberately absent — see design D1.

---

## 1. Law coverage: close the `def`-level hole

### 1.0 `../lean-basen` gate parity — do this FIRST

- [ ] 1.0.1 Add `partitionInto`, `publicTheorems` and the two `run_cmd` checks to
      `../lean-basen/Axioms.lean`, mirroring `codec`'s
      (`Axioms.lean:120-136`, `:615-636`, `:653-683`). It currently has **zero**
      mechanism: `grep -cE 'run_cmd|Lean\.Elab|Environment|partitionInto|getEnv'
  Axioms.lean` → `0`, and 437 theorems vs 440 pins agree only by discipline.
- [ ] 1.0.2 Add a `generatedAuxAllowlist` for basen's own compiler auxiliaries,
      by name with a reason, so the partition is closed rather than merely added.
- [ ] 1.0.3 Verify load-bearing in **that** repo: add a throwaway public theorem,
      confirm `lake build` fails naming it, restore. Then add a stale pinned name
      and confirm the coverage check fails. Record both results in this file.
- [ ] 1.0.4 `../lean-basen` gates: `lake build` (25 jobs), `lake build bench`
      (45), `nix build '.#bench'` (detached, it runs the vectors).
- [ ] 1.0.5 Fix `lean-codec/lakefile.lean:28`'s now-backwards comment: it says the
      codec gate mirrors `../lean-basen/Axioms.lean` "which is where this shape is
      proven". Basen has the _shape_, not the mechanism. Record that codec
      strengthened what it inherited and basen now adopts it back — otherwise the
      next reader copies the weaker version.

### 1.1 `count`'s inductive step (root of five gaps)

- [ ] 1.1.1 Prove the step law `Rel (count (n+1) p) xs s` in
      `Codec/Combinators.lean`. `count`'s only law today is `Rel_count_zero`
      (`n = 0`); the step is where `Iso.cons` and `Codec.seq` do their work. This
      unblocks `manyUpTo`.
- [ ] 1.1.2 If the step does not close, record it as **open** in place with the
      precise blocking lemma named — never claim the derived combinators are
      proven. (Design D3's pre-authorized fallback.)
- [ ] 1.1.3 Add a bench-lane or `#eval` value check for the step at two concrete
      `n`, so the behaviour is exercised as well as proved.

### 1.2 `manyUpTo` — currently no law at all

- [ ] 1.2.1 Add the `List.range`/`map` membership lemma that does not exist: the
      link from `choice ((List.range (n+1)).map (fun k => count k p))` to "some
      `k ≤ n`". Without it `Rel_choice` cannot reach `count`.
- [ ] 1.2.2 Prove `Rel (manyUpTo n p)` in terms of `relRepeat` at a bounded length,
      so the value is tied to the repetition denotation rather than merely
      `#eval`-ed.
- [ ] 1.2.3 Document the **ordering** consequence measured at
      `Combinators.lean:89`: results are shortest-first (`[(0,2),(1,1),(2,0)]`), so
      a first-result consumer gets the empty list. `decodeOne` over a `manyUpTo`
      therefore always yields `[]`. That is the failure mode `[D3]` describes for
      committed choice, reintroduced in a derived value — say so at the definition.

### 1.3 `seqRight` / `seqLeft` / `between` — zero theorems

- [ ] 1.3.1 Prove the `Rel` characterization for each (`Combinators.lean:47,52,56`).
      These are `Iso` rewrites over `Codec.seq`; `between` is the paper's own §6.1
      combinator, so a porter reaches for it first and currently finds no proof.
- [ ] 1.3.2 Fix `seqRight`'s docstring (`:47-49`): it states
      `commute ≫ inverse unit : Iso (Unit × α) α`, which is the wrong intermediate
      type. With no theorem stating an equality, the type is only ever checked at
      the definition site, where Lean fills it in — the exact error class that "a
      docstring type with no theorem" permits. Restate it against the proved law.

### 1.4 `optional` / `choice` / `maybe` — partial or alias

- [ ] 1.4.1 Complete `optional`'s `Rel` characterization: `Rel_optional_some` is
      one direction only; add the `none` case.
- [ ] 1.4.2 Give `maybe` (`:67`, a bare alias for `optional`) a law naming it
      (`Rel_maybe_some` is a one-token proof), so the alias claim is checkable from
      the proof surface. Either that or delete it and stop listing it in the
      README inventory — an alias no theorem names has nothing to reproduce.
- [ ] 1.4.3 Record what `Rel_choice` does and does not give (exists-in-list only).

### 1.5 The under-covered triples: `sepBy`, `takeWhile`

- [ ] 1.5.1 Add `encodeSepBy_of_decode` and `encodeSepBy_ne_none`, mirroring
      `encodeChainl1_of_decode` / `encodeChainl1_ne_none`.
- [ ] 1.5.2 Add the `takeWhile` twins (`encodeTakeWhile_of_decode`,
      `encodeTakeWhile_ne_none`).
- [ ] 1.5.3 If a decode→encode law is not obtainable for either triple, record the
      asymmetry at `Combinators.lean` and in the README rather than presenting the
      triples as "the same shape every other combinator has" — `chainl1`/`chainr1`
      have four laws each; `sepBy`/`takeWhile` have two.

### 1.6 Dead public surface

- [ ] 1.6.1 Resolve `btake` (`Codec/Codec.lean:112`): zero theorems, zero callers,
      one `grep` hit (its own definition) while `bdrop` has 19 lemmas. Either prove
      the law its docstring advertises (`btake m s i = s i` for `i < m`) or delete
      it.
- [ ] 1.6.2 Same for `Suffix.consumed` (`:134`): its docstring says it exists so
      consumers do not recompute the length, and nothing calls it. One-line law or
      delete.

### 1.7 Correct the Combines docstring's "free theorems" claim

- [ ] 1.7.1 Rewrite `Combinators.lean:92-100`. It claims each derived
      combinator's `Rel` characterization is "a definitional consequence … no new
      induction" and that "the full laws (`decode_spec`, `bidir`, `roundtrip`)
      hold unconditionally via `Codec.Sound`". **False for all eight** at a
      variable-`n` `count`: those laws are structural inductions on the `Codec`
      value and cannot close without the step law. State which values are proved,
      which are not, and why the three laws do not transfer.

### 1.8 Make the definition-level gap a build failure

- [ ] 1.8.1 Add a public-`def` enumeration to `Axioms.lean` (alongside
      `publicTheorems`) and a `run_cmd` that fails when a public `def` is mentioned
      by no gated theorem and is not in a `definitionSurfaceAllowlist`.
- [ ] 1.8.2 State in the gate's header that the check is a **mention proxy**, not a
      guarantee of law strength — its property is that no public definition can be
      covered by silence. Do not let it read as soundness.
- [ ] 1.8.3 Run it against the tree and confirm it names the definitions the audit
      found (`btake`, `maybe`, `manyUpTo`, `seqRight`, `seqLeft`, `between`, …).
      That list is the check working, not a regression.
- [ ] 1.8.4 Every remaining allowlist entry carries its reason in place.

### 1.9 Generate the footprint table

- [ ] 1.9.1 Emit the footprint distribution from `scripts/gen-axioms.lean` so the
      header is generated rather than transcribed. Nothing currently checks the
      counts — `partition`/`gateCoverage` compare set membership only — so a stale
      table would be silent. (The audit claimed this table was _wrong_; design D1
      refutes that — it is correct today. This task is anti-drift, not a fix.)
- [ ] 1.9.2 Regenerate and confirm the generated table equals the current
      hand-written one (`197 / 61 / 4 / 30 = 292`). If it differs, the hand-written
      one was stale and that is the finding.

### 1.10 Part 1 gates

- [ ] 1.10.1 `nix develop --command lake build` — zero `sorry`, zero warnings,
      both partition checks green.
- [ ] 1.10.2 `nix develop --command lake build bench` — compiles and links.
- [ ] 1.10.3 `nix develop --command openspec validate --all`.
- [ ] 1.10.4 Commit per task family (basen gate / count+manyUpTo / seq* / the two
      triples / def-check / docstring), individual files only, printing
      `git diff --cached --name-only` before each.

---

## 2. Prose, and the two remaining gate asymmetries

### 2.1 The `RelAligned` claim — a theorem, not a deletion

- [ ] 2.1.1 Land `relUnambiguous_not_implies_relAligned` in `Codec/Sound.lean` with
      the `S` witness from design D4. Measured: `relUnambiguous S` is
      `[propext, Quot.sound]`-only, `¬ RelAligned S` is `[propext]`-only.
- [ ] 2.1.2 Replace `Sound.lean:1119-1129`. The paragraph says "there is no
      relation that is unambiguous and not aligned, and no such witness is worth
      hunting for" — refuted by 2.1.1. State the measured relationship: the
      families are **incomparable**, and `decodeArray_unique` needs `RelAligned`
      **and** `Functional`, which `relUnambiguous` will not supply.
- [ ] 2.1.3 Remove the unsupported `LengthDet → RelAligned` "needs a
      `DecidableEq α`, i.e. a classical axiom" aside, or prove it. It is a claim
      about a proof route the authors tried, presented as a strength fact, and no
      theorem supports either half (`Sound.lean`, `RelAligned` block).
- [ ] 2.1.4 Re-read the whole `RelAligned`/`LengthDet`/`LengthConst` block for
      other prose-only ordering claims, and apply 2.1.2's rule to each.

### 2.2 `../lean-nix-flake-template` — make the gate claim true

- [ ] 2.2.1 Add `moreLeanArgs := #["-DwarningAsError=true"]` to the template's
      `lakefile.lean` `lean_lib`. Measured: `grep -c warningAsError` → template
      `0`, codec `5`, basen `3`; the template's `README.md:50` already claims "a
      build that encounters a `sorry` fails" and `default.nix:101` repeats it.
      Making the claim true beats deleting it: every scaffolded project inherits
      the gate.
- [ ] 2.2.2 Correct `README.md:134`: `require codec … @ "main"` → `@ "master"`.
      Codec's branch is `master`; basen's `lakefile.lean:8-10` documents the point
      explicitly. A forker copying the example gets a fetch failure that reads as
      a broken dependency.
- [ ] 2.2.3 Add a `sorry`-stub prober to the template's own verification and
      record that `lake build` now fails on it (2.2.1's load-bearing check).
- [ ] 2.2.4 Template gates: `nix flake check`, `nix build .#native .#cli`.

### 2.3 `../lean-basen` remaining

- [ ] 2.3.1 `CHANGELOG.md:75` says "Moving to 4.35.0 was declined"; `:42` records
      it as taken. Remove the contradiction — the repo's own `AGENTS.md` names
      exactly this shape as a defect. Keep the true part (the file is inert, and
      deleting it is an owner call).
- [ ] 2.3.2 Correct `Axioms.lean:24-30`: "all 440 public theorems of
      [basen modules]" over-counts by 3 — 437 are basen's, 3 are codec's
      (`roundtrip`/`bidir`/`decode_spec`).
- [ ] 2.3.3 Prove the **general** arity rejection for the five fixed-width bases,
      mirroring `Base32.decodeFullB32_reject_arity` (`n % 8 ≠ 0 → none`) and
      `Base64.decodeFullB64_reject_arity`. Today `rejects_bad_arity`
      (`Base2:693`, `Base4:571`, `Base8:556`, `Base10:524`, `Base16:549`) is an
      `n = 1` probe named like the general law. Rename to a witness name
      regardless, so the name matches the statement.
- [ ] 2.3.4 Restate `Base16.rejects_lowercase` (`:544`). It currently proves
      `decodeFull hexElem hexConsumesByte 1 (fun _ => 0x66) = none`, where the
      governing reason is odd arity — uppercase `'F'` at `n = 1` is **also**
      `none`. Add an even-arity lowercase witness whose only rejection reason is
      case, and rename or fold the `n = 1` one into `rejects_odd_arity`.
- [ ] 2.3.5 `../lean-basen` gates: `lake build`, `lake build bench`,
      `nix build '.#bench'`.

### 2.4 codec prose drift

- [ ] 2.4.1 Delete the `CHANGELOG.md:59-64` `Codec.Buffer` entry. It documents a
      module, its entry points and four named theorems; `#check @Codec.Buffer` →
      unknown constant. The entry was seeded from history in the same commit that
      deleted the tier.
- [ ] 2.4.2 Fix README:380's `Codec/Encode.lean` row: it cites
      `Codec.encodeArray_eq`, which lives in `Packed.lean`, and `Encode.lean` has
      no law about `encode` at all (`encode_rel` is in `Sound.lean`). Cite
      something in the module or say where the encoder's law lives.
- [ ] 2.4.3 README:577-582: "the leak's growth is in the result list" sits inside
      a paragraph introduced as the paper's own cost. The paper says no such
      thing and nothing here measured it. Mark it as the project's unmeasured
      inference, or measure it.
- [ ] 2.4.4 README:222: mark the elision between the two quoted paper fragments.
- [ ] 2.4.5 Update README:343 ("the same relation-then-two-directions shape every
      other combinator has") to match what 1.5 established.
- [ ] 2.4.6 Correct `Combinators.lean:171-183`'s "zero-or-more separation is
      `optional (sepBy p sep)`" — no such `Codec` value exists, and
      `optional (sepBy …)` would be `Option (List α)`, not zero-or-more lists.
- [ ] 2.4.7 Re-read `AGENTS.md` and `README.md` for stale counts and job numbers
      (`AGENTS.md:44`'s "418/418", `:176`'s "13 jobs" both predate the current
      tree) and restamp or drop them.

### 2.5 Part 2 gates

- [ ] 2.5.1 codec: `lake build`, `lake build bench`, `openspec validate --all`,
      `nix flake check` (detached with `nohup`, never foregrounded).
- [ ] 2.5.2 `../lean-basen`: `lake build`, `lake build bench`,
      `nix build '.#bench'`.
- [ ] 2.5.3 `../lean-nix-flake-template`: `nix flake check`,
      `nix build .#native .#cli`.
- [ ] 2.5.4 Commit per task family, individual files only.

---

## Archive ordering — RESOLVED 2026-11-05

`codec-audit-round-two` **has been archived** as
`openspec/changes/archive/2026-11-05-codec-audit-round-two/`, with its three spec
deltas synced into `openspec/specs/` first and verified scenario-by-scenario
(no live scenario was dropped: `codec/axiom-gate` 3 -> 6, `codec/review-remediation`
4 -> 5, `codec/congruence-honesty` created from ADDED-only).

**What this means for this change's archive:** this delta was authored against the
_pre_-sync text, so it will replace `codec/axiom-gate`'s and
`codec/review-remediation`'s requirements a second time. Round two's scenario sets
are now the baseline. Before archiving this change:

1. ~~Re-run the scenario diff live-vs-delta.~~ **Verified 2026-11-05, now that
   round two is synced:** every replacement is a strict superset —
   `codec/axiom-gate` 6 -> 6 (identical set), `codec/review-remediation`
   "Documentation SHALL distinguish quoted from derived claims" 2 -> 4,
   `basen` "conformance laws are gated" 1 -> 3 and "A decoder rejects malformed
   input" 5 -> 7, `template` "skeleton builds … zero sorry" 2 -> 3 and
   "dependency-injection convention" 1 -> 2. **Nothing is dropped.** Re-run the
   diff at archive time anyway; it is cheap and this repo has been bitten.
2. `openspec validate --all` after the archive and confirm it stays green.
3. Check `codec/law-coverage` is created with its `## Purpose` carried across (it is
   the only ADDED-only capability here).
