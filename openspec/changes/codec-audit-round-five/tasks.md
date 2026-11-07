# Tasks — `codec-audit-round-five`

**Issue ledger: 38 numbered findings** (`R6-01` … `R6-38`), from the round-six
audit. Reports: `/tmp/r6/{A,B,C}.md`; merged ledger `/tmp/r6-SYNTHESIS.md`.

**Numbering, which is off by one from the change name — this is not a typo.**
`codec-audit-round-five` is the **fifth audit _change_**; its findings come from the
**sixth review round** (rounds one to four produced `codec-audit-remediation`,
`-round-two`, `-round-three`, `-round-four`). Hence the change is `round-five` and the
ids are `R6-nn`. When this archives it will be `<date>-codec-audit-round-five`, and the
next review's findings will be `R7-nn` in a change called `round-six`.

**Nothing here requires `/tmp`.** The reports are cited for **provenance only**. Every
finding a task fixes is stated in full below, and the one proof body this change needs
is inlined in **Appendix A**, re-verified against the tree on 2026-11-07. A `/tmp` path
is "where this came from", never "what you must open".

**Verification status.** Every MUST and the highest-value SHOULDs were independently
re-derived by the main agent before being written here (marked ✔). The review also
**refuted 26** suspected defects; those are listed in §9 so they are not re-derived, and
they are not tasks.

**Severity key.** MUST = a false claim, a broken gate, a stale dependency. 7 findings.
SHOULD = an over-claim that steers a reader wrong, or an advertised law that is absent.
15 findings. NITPICK = a wording error, a dead lemma, a mis-citation. 16 findings.

## Build state during implementation — read this before task 1.1

**`lake build` will be RED from §1.1 until §7.1, and that is expected.** The def-side
arm added in §1 will fire on the current tree until the classifications in §2 land, and
the theorem counts move only at regeneration. The policy is the same as round four:

```bash
nix develop --command lake env lean Codec/Sound.lean   # per-module type check
nix develop --command lake build                       # run at §1.1 to see WHAT it names
```

Run `lake build` **once** at §1.1 because its failure message _is_ the work list for §2.
After that, use per-module checks until §7.1's regeneration, which is the single stated
endpoint. Do **not** regenerate after every individual change — the generator rewrites
the whole file and the header constants must be recomputed each time. §8 is where green
is required.

`openspec` counts every `- [ ]` in this file, so §9 (records, no action) carries no
checkboxes, deliberately.

## Issue ledger (the index — every id is fixed by a task below)

| id    | sev     | repo     | location                                | one-line                                                                                  |
| ----- | ------- | -------- | --------------------------------------- | ----------------------------------------------------------------------------------------- |
| R6-01 | MUST    | codec    | `Axioms.lean` `isDerivedDefName`        | drops `Iso.prod` — the paper's `×` — out of the universe; gate green ✔                    |
| R6-02 | MUST    | codec    | `Axioms.lean` `gatedNames` vs allowlist | three `Prop`-field projections gated as laws, their three twins allowlisted as not-laws ✔ |
| R6-03 | MUST    | codec    | `Axioms.lean` defs table                | "axiom-free is the signature of a restatement" false for one of its own two examples ✔    |
| R6-04 | MUST    | codec    | `README.md` `[S1]`                      | "exactly two other `Iso`-valued definitions" — there are four ✔                           |
| R6-05 | MUST    | codec    | `README.md` `[S3]`                      | "every `Codec`-valued definition is one of these fifteen" — four omitted ✔                |
| R6-06 | MUST    | codec    | `Codec/Sound.lean`                      | "it is the length index, not `LengthDet`" — false as a general claim ✔                    |
| R6-07 | MUST    | codec    | `Axioms.lean` allowlist                 | "correctness is the `law` field" is vacuous for the _partial_ `subset`/`element`          |
| R6-08 | SHOULD  | codec    | `README.md` perf                        | "~25 ns/step (52.4 − 27.4)" — cross-run subtraction; `52.4` orphaned ✔                    |
| R6-09 | SHOULD  | basen    | `flake.lock`                            | pin validates `codec` `a12ac65`; sibling tree is `d86132b` — 10 commits ✔                 |
| R6-10 | SHOULD  | basen    | `Bench.lean:403`                        | "the only `native_decide` in the ecosystem" — there are 13 ✔                              |
| R6-11 | SHOULD  | codec    | `Axioms.lean` allowlist                 | `candsAt`/`candsRoot`/`retypeCands` have zero mentioning constants                        |
| R6-12 | SHOULD  | codec    | `scripts/gen-axioms.lean`               | "cannot silently disagree" covers theorems only; def counts underived                     |
| R6-13 | SHOULD  | codec    | `Codec/Sound.lean` ×3                   | "needs … **beyond unambiguity**" — no such hypothesis exists                              |
| R6-14 | SHOULD  | codec    | `Codec/Sound.lean` `LengthConst`        | mechanism stated 3×, side condition `c ≠ 0` never named                                   |
| R6-15 | SHOULD  | codec    | `README [S3]`                           | "`relFunctional` conditional in every case" — possibly derivable; **open**                |
| R6-16 | SHOULD  | codec    | `README [D5]`                           | the elision note is itself a spliced quote                                                |
| R6-17 | SHOULD  | codec    | `README [D4]`                           | "not injective" then "that is not the reason"                                             |
| R6-18 | SHOULD  | codec    | `README [S3]`                           | "only at `Codec.byte`" — `Unambiguous` has two composed suppliers                         |
| R6-19 | SHOULD  | codec    | `Axioms.lean` `run_cmd`s                | four failure branches never exercised in this tree                                        |
| R6-20 | SHOULD  | basen    | `README.md:90`                          | converse law rendered as a pseudo-signature                                               |
| R6-21 | SHOULD  | basen    | `README.md:100`                         | "alphabet is ASCII (48-122)" — base64 uses 43 and 47 ✔                                    |
| R6-22 | NITPICK | codec    | `README [D1]`                           | mis-quotes both paper declarations                                                        |
| R6-23 | NITPICK | codec    | `README [D2]`                           | "exactly the paper's `Rel`" vs `[D3]`'s Multiplicity note                                 |
| R6-24 | NITPICK | codec    | `README [D7]`                           | collapses `measure` and `MeasureDecreases`                                                |
| R6-25 | NITPICK | codec    | `README`                                | quotes `AGENTS.md` saying something it no longer says ✔                                   |
| R6-26 | NITPICK | codec    | `README` table caption                  | "512 steps per burst" wrong for `idealCursor` (4096)                                      |
| R6-27 | NITPICK | codec    | `Axioms.lean`                           | historical footprint quadruple with no commit sha                                         |
| R6-28 | NITPICK | codec    | `Axioms.lean` `gatedNames`              | `Codec.brecOn.eq` gated as an axiom-free law                                              |
| R6-29 | NITPICK | codec    | `Codec/Sound.lean`                      | `relFunctional` has no docstring, no link to `Functional`                                 |
| R6-30 | NITPICK | codec    | `README [S1]`                           | five listed isos have zero referencing constants                                          |
| R6-31 | NITPICK | codec    | `Codec/Iso.lean`                        | `Iso.element`'s retention reason is false                                                 |
| R6-32 | NITPICK | basen    | `Base10.lean:13`                        | phantom `decode (encode bs)` shorthand                                                    |
| R6-33 | NITPICK | basen    | `default.nix:17`                        | calls all bench checks `rfl`; 13 are `native_decide`                                      |
| R6-34 | NITPICK | basen    | `CHANGELOG.md`                          | names a five-bumps-stale pin                                                              |
| R6-35 | NITPICK | template | `lakefile.lean`                         | cites `codec-audit-round-three §2.2.1`, unresolvable from a fork                          |
| R6-36 | NITPICK | template | root                                    | ships no `AGENTS.md`                                                                      |
| R6-37 | NITPICK | codec    | `Axioms.lean` `isDerivedDefName`        | three dead suffix entries (`rec`, `mk`, `sizeOf`)                                         |
| R6-38 | NITPICK | codec    | `Axioms.lean` allowlist                 | `Iso.element`/`subset` reasons duplicated from the group's                                |

---

## 1. The gate's missing audit arm (R6-01, R6-37)

The highest-priority section: it is the **mechanism** behind R6-01/02/03, not three
separate prose fixes.

- [x] 1.1 Add the def-side audit arm to `Axioms.lean`, mirroring the theorem-side
      `partition`. **R6-01.** ✔Verified: `publicDefs = 141`, `Iso.prod in publicDefs:
false`, `Iso.prod in allowlist: false`, `Iso.commute in publicDefs: true`.

      Two arms, both as `run_cmd`s in the same style as the existing coverage check:

      1. **Every dropped name needs a reason.** For each public `def` in the gated
         namespaces that `isDerivedDefName` removes, require membership in a new
         `derivedDefAllowlist` (name + reason, in place). A name in neither the
         universe nor that list is a build failure naming it.
      2. **The pattern list is verified.** An entry in `isDerivedDefName` that matches
         **no** declaration in the environment is a failure naming the entry, and so is
         an entry whose matched set contains a name that also appears in a
         `definitionSurfaceAllowlist` reason mentioning authorial API.

      Run `nix develop --command lake build` once here: its failure output **is** the
      work list for §2. Do not try to make it green in this task.

- [x] 1.2 Delete the three dead suffix entries. **R6-37.** `rec`, `mk`, `sizeOf` match
      no `def` in `Codec`/`Iso` (✔measured). Removing them is safe once 1.1's second arm
      exists, because it will re-add such an entry as an error rather than a default.
- [x] 1.3 Remove `"prod"` from the list so `Iso.prod` re-enters the universe. It will
      then fail as unnamed — that is §2.1's task, not this one.

## 2. Classifying what the gate names (R6-02, R6-07, R6-11, R6-38)

- [x] 2.1 Give **`Iso.prod` a law** rather than an allowlist reason. **R6-01/§D2.** It is
      the paper's `×` and is in `[S1]`'s unconditional list, so a theorem naming it is
      the honest resolution. State the law (`Rel (prod i j) (x, y) s` decomposed over a
      split) and keep it `[propext, Quot.sound]`-only; if it proves awkward, the
      fallback is a `definitionSurfaceAllowlist` entry — but then `[S1]`'s list must not
      be described as complete.
- [x] 2.2 Move `Iso.law`, `Codec.Normal.fixed`, `Codec.Normalizer.idem` into
      `generatedAuxAllowlist`'s existing `Prop`-valued-structure-field group, whose
      reason already covers them, and move the counts. **R6-02**, design §D3.
      ✔Measured: all three are `fun … => self.1`/`self.2` and report no axioms.
- [x] 2.3 Add the **domain laws** for the two partial isos: `(subset p).apply x = some x
↔ p x` and `(element x).unapply b = some () ↔ b = x`. **R6-07**, design §D5.
      If either is awkward, fallback is a fourth allowlist group with the "partial iso"
      reason — design §D5 records it so the decision does not return.
- [x] 2.4 Resolve the three zero-reference allowlist entries. **R6-11.** `candsRoot` and
      `retypeCands` are unreferenced by any constant and `candsAt` is referenced only by
      `retypeCands` — a closed dead island. **Delete them** if `Codec/Decode.lean` no
      longer needs them (check first), otherwise change the reason to "unreferenced —
      pending deletion", since a "Type-level alias" reason does not say "dead".
- [x] 2.5 De-duplicate `Iso.element`/`Iso.subset`'s allowlist reasons. **R6-38.** They
      currently repeat the group's reason verbatim; if 2.3 and 2.2 land they leave the
      list entirely, so verify rather than assume.
      **Verified, not assumed:** both left. The definition-coverage check itself
      reported them under "definitions that HAVE a gated law but are also
      allowlisted", because their domain laws mention the constants — so the entries
      were removed and the group comment now records _why_ the two are absent.

## 3. The mathematics sentence (R6-06)

- [x] 3.1 Land the counterexample in `Codec/Sound.lean`. **R6-06.** ✔Proved and in
      **Appendix A.1** (`[propext]` and `[propext, Quot.sound]`-only). The witness
      `Rab` is `LengthDet`, productive, and admits two distinct full-consumption lists
      of **one** string at **different list lengths** — so "the list-length index, not
      `LengthDet`" is false as a general claim.
- [x] 3.2 Rewrite the section sentence. Replace "it is the **length index**, not
      `LengthDet`" with: the list-length index handles list length, while per-step
      agreement _inside_ the induction is `LengthDet`'s job; `huniq_not_derivable`'s
      witness fails both, so neither premise is decorative. The **next** paragraph
      already says this correctly — do not duplicate it, make this sentence agree.
- [x] 3.3 Correct the three "needs **beyond unambiguity**" sites. **R6-13.**
      `relRepeat_unique_same_length` takes no unambiguity hypothesis at all, and
      `RelAligned → relUnambiguous` is proved in the same file, so `RelAligned`
      _contains_ unambiguity and there is no set "beyond" it. Correct phrasing: "in
      place of unambiguity — one subsumes it, the other supplies per-step length
      agreement".
- [x] 3.4 Name the side condition `c ≠ 0` wherever `LengthConst`'s mechanism is stated.
      **R6-14.** Stated three times in the section header, never with `hc0`; at `c = 0`
      a list of any number of steps consumes zero bytes and the lemma is false.
- [x] 3.5 Add `relFunctional`'s docstring and the bridge theorem. **R6-29.** State
      `Functional d ↔ relFunctional (Rel d)` so the two spellings cannot drift silently.
      This is a NITPICK with a real payoff: both are used for the same obligation.

## 4. `basen` (R6-09, R6-10, R6-20, R6-21, R6-32, R6-33, R6-34)

- [x] 4.1 Decide the pin. **R6-09.** ✔Verified: pinned `a12ac65`, sibling tree
      `d86132b`, 10 commits, 7 library files, +370/−70. Round six **proved the gap
      benign** by rebuilding against HEAD in `/tmp` (25 jobs green). **Take the bump**
      (`nix flake update codec` — targeted, never all inputs; then `lake update codec`)
      and re-run `lake build`, `lake build bench`. Record the actual output.

      **DONE ahead of this change, in the session that authored it** (`2751537`), because
      the pin was the one item that could be closed without touching a spec delta and it
      blocked nothing. Pinned `a12ac65` → **`93acd59`**, which is `codec`'s
      `origin/master` exactly — so the validated revision and the sibling tree now agree
      and R6-09 is closed rather than merely decided. **Every gate was run on the new
      pin, not predicted:**
      `lake build` → `486 = 440 + 46` theorems, `137 = 122 + 15` defs, four gate lines;
      `lake build bench` → 45 jobs; `nix build '.#bench'` → builds, `installPhase` runs
      the executable, exit 0. The update was **targeted** (`nix flake update codec`):
      `nixpkgs` (`1d06008`), `flake-utils`, `treefmt-nix` and `systems` were already
      identical across all three `lean-*` repos, so nothing else moved.
      **What remains for this task: nothing.** The prose arm the spec delta adds
      (`basen` must record the validated revision or the lag) is still 4.2–4.3's
      neighbour work and is not satisfied by the bump alone — a future drift would again
      be invisible, which is what the delta is for.

- [x] 4.2 Correct the `native_decide` count claim. **R6-10.** `Bench.lean:403` says
      "these three stay as the only `native_decide` in the ecosystem"; there are **13**
      (✔), and the second block's own header already says "`native_decide` **again**".
      Delete the sentence or state 13. Per the new `basen` spec delta, the count must be
      **asserted** if it is stated — add the `run_cmd` arm in 4.3.
      **Done.** **Measured: 12, not 13.** `grep -nE '^\s*native_decide\s*$' Bench.lean | wc -l` → 12 (18 identifier occurrences, 6 of them prose). Sentence rewritten to name twelve and to point at the new assertion.
- [x] 4.3 Add the stated-count assertion to `basen/Axioms.lean` (the prose-counts arm's
      sibling). **R6-10**, `basen` spec delta. Count `native_decide` occurrences in
      `Bench.lean` and assert it equals the number the prose states.
      **Done.** `Axioms.lean` gained a fifth `run_cmd` (`nativeDecideCount`) reading `Bench.lean` as text (it cannot be imported) and failing when the prose count and the tactic-line count disagree. Green: `native_decide stated count verified (12 uses in Bench.lean, all bench-lane, none in the gate)`.
- [x] 4.4 Fix the two pseudo-signatures. **R6-20/R6-32.** `README.md:90` renders the
      converse law as `decode c = some b → encode b = c`, which matches no declaration
      (✔`BaseN.Base16.decode` does not exist) — and the same README forbids that
      shorthand 50 lines earlier. `Base10.lean:13` repeats it. State both in the real
      `decodeFull`/`Σ n, Bytes n` form.
      **Done.** Both now quoted at the real types (`decodeFull : … → Bytes n → Option (List UInt8)`, `encode… : List UInt8 → Option (Σ n, Bytes n)`) with the two actual declarations named.
- [x] 4.5 Fix the alphabet range. **R6-21.** `README.md:100` says "(48-122)"; base64
      uses `+`=43 and `/`=47, so the union is 43-122 (✔). The `< 256` conclusion is
      true, so nothing follows for proofs — fix the number the reader would use.
      **Done.** Now "43-122", with `+`=43 and `/`=47 named.
- [x] 4.6 Fix the bench-lane characterisation and the stale changelog pin.
      **R6-33/R6-34.** `default.nix:17` calls the lane's checks `example … := rfl`;
      13 are `native_decide` and 19 are `rfl` of ~90. `CHANGELOG`'s newest entry names
      `codec → 3277d48`; add the current pin or (preferred) state it once in `AGENTS.md`.
      **Done.** `default.nix` now says "mostly `example … := rfl` … but not all: 12 `by native_decide`". `basen/AGENTS.md` gained "The validated `codec` revision — read `flake.lock`, never a number here", with the command that prints it; `CHANGELOG`'s rev is marked historical.

## 5. Documentation claims: completeness, derivation, signature (R6-03, R6-04, R6-05, R6-08, R6-16, R6-17, R6-18)

- [x] 5.1 Delete the "axiom-free ⇒ restatement" diagnostic in `Axioms.lean`.
      **R6-03**, design §D4. ✔`decodeWholeOneBytes_eq` is `[propext, Quot.sound]`, not
      axiom-free, so it fails on its own example; it also over-flags the three Layer-2
      `*_spec`s. Name identities by `#print`ing their bodies instead.
      **Done.** Deleted and replaced with the measured facts (`decodeWholeOneBytes_eq` is `[propext, Quot.sound]`; the three Layer-2 `*_spec`s over-flagged; name identities by `#print`ing the body).
- [x] 5.2 Restate `[S1]`'s completeness claim. **R6-04.** ✔17 `Iso`-valued defs, not 15. `counterIso`/`counterIsoR` are the `MeasureDecreases` satisfiability
      witnesses and hold their law **unconditionally**, so the "only on the
      terminal-seed domain" qualifier is wrong too. Also replace the method claim —
      `grep '^def'` misses multi-line signatures — with the environment walk.
      **Done.** Rewritten: **19** public `Iso`-valued defs by environment walk (13 listed + `foldl`/`foldr`/`counterIso`/`counterIsoR`); the four are split by position (`counterIso`/`counterIsoR` hold their law **unconditionally**, so the old "both hold only on the terminal-seed domain" was false); the `grep '^def'` method claim is replaced by the walk.
- [x] 5.3 Restate `[S3]`'s inventory claim. **R6-05.** ✔`uniqSeqBt`/`Bo`/`D2`/`Whole`
      are four public `Codec` values in no row. Say "the fifteen a **porter must
      reproduce** … plus four values that exist only as counterexample witnesses", and
      reuse `Axioms.lean`'s existing characterisation rather than asserting
      exhaustiveness.
      **Done.** Now "the fifteen a **porter must reproduce** (7 constructors + 8 bounded defs)", plus the four `uniqSeq*` counterexample-witness values stated as environment-only.
- [x] 5.4 Re-derive the second-candidate cost. **R6-08**, design §D7. ✔The adjacent
      table gives 26.4 (run 1) / 23.6 (run 2); `52.4` appears nowhere else in the
      document. Present as a range with the run number, and delete the orphan. **Do not
      re-run the bench** — this is a documentation inconsistency between committed
      figures.
      **Done.** Now "~24-26 ns/step" from the adjacent table (`54.9 − 28.5 = 26.4` run 1, `51.1 − 27.5 = 23.6` run 2), with the orphan `52.4` deleted and the cross-table/cross-run defect named. `~21×` → `~20×`. No bench was re-run.
- [x] 5.5 Rewrite `[D5]`'s elision note. **R6-16.** The note that marks the elision is
      itself assembled across the text it says is elided; the material strictly between
      the two fragments is three words ("This means that"). Quote the elided span
      exactly and no more.
      **Done.** The elided span is now quoted exactly ("This means that", three words) and the note no longer carries an ellipsis of its own.
- [x] 5.6 Fix `[D4]`'s injectivity contradiction. **R6-17.** The anchor says `ignore`
      fails "because its `apply` is **not injective**", then three sentences later says
      that is _not_ the reason. The sibling "why" section has it right: the obstruction
      is that `apply` is **constant** and `law` is an `↔` over every `a`.
      **Done.** The obstruction is now stated once, as **constancy** of `apply` plus the law being an `↔` over every `a`; non-injectivity is named as a consequence and explicitly not the reason.
- [x] 5.7 Qualify "only at `Codec.byte`". **R6-18.** `Unambiguous` has two composed
      suppliers (`uniqSeqBo_unambiguous`, `uniqSeqD2_unambiguous`) besides
      `unambiguous_byte`. Say "each family has a supplier at `Codec.byte`" — which is
      true — rather than "only at".
      **Done.** Now "each family has a supplier at `Codec.byte`", with the two composed `Unambiguous` suppliers (`uniqSeqBo_unambiguous`, `uniqSeqD2_unambiguous`) named.

## 6. Nitpick sweep (R6-19, R6-22 … R6-31, R6-35, R6-36)

Each is one clause. Do them as one pass.

- [x] 6.1 `[D1]`: quote both paper declarations correctly — `newtype Parser α = Parser
(String → [(α, String)])` and `data Rel α = Rel [(α, String)]`. **R6-22.** `[D2]`
      quotes them right 20 lines later; make them agree.
      **Done.** Both quoted in full (`newtype Parser α = Parser (String → [(α, String)])`, `data Rel α = Rel [(α, String)]`), agreeing with `[D2]`.
- [x] 6.2 `[D2]`: add "**as a graph** (not as a multiset — see the Multiplicity note
      under `[D3]`)". **R6-23.**
      **Done.** Added, with a pointer to the Multiplicity note under `[D3]`.
- [x] 6.3 `[D7]`: `MeasureDecreases` is parameterised _by_ the measure and its only
      field is the proof; the same anchor's later list already gets this right. **R6-24.**
      **Done.** Now stated at its real type, `MeasureDecreases (measure : α → Nat) (i : Iso (α × β) α)` with `dec` as the only field.
- [x] 6.4 Remove the stale quotation of `AGENTS.md`. **R6-25.** ✔`README` quotes "which
      this repo does not yet measure"; `AGENTS.md` now says "This repo now measures one".
      **Done.** Reframed as what `AGENTS.md` _used to_ say, with the current text quoted back.
- [x] 6.5 Fix the "512 steps per burst" caption. **R6-26.** `idealCursor` runs 4096
      steps, `decodeFullArray` 512; the per-step figures are each divided by their own
      count, so this is a caption error — and a reader applying 512 to the floor row
      concludes it is 8× worse than it is.
      **Done.** Now says `idealCursor` runs **4096** and the others **512**, with the 8× consequence named. The second table's caption (`n/8` = 512, correct for every row) was made explicit.
- [x] 6.6 Cite the commit beside the historical footprint quadruple. **R6-27.**
      **Done.** `9db99b8` cited at both sites, with "quote the gate, never a number written in a file" added.
- [x] 6.7 Add `"eq"` to `isGeneratedAux` after confirming `Codec.brecOn.eq` is the only
      authorial theorem ending in `eq`. **R6-28.**
      **Done.** ✔Confirmed by environment walk: `Codec.brecOn.eq` is the only public theorem ending in `eq`. Added to both `isGeneratedAux` and the generator's mirror; the name moved to `generatedAuxAllowlist`. **Side effect worth recording:** moving it out of the gated set removed the only mention of `Codec.brecOn.go`, which then surfaced as an un-named public def — and its old pattern `"brecOn.go"` had never matched anything (a last name component is `go`), so that was a fourth dead entry. Fixed by adding a correct `"go"` pattern.
- [x] 6.8 Note that five of `[S1]`'s thirteen listed isos have zero referencing
      constants — expected under `[S3]`, but unstated. **R6-30.**
      **Done.** **Measured: 3, not 5** — `Iso.id`, `Iso.ofTotal`, `Iso.associate` have zero referencing constants (`.eq_1` unfoldings ignored). The five was 3 plus `element`/`subset`, which §2.3's domain laws now reference; the note says so rather than repeating the stale five.
- [x] 6.9 Fix `Iso.element`'s retention reason. **R6-31.** ✔`[D8]` names only the
      paper's constructors, never `Iso.element`; re-point at `[S1]`'s parenthetical or
      delete the sentence.
      **Done.** **Refuted on inspection** — `README [D8]`'s opening sentence names `Iso.element` and `Iso.subset` verbatim, so the reason holds. The docstring now cites both anchors by name and records the refutation.
- [x] 6.10 Record that the four `run_cmd` failure branches are unexercised, with the
      deliberately-red probe a maintainer can run. **R6-19.** Stated narrowly: absence
      of evidence, not proof the checks are dead.
      **Done.** Recorded in `derivedDefPatternAudit`'s docstring, narrowly: all four `run_cmd` arms are on their passing path in this tree, with the deliberate one-line edit that exercises each.
- [x] 6.11 Template: replace the `codec-audit-round-three §2.2.1` citation with a
      self-contained sentence. **R6-35.** A fork cannot resolve another repo's change
      section number.
      **Done.** `lakefile.lean` now says "**It was absent before 2026-11-06**", keeping the ledger's section number only as a parenthetical provenance note a fork need not resolve.
- [x] 6.12 Template: ship a short `AGENTS.md`. **R6-36.** The ecosystem rules —
      commit granularity, `flake.lock` vs `lake-manifest.json`, the axiom discipline,
      the two-layer trust posture. `basen` and `codec` both have one; a fork starts
      without.
      **Done.** Written: non-negotiables (zero `sorry`, axiom discipline, per-file commits, lock-vs-manifest), the two-layer trust posture and the "no axiom is never no trust" rule, what each verification command actually proves, cross-repo pin/bad-import guidance, and the documentation-discipline lessons.

## 7. Settle R6-15, then regenerate

- [x] 7.1 **Attempt the `relFunctional` derivability proof.** **R6-15**, design §D6.
      Claim under test: `relFunctional` is derivable for `takeWhile`/`sepBy` (both are
      `relRepeat`-shaped over `ConsumesByte` steps, so each value list's string length
      is pinned by the list's own length), leaving only `chainl1`/`chainr1` as genuine
      caller obligations. **The reviewer flagged this as inferred, not proved, after
      five failed attempts.**

      Two outcomes, both of which end in a tick: (a) it closes → land the theorem, and
      replace `[S3]`'s "conditional in **every** case" with a two-row table
      (obligation vs derivable); (b) it does not → record the refutation in this
      ledger's §9 and leave the prose alone. **Do not change the prose on an unproved
      inference** — that is the defect class this change exists to fix.

      **OUTCOME (a), partial — and the partiality is the finding.** Landed
      `Codec.relRepeat_functional_of_step`, `Codec.satisfy_sigmaFunctional`,
      `Codec.relTakeWhile_functional`, `Codec.relSepBy_functional`
      (`Codec/Combinators.lean`), all `[propext, Quot.sound]`-only by `#print axioms`.
      Measured:
      * `takeWhile` — `relFunctional` is **unconditionally derivable**: a `satisfy p`
        step's bytes are determined by its value, so `relRepeat_functional_of_step`
        applies with no hypothesis on `p`.
      * `sepBy` — derivable **from `relFunctional (Rel p)`**, not unconditionally: its
        tail is `takeWhile`-shaped, but its head is an arbitrary `Codec α`. The
        reviewer's inference was right about the tail and silent about the head.
      * `chainl1`/`chainr1` — not attempted; the fold can send two distinct
        `(seed, ops)` pairs to the same value, so the obligation is real.

      Prose updated in `README [S3]` to a three-row table (derivable / derivable given
      `p` / genuine obligation) rather than the old "conditional in **every** case".

- [x] 7.2 Regenerate `Axioms.lean` once (`scripts/gen-axioms.lean`) and move the header
      tables and the six `expected*` constants together. **Do not predict the delta —
      the run prints it.** The generator also rewrites the footprint distribution
      between its `BEGIN/END GENERATED` markers, and the new def-side counts from §2
      must be asserted there (design §D1). Re-run until green.
      **Done.** Regenerated **once** (`rewrote 348 gates and the distribution table`), then the header table and all six `expected*` constants moved together. Four gate lines became **six**: the two new def-side arms print too. Final `lake build` output is in §8.1.
- [x] 7.3 Scope `gen-axioms.lean`'s "the two cannot silently disagree". **R6-12.** It
      covers the theorem half only; the def counts (141/112/29 → new values) have no
      derivation path and are asserted by hand. Either add a def-side generator step or
      say so explicitly.
      **Done.** Header now says the mirror covers the **theorem half only**; the def counts have no generator step and are asserted by hand in `Axioms.lean`'s `headerNumbers`.

## 8. Gates (run all three repos; they are different flakes)

**Measured output of the whole section, 2026-11-07.** Every line below is pasted from
the run, not predicted.

`codec` — `lake build` prints **six** gate lines, all green, zero warnings:

```
axiom gate: 348 public theorems covered (0 explicit exclusion(s))
axiom gate: 425 public theorems partitioned, 348 gated and 77 allowlisted
axiom gate: 140 public definitions covered, 115 mentioned and 25 allowlisted (mention proxy)
axiom gate: 54 definitions dropped by the name classifier, all reason-recorded
axiom gate: 12 def-name patterns, each matching a recorded non-surface declaration
axiom gate: header numbers verified (425 = 348 + 77; defs 140 = 115 + 25)
```

`lake build bench` green (28 jobs). `openspec validate --all` **11/11**. `nix fmt`
then `nix flake check` green: `checks.{lean,openspec,formatting}` all ✅.

`basen` — `lake build` green (25 jobs) with **five** gate lines, including the new
`native_decide stated count verified (12 uses in Bench.lean, all bench-lane, none in
the gate)`; `lake build bench` green (45 jobs); `nix build '.#bench'` exit 0 (its
`installPhase` runs the executable).

`template` — `nix flake check` green (`checks.{formatting,lean}` ✅, template
validity ✅); `nix build .#native .#cli` exit 0.

- [x] 8.1 `codec`: `lake build` (zero `sorry`, four gate lines, counts in lockstep),
      `lake build bench`, `openspec validate --all`, `nix flake check` (detached with
      `nohup`, never foregrounded — and **`nix fmt` first**).
- [x] 8.2 `basen`: `lake build`, `lake build bench`, `nix build '.#bench'` (its
      `installPhase` **runs** the executable).
- [x] 8.3 `template`: `nix flake check`, `nix build .#native .#cli`.
- [x] 8.4 Commit per task family, individual files only, printing
      `git diff --cached --name-only` before each. The pre-commit hook runs `nix fmt`
      and rejects a reformatted staged file; re-add and commit again.
      **Done.** Eight `codec` commits (`Codec/Iso.lean`, `Codec/Sound.lean`,
      `Codec/Combinators.lean`, `Codec/Decode.lean`, `Axioms.lean`,
      `scripts/gen-axioms.lean`, `README.md`, `tasks.md`), two `basen` commits
      (`Bench.lean`+`Axioms.lean`, then `README.md`+`Base10.lean`+`default.nix`+
      `AGENTS.md`) and two `template` commits (`lakefile.lean`, `AGENTS.md`). Each
      printed `git diff --cached --name-only` first; the basen and template hooks
      reformatted and rejected once each, and the re-stage committed normally.
- [x] 8.5 Verify every new law's footprint by hand:
      `printf 'import Codec\n#print axioms Codec.<n>\n' > /tmp/c.lean` →
      expect `[propext, Quot.sound]` or cleaner. `Classical.choice` is a defect.

---

## 9. Recorded, deliberately NOT fixed here

**These are NOT tasks and carry no checkboxes, deliberately** — `openspec` counts every
`- [ ]`, so a "no action" box makes 100% unreachable.

- **The 26 refuted findings.** Do not re-derive them; each has evidence in
  `/tmp/r6/{A,B,C}.md`. Notably: base10 **is** fixed-width and **does** roundtrip
  unconditionally (the variable-width trap does not exist here); the `_char` theorems
  **do not** smuggle their own hypothesis; `Iso.law` **is** a genuinely required field;
  `[D4]`'s round-four repair **is** real; both bench lanes **are** load-bearing;
  `relRepeat_cons_eq`'s "neither hypothesis can be dropped" **is** true; the gate's 337
  `#guard_msgs` footprints **are** in lockstep with the environment.
- **Deriving the classifier from the environment instead of a string list.** Recorded as
  design §Open-Questions; possible (`recOn`/`casesOn` are recoverable from an inductive's
  info) and would remove `isDerivedDefName` entirely, but larger than this change.
- **`basen`'s general arity rejection** for the five fixed-width bases — still needs a
  `decodeFull`-length lemma. Unchanged, still open.
- **`[D4]`'s length-changing carrier** — still not built; needs an owner decision.
- **`basen`'s 13 `native_decide` bench uses** — sanctioned, bench-only, out of the gate.
  The count grew from 3 and §4.2/4.3 put it on the record. Converting them needs a
  `b32TailApply_b32MZTA_chars`-shaped lemma that does not exist.

---

## Appendix A — the proofs, inlined (do not depend on `/tmp`)

### A.1 — §3.1 (`Codec/Sound.lean`) — `[propext]` / `[propext, Quot.sound]`

Verified 2026-11-07 against the current tree. Landing means moving these inside
`Codec/Sound.lean`'s existing `namespace Codec` and dropping the `#print axioms` lines
(`scripts/gen-axioms.lean` generates the gated equivalents).

```lean
/-- length-determinate AND productive, yet two distinct full-consumption lists
    of the same string, differing only in list length. -/
def Rab : Bool → {m : Nat} → Bytes m → Prop
  | true,  m, _ => m = 2
  | false, m, _ => m = 1

theorem Rab_lengthDet : LengthDet Rab := by
  intro a m₁ m₂ t₁ t₂ h₁ h₂
  cases a <;> simp_all [Rab]

theorem Rab_productive : ∀ a {m : Nat} (t : Bytes m), Rab a t → m ≠ 0 := by
  intro a m t h
  cases a <;> simp_all [Rab]

theorem four : relRepeat Rab [false,false,false,false] 4 (fun _ => 0) := by
  refine ⟨1, by omega, (fun _ => 0), (fun _ => 0), by ext i; simp [splice, concat], rfl, ?_⟩
  refine ⟨1, by omega, (fun _ => 0), (fun _ => 0), by ext i; simp [splice, concat], rfl, ?_⟩
  refine ⟨1, by omega, (fun _ => 0), (fun _ => 0), by ext i; simp [splice, concat], rfl, ?_⟩
  refine ⟨1, by omega, (fun _ => 0), (fun _ => 0), by ext i; simp [splice, concat], rfl, ?_⟩
  exact (relRepeat_nil _ _).2 (by omega)

theorem two : relRepeat Rab [true,true] 4 (fun _ => 0) := by
  refine ⟨2, by omega, (fun _ => 0), (fun _ => 0), by ext i; simp [splice, concat], rfl, ?_⟩
  refine ⟨2, by omega, (fun _ => 0), (fun _ => 0), by ext i; simp [splice, concat], rfl, ?_⟩
  exact (relRepeat_nil _ _).2 (by omega)

theorem Rab_fails_huniq :
    ¬ (∀ (xs ys : List Bool) (n : Nat) (s : Bytes n),
        relRepeat Rab xs n s → relRepeat Rab ys n s → xs = ys) := by
  intro h
  have := h [false,false,false,false] [true,true] 4 (fun _ => 0) four two
  exact absurd this (by simp)
```

Measured footprints: `Rab_lengthDet` `[propext]`; `Rab_fails_huniq`
`[propext, Quot.sound]`. No `Classical.choice`.

**Trap, which cost a probe:** the tail `s₂ : Bytes (n - m)` cannot be written
`(fun _ : Fin 0 => by omega)` — at `n = 4`, `m = 1` the bound is `4 - 1 - 1 - 1`, not
`0`, so `omega` has no hypothesis to work with. Use a plain `(fun _ => 0)` and let the
size be inferred.

### A.2 — §1.1's probe (the work list for §2)

Re-run this after §1.1 to see what the new arm names:

```lean
import Axioms
open Lean

open CodecAxioms in
#eval show Lean.Elab.Command.CommandElabM Unit from do
  let env ← getEnv
  let defs := CodecAxioms.publicDefs env
  let mentioned := CodecAxioms.mentionedByGated env
  let allow := defs.filter (fun n => !mentioned.contains n)
  let _ ← Lean.Elab.Command.liftCoreM (logInfo m!"publicDefs={defs.size} silent={allow.size}")
  let _ ← Lean.Elab.Command.liftCoreM (logInfo m!"Iso.prod in publicDefs: {defs.contains `Iso.prod}")
  let _ ← Lean.Elab.Command.liftCoreM (logInfo m!"Iso.prod in allowlist: {CodecAxioms.definitionSurfaceAllowlist.contains `Iso.prod}")
```

Current output on the pre-change tree: `publicDefs=141 silent=29`,
`Iso.prod in publicDefs: false`, `Iso.prod in allowlist: false`.

---

## Archive ordering

`codec-audit-round-four` archived 2026-11-07, so this change's MODIFIED blocks are
authored against the **post-sync** text. Before archiving:

1. Re-run the live-vs-delta scenario diff for all three modified requirements. Expected:
   `codec/axiom-gate` "partition extends to public definitions" 4 → 6;
   `codec/review-remediation` "documentation distinguishes quoted from derived" 4 → 8;
   `basen` "conformance laws are gated" 6 → 8. **Nothing may be dropped** — these are
   additive-only deltas; a drop means the delta was authored from the wrong base.
2. `openspec validate --all` after the archive; confirm it stays green (it is 11/11 while
   this change is open — one item is the change itself — and should be 10/10 live
   capabilities once archived).
3. No new capability is created. All three are MODIFIED-existing.
