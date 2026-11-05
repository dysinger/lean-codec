# Design

## Context

`codec-audit-round-three` acts on the 2026-11-05 third audit
(`/tmp/r3-a-codec.md`, `/tmp/r3-b-basen.md`, `/tmp/r3-c-cross.md`).
`codec-audit-round-two` is complete and its gates are green; this document records
only decisions taken on the _new_ evidence, and the constraints they must respect.

Everything marked **measured** was re-run in this repository before being written
down, so it can be re-derived rather than trusted. Where a reviewer's claim was
checked and did not survive, that is recorded here too — a refuted finding is a
result, and suppressing it would be the defect this change is about.

## Goals / Non-Goals

**Goals:**

- Make law coverage **structural**: a public `def` with no law becomes a build
  failure, not something a human must enumerate.
- Close the two genuine coverage holes the enumeration found: five of the eight
  bounded `Codec` values, and the decode→encode half of `sepBy`/`takeWhile`.
- Make the `RelAligned`/`relUnambiguous` relationship the measured one.
- Bring the ecosystem's two remaining gate asymmetries (`lean-basen`,
  `lean-nix-flake-template`) to parity with codec.

**Non-Goals:**

- No weakening of any theorem statement.
- No new formats in core (`[S3]`), no unbounded `many` `Codec` node (`[S6]`).
- Not a performance change; no bench lane is re-timed.
- **Not** a correction of `Axioms.lean`'s footprint table — see D1.

## Decisions

### D1 — The footprint-table finding is refuted; only the _absence of a check_ remains

A reviewer reported that `Axioms.lean`'s header table says `197` for
`[propext, Quot.sound]` while the generated body contains `195`, and that the four
rows do not sum to `292`. **Measured directly against the generated body:**

```
pq   depends on axioms: [propext, Quot.sound]   197
p    depends on axioms: [propext]                61
q    depends on axioms: [Quot.sound]              4
none does not depend on any axioms               30
total 292     #print axioms commands 292
```

The table is **correct**. The reviewer's parser truncated at the `?` in
`Codec.attach_getElem?_corr` and `Codec.map_toList_eq_ofFn_none_iff`, which their
own F16 acknowledges as a tooling artifact. No correction is made.

**What survives is a real, smaller gap:** nothing mechanically re-derives the
header. `partition` and `gateCoverage` check set _membership_, not the counts, so a
future regeneration could leave the table stale and no gate would notice. Task 1.6
makes the generator emit the distribution it computed, so the header becomes
generated rather than remembered. **This is deliberately last in this change** —
it is bookkeeping, and doing it first would have been work spent on a non-defect.

### D2 — The gate's universe is the defect; extend the partition to definitions

**Problem.** `Axioms.lean:120-136` keeps only `thmInfo` constants. A public `def`
with no law is therefore in neither set of the partition. Measured: `btake`
(`Codec/Codec.lean:112`) has exactly one occurrence in the tree — its own
definition — and no lemma; `maybe`, `manyUpTo`, `seqRight`, `seqLeft`, `between`
likewise have zero theorems (`grep -c "\`Codec.<n>" Axioms.lean`→`0` for each).

**Decision.** Add a definition-coverage check: for each public `def` in
`Codec`/`Iso`, require that some gated theorem's statement mentions it, **or** that
it is listed in a `definitionSurfaceAllowlist` with a reason. A `def` in neither
fails the build printing the name.

**The mechanism, and why it is a _mention_ check.** "Does a law exist for this
`def`?" is not directly decidable — provability is not a property you can grep for.
What _is_ decidable is whether any gated theorem's _type_ mentions the constant,
which is the honest proxy: a `def` no theorem mentions has no stated law, and a
`def` one mentions has at least been reasoned about in a proof. This is the same
escalating-proxy discipline the axiom gate already uses (it proxies "is this a
law" by "is this a `thmInfo`"), and it is stated as a proxy rather than as a
guarantee.

**Rejected alternative:** require a naming convention (`<def>_spec`) so the check
is exact. Rejected because the tree's laws are already named
`encodeSepBy_rel`/`decodeSepBy_spec`/`decodeChainl1_spec`, and forcing a single
suffix would rename dozens of gated laws — a large diff for a check that the
mention proxy already covers.

**Honest limit.** The mention proxy can be satisfied by a vacuous theorem that
mentions the name trivially. It cannot be satisfied by _silence_, which is the
failure mode that is actually present. Recorded as the strongest property a
decidable check can have here, not as soundness.

### D3 — The `count` step law is the root of five of the eight gaps

`count n p` is `Iso.foldl`-shaped over `n`, and its only law is
`Rel_count_zero`, the `n = 0` case. The inductive step
(`Rel (count (n+1) p) xs s`) is where `Iso.cons` and `Codec.seq` actually do work,
and it is unproved — so `manyUpTo`, which is
`choice ((List.range (n+1)).map (fun k => count k p))`, has nothing to build on
even though `Rel_choice` holds. The dependency order for part 1 is therefore:

1. `count` step law (unblocks `manyUpTo`);
2. `manyUpTo` law, via a `List.range`/`map` membership lemma that does not
   currently exist;
3. `seqRight`/`seqLeft`/`between` `Rel` characterizations — these are pure `Iso`
   rewrites and are independent of 1–2, so they can land in parallel;
4. `optional`/`choice` missing `Rel` directions, and `maybe` (an alias, one
   `rfl`-shaped law).

`between` is the paper's own §6.1 derived combinator, so a porter following the
paper will reach for it first and find no proof — which is why it is in this
change rather than a later one.

### D4 — The `RelAligned` ordering claim is false, and the fix is a theorem

**Measured.** `Codec/Sound.lean:1119-1129` asserts

> "there is no relation that is unambiguous and not aligned, and no such witness
> is worth hunting for"

Let `S a t := (a = true ∧ m = 1) ∨ (a = false ∧ m = 2)`. Then:

```
'S_unamb'       depends on axioms: [propext, Quot.sound]     -- relUnambiguous S
'S_not_aligned'  depends on axioms: [propext]                 -- ¬ RelAligned S
```

`true` relates only at length 1, `false` only at length 2 — so the length pins the
value and `relUnambiguous` holds — while `RelAligned` compares a length-1 string
against a length-2 one with a shared prefix and demands the values agree. The
predicates are **incomparable**: neither implies the other.

**Decision.** Land `relUnambiguous_not_implies_relAligned` as a theorem and replace
the paragraph with the measured statement. **Do not** merely delete the false
sentence: the paragraph exists to advise a caller which hypothesis to prove, and
the advice is the harmful part. The replacement must say what
`decodeArray_unique` actually needs (`RelAligned` **and** `Functional`) and why
`relUnambiguous` will not substitute.

**Why this is not a "weaker claim" fix.** The standing preference is to prove the
true statement rather than narrow the plan. Here the true statement is _stronger_
in scope — the predicates are incomparable, which is more than "the ordering was
unproven" — and it is proved, not asserted.

### D5 — `lean-basen` gate parity comes first, because everything else leans on it

`lean-basen`'s `Axioms.lean` is 440 hand-written `#print axioms` blocks with no
`run_cmd`, no `Environment` walk, no partition. Measured: 437 public theorems, 437
`BaseN.*` pins + 3 `Codec.*` pins = 440, consistent **today**; `grep -cE 'run_cmd|
Lean\.Elab|Environment|partitionInto|getEnv' Axioms.lean` → `0`.

**Decision.** Port codec's shape: `partitionInto` over the compiled environment
plus the two `run_cmd` blocks. This is task 1.0 — before any new basen law — for
two reasons: it is a _known_ fix (codec has run it for two rounds), and every law
part 2 adds would otherwise land un-gated, which would reproduce the defect the
change exists to close.

**Where codec's lakefile comment is now wrong:** `lean-codec/lakefile.lean:28`
says the codec `Axioms` lib mirrors `../lean-basen/Axioms.lean` "which is where
this shape is proven in this ecosystem". Basen has the _shape_ (a
`@[default_target]` Axioms lib) but not the _mechanism_. Fix the comment to say
codec strengthened what it inherited, and that basen now adopts the mechanism
back. Direction matters: leaving it makes the next reader copy the weaker version.

### D6 — The template's gate claim must become true, not be removed

`lean-nix-flake-template/lakefile.lean` has no `moreLeanArgs :=
#["-DwarningAsError=true"]` (`grep -c warningAsError` → `0`, vs codec `5`, basen
`3`), while `README.md:50` says "a build that encounters a `sorry` fails" and
`default.nix:101` repeats it. Two options were considered:

- **remove the claim** from the README — cheap, but leaves every scaffolded
  project with a non-enforcing gate, which is the state that produced this
  finding;
- **add the flag** — one line, makes the existing README true, and propagates to
  every future project.

Take the second. It is the same call the standing preference names: correct over
convenient. Also correct `@ "main"` → `@ "master"` at `README.md:134`, since
codec's branch is `master` and basen's lakefile documents the point explicitly.

### D7 — Prose findings are satisfied by making the text match a measurement

Five smaller items, each a claim the code does not support. None needs design
content, all need a measurement attached at the point of use:

- `CHANGELOG.md:59-64` documents `Codec.Buffer` and four named theorems;
  `#check @Codec.Buffer` → unknown constant. The entry was seeded from history in
  the same commit that deleted the tier. Delete the entry, keep the history in the
  commit message where it belongs.
- README:380 cites `Codec.encodeArray_eq` as `Codec/Encode.lean`'s sample law; it
  lives in `Packed.lean`, and `Encode.lean` has no law about `encode` at all
  (`encode_rel` is in `Sound.lean`). Cite something in the module, or state that
  the encoder's soundness law lives in `Sound`.
- README:577-582 presents "the leak's growth is in the result list" inside a
  paragraph introduced as the paper's own cost; the paper says no such thing and
  nothing here measured it. Mark it as unmeasured, or measure it.
- README:222 splices two paper fragments with no `…` between them.
- `lean-basen/CHANGELOG.md:75` says the 4.35.0 move "was declined" while `:42`
  records it as taken — a self-contradiction 33 lines apart, in the shape the
  repo's own `AGENTS.md` names as a defect.

## Risks / Trade-offs

- **[The definition allowlist could become a dumping ground]** → same mitigation
  as the generated-aux allowlist: a `def` in neither set fails the build, and each
  entry carries a reason, so growth is visible in the diff.
- **[The mention proxy may be satisfied vacuously]** → accepted and recorded
  (D2). It closes the practically-present failure mode (silence) and is stated as
  a proxy, never as a guarantee.
- **[Proving `count`'s step may be more work than estimated]** → it is an
  `Iso.foldl` over `n`, and `foldRec_append` / `isoConsumesByte` already exist for
  the shape. If it stalls, the fallback is to record `count`'s step as **open**
  with the precise blocking lemma named — never to claim the derived combinators
  are proven.
- **[Two repos plus a template in one change]** → the ordering in `tasks.md` is
  strict: basen gate parity, then codec laws, then prose. Cross-repo work is
  listed per-repo with its own gate commands (they are different flakes).
- **[The reviewer's F15 was wrong]** → recorded in D1 so it is not re-litigated;
  the residual (no mechanical re-derivation of the header) is scheduled last,
  explicitly, as bookkeeping.

## Migration Plan

1. `lean-basen` gate parity (§1.0) — the mechanism every later law leans on.
2. Codec law coverage (§1.1–1.5): `count` step, then `manyUpTo`,
   `seqRight`/`seqLeft`/`between`, `optional`/`choice`/`maybe`, then the
   `sepBy`/`takeWhile` encode halves; `btake`/`Suffix.consumed` resolved.
3. Definition-coverage check (§1.7), then the generated footprint table (§1.8).
4. Prose (§2): `RelAligned` theorem first (it is a theorem, not an edit), then
   template, then the remaining text corrections.
5. Gates everywhere: codec `lake build` / `lake build bench` /
   `openspec validate --all` / `nix flake check`; basen `lake build` /
   `lake build bench` / `nix build '.#bench'`; template `nix flake check`.

## Open Questions

- **Archive ordering against `codec-audit-round-two`.** That change is complete
  and its tasks are ticked, but it is **not yet archived** — this change was
  authored first, at the owner's direction. If both touch
  `codec/axiom-gate`'s partition requirement, the MODIFIED blocks could collide.
  Check at sync time: round two's delta and this one's both modify
  "The axiom footprint of every public theorem is checked on every build".
  **Archive `codec-audit-round-two` first**, then run
  `openspec validate --all` before archiving this one — and carry every scenario
  from round two's MODIFIED block into this change's if they both still apply.
- No blocking design questions. The one pre-authorized fallback is D3's
  `count`-step case, which is recorded so implementation need not return.
