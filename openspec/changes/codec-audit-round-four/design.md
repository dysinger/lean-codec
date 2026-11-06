# Design — `codec-audit-round-four`

## Context

`codec-audit-round-three` (56/56) archived 2026-11-06 and closed the _definition-level_
gap: a public `def` with no law became a build failure, via a **mention proxy**. Round
five audited the result and found that the proxy is right about what it claims and
wrong about what its header says (§D2), that the predicate-ordering advice in
`Sound.lean` is still false in one direction (§D1), and that a specific class of
"why this choice was made" prose survives every gate, because gates check theorems.

This document records only decisions taken on the _new_ evidence. All three audit
reports are cited by finding id (`R5-nn`), and the merged ledger is
`/tmp/r5-SYNTHESIS.md`.

## Goals / Non-Goals

**Goals**

- Retire the last false _mathematical_ claim in the tree (`LengthDet → RelAligned`).
- Turn four "advertised but absent" laws into present ones, with proofs.
- Make `[D4]`'s title honest, because it is the one anchor a porter will trust and be
  misled by.
- Bring `basen` to gate parity and off a 27-commit-stale pin.

**Non-Goals**

- No statement weakened; no decoder/encoder behaviour changed.
- No new carrier for length-changing normalisation (`[D4]`'s real gap) — that is a
  design change, filed as future work in §D4.
- No re-timing of any bench lane.

## Decisions

### D1 — `LengthDet → RelAligned` is refuted; the deliverable is a four-way independence diagram, not a proof

**Measured.** `LengthDet` constrains _one value's_ possible lengths; `RelAligned`
constrains _two values_ over a shared prefix. They are incomparable, and the tree
already contains the witness:

```
relUnambAlignedWitness a := (m=1 -> a = true) | (m=2 -> a = false) | otherwise False
```

`true` sits only at length 1 and `false` only at length 2, so each value has exactly one
length (`LengthDet` holds). But `a = true` at `m=1` and `b = false` at `m=2` are both
all-`0x41`, so the prefix agrees while the values differ (`RelAligned` fails).

**Reproduced by the main agent** (`/tmp/verify/m1.lean`), `[propext]`-only:

```
'Codec.lengthDet_relUnambAlignedWitness'    depends on axioms: [propext]
'Codec.lengthDet_not_implies_relAligned'    depends on axioms: [propext]
```

The auditor additionally proved the **strong form** — it fails _even with productivity
added_ — which matters because `relRepeat_unique_same_length` takes productivity as a
third hypothesis and a reader could reasonably guess the pair suffices.

**Decision.** Land the two theorems, and replace _every_ "open" record with the
refutation: `Codec/Sound.lean` (two docstrings), `AGENTS.md`, and the archived ledger is
history so it is annotated rather than edited (a ledger records what was believed at the
time; rewriting it would hide that the belief was wrong for three rounds).

**The honest statement is a four-way diagram**, and two of its four edges were proved in
round three (§2.1.4) and this round:

| implication                   | status                                                        |
| ----------------------------- | ------------------------------------------------------------- |
| `LengthConst → LengthDet`     | proved (`lengthDet_of_lengthConst`)                           |
| `RelAligned → relUnambiguous` | proved (`relUnambiguous_of_relAligned`)                       |
| `relUnambiguous ↛ RelAligned` | proved (`relUnambiguous_not_implies_relAligned`, round three) |
| `relUnambiguous ↛ LengthDet`  | proved (`lengthDet_not_implied_by_unamb`, round three §2.1.4) |
| **`LengthDet ↛ RelAligned`**  | **proved this round** (`lengthDet_not_implies_relAligned`)    |
| `RelAligned ↛ LengthDet`      | proved (auditor probe; lands with the same task)              |

**Rejected alternative:** weaken `RelAligned` to something `LengthDet` implies, so the
chain shortens. Rejected on the standing preference (prove the true statement, do not
narrow the plan) _and_ on evidence: `relRepeat_cons_eq` uses `hld` only _after_ `hal`
has already identified the two values, so neither hypothesis can be dropped and a
weakened `RelAligned` would not discharge `decodeArray_unique`.

### D2 — The mention proxy is honest; its _header table_ is not

`Axioms.lean`'s def-coverage check is described in its own header as a proxy that "can
be satisfied **vacuously**" — accurate. But the counts table row reads
"mentioned by a gated theorem's type | **111** | has a stated law, by the proxy", and
"has a stated law" is false for two of the eleven: `decodeArrayFast` and
`decodeWholeOneBytes` are thin aliases whose "law" is the `rfl` unfold of their own
body (`#print axioms` reports `no axioms` — the signature of a restatement).

**Decision.** Do **not** delete the alias laws (a recorded alias-equation is
defensible, and §1.8's task explicitly chose "prove one" over "delete"). Change the
column to "named by a gated theorem's type — the proxy's whole measurement (a mention,
not a strength claim)", and add a sentence naming the two vacuous cases. The count
stays 111; what changes is that the table stops implying 111 characterisations.

**Rejected alternative:** add a `definitionSurfaceAliasAllowlist` so the two count as
"alias" rather than "mentioned". Rejected as machinery for two entries — and it would
_reduce_ coverage, since an allowlisted def is exempt from the check entirely, whereas
today both defs are at least named by a law.

### D3 — `decodeWholeBytes_spec` is landable, and the auditor's "unresolved" was a proof-search failure, not a mathematical one

The auditor reported `decodeWholeBytes`'s advertised law as absent and could not close
the transport, ending in `sorryAx`. It closes; main agent, `/tmp/verify/s2z.lean`,
`[propext, Quot.sound]`-only:

```lean
theorem ab_apply {n} (s : Bytes n) (i : Fin (bytesToArray s).size) :
    arrayToBytes (bytesToArray s) i
      = s ⟨i.val, Nat.lt_of_lt_of_eq i.isLt (bytesToArray_size s)⟩   -- Array.getElem_toList + List.getElem_ofFn
theorem ab_eq {n} (s : Bytes n) :
    arrayToBytes (bytesToArray s) = cast (congrArg Bytes (bytesToArray_size s).symm) s
theorem spec_aux {α} (d) (h) {n} (s : Bytes n) (k : Nat) (hk : k = n)
    (a : Bytes k) (ha : a = cast (congrArg Bytes hk.symm) s) :
    d.decodeFull h k a = d.decodeFull h n s := by subst hk; subst ha; rfl
```

**Three traps, all hit, all worth recording:**

1. The docstring claims the round-trip is "`rfl` by `funext`/`Fin.ext`". **It is not.**
   It needs `Array.getElem_toList` (the `Array`→`List` read bridge) and then
   `List.getElem_ofFn`. `Array.getElem_mk` and `Array.getElem_eq_getElem_toList` do
   **not exist** in Lean 4.35.0 — the correct name is `Array.getElem_toList`.
2. **The first version that compiled leaked `Classical.choice`.** Using `simpa` on the
   dependent `Fin` bound reaches classical logic through the `Array`/`List` sizing
   simp set. This is this repo's own documented trap and it fired again. The fix is to
   state the bound with `Nat.lt_of_lt_of_eq i.isLt (bytesToArray_size s)` and never let
   `simp` see it.
3. **The final dependent rewrite cannot be a `rw`.** `decodeFull h (size) (cast …)` →
   `decodeFull h n s` is a rewrite under a dependent argument; `rw`, `subst`, and
   `generalize` each failed with "Dependent elimination failed" or an unsolved bound.
   What works is the `spec_aux` shape above: carry `hk : k = n` and `ha : a = cast …`
   as _hypotheses_ so `subst` has the orientation it needs.

**Decision.** Land all three lemmas in `Codec/Packed.lean` and correct the docstring's
"`rfl`" claim to name the two real bridge lemmas.

### D4 — `[D4]`'s title is the defect, and the fix is prose; the missing carrier is future work

`[D4]` is headed "**Lossless capture**" and opens by presenting capture-verbatim as the
answer to the paper's `ignore`. Both shipped mechanisms are **length-preserving**:
`norm : Bytes n → Bytes n` (the `Normal` quotient) and `relTakeWhile`, which relates a
run of length `n` to a value of _all_ `n` bytes. `ignore`'s sole purpose is
**length-changing** — any run of blanks → a fixed run.

Verified: no definition anywhere in the tree has type `Bytes m → Bytes n` with `m` and
`n` independent.

**Decision.** Rewrite the title and the opening paragraph to state, at the anchor, that
the paper's whitespace use case is **not reproduced** by core, and that it needs a
different carrier. Keep the 40-lines-later caveat (it is correct) but stop making it
carry the whole disclosure.

**Not doing: building the carrier.** That would be `Iso (Bytes m) (Bytes n)` or a
`List`-shaped normalizer — a design change with its own law obligations
(`Productive`, `ConsumesByte`, a shrink witness), well outside a prose-and-lore change.
Recorded in `tasks.md` §8 as the follow-on.

### D5 — `basen`'s eight dead `*Run` values: delete, not allowlist

The def-coverage port would otherwise demand a reason for each. Verified independently:
`bitRun`, `quartetRun`, `octRun`, `digRun`, `b32Run`, `b64Run`, `b32TailRun`,
`b64TailRun` each occur **exactly once** in the tree — their own `def`. `hexRun` has five
occurrences and is genuinely used by base16's fold proofs.

**Decision.** Delete the eight dead ones (keeping `hexRun`), then port the check.
Deleting public API is a real cost, so it is scoped: these are `Run` _values_ that only
exist so a docstring could say "the run value for base N", and nothing — no theorem, no
proof line, no bench — consumes them. Allowlisting them would make the gate greener
while leaving the dead API in place, which is the exact failure mode §1.8 exists to
prevent.

**Fallback if an owner objects:** allowlist each with the reason "documented run value
for base N, no in-tree consumer" — recorded here so the decision need not return.

### D6 — The stale pin is bumped, but `basen`'s green-on-HEAD build is _verified_, not assumed

`basen` pins `codec` at `eb1d77a`; HEAD is `e1d8d12` — 27 commits. Those commits add
theorems and _withdraw a prose claim_; none changes a type `basen` imports. Still:

**Decision.** `nix flake lock --update-input codec` (targeted, never all inputs), then
re-run **all three** gates (`lake build`, `lake build bench`, `nix build '.#bench'`) and
record the actual output. The audit predicted success but **did not run it** (it would
have had to mutate `lake-manifest.json`, which its brief forbade). A predicted-green that
is recorded as run is the defect this change exists to fix.

### D7 — `basen`'s header prose gets a _gate_, not just a correction

`basen`'s `Axioms.lean:32-40` says `440 pins / 437 / 483`; reality is
`441 / 438 / 484`. The `headerNumbers` `run_cmd` asserts the _table_
(`expectedPub=484` etc.) and never reads the paragraph, so the paragraph rotted
undetected across a full regeneration — precisely the failure that check was built to
prevent in codec.

**Decision.** Correct the three figures **and** extend `headerNumbers` so the prose
constants are computed (`gatedNames.length`, `generatedAuxAllowlist.size`, plus the
count of `Codec.*` pins) rather than remembered. Do not soften it to a `logInfo`.

**Also corrected:** the coverage `run_cmd`'s message prints
`438 pinned + 46 allowlisted = 447 of 484`. The `447` is the _kept_ side of
`partitionInto` (`484 − 37 suffix-dropped`), not `438 + 46`; the printed equation is
arithmetically false and conflates two sets. The checks are right; the message is wrong.

### D8 — The `filterMap` contradiction: delete the lemma, do not fix its docstring

`length_filterMap_le`'s docstring says `packedCands` "is a `filterMap` of
`(decodeArray d a k).attach`", and the same file bolds 30 lines earlier that it is built
by **`map`**, "a measured 2.6×". The lemma has **zero callers**; `packedCands`'s length
bound is proved by `length_map` in `length_packedCands_le`.

**Decision.** Delete the dead lemma rather than repair its prose — an unused lemma with
a false docstring has no reader to serve, and deleting keeps the file honest about its
own measured design choice. If a future `filterMap` search needs it, it is three lines.

### D9 — The nine necessity/uniqueness docstrings: correct in place, and record the class

Each of R5-13 … R5-18 and R5-03/10 is a variant of "this is the only X" / "the full
list" / "none has a caller" / "sound only when". Every one is at a point where a _reader_
would form a plan (why the code is specialised, why a list is complete, what a gate
measures), and every over-claim was in the direction of _narrowing what the reader must
do_ — so a reader who trusted it would under-prove or under-test.

**Decision.** Correct each in place with (a) what is actually true, (b) one clause
naming the over-claim so it cannot silently return, matching the house style rounds two
and three established. Additionally record the **class** in `openspec/lean-notes.md`
(this is a lesson, not direction): _a "necessity" claim about why a code was written the
way it is has no gate; check it with a grep before believing it._

## Risks / Trade-offs

- **[Deleting eight public `basen` `def`s is an API break]** → they are consumed by
  nothing in the tree, and `basen` ships no downstream user yet. The fallback
  (allowlist with a reason) is recorded in D5.
- **[The pin bump could break `basen`]** → then the breakage is the finding, and it is
  recorded rather than reverted. The 27 commits are additive.
- **[`[D4]`'s corrected title reads as a regression]** → it is not: nothing is removed.
  The anchor now says at the top what it previously said 40 lines down.
- **[Correcting prose without a gate invites recurrence]** → mitigated for the two
  Axioms tables (§D2, §D7) and accepted elsewhere; §D9's lesson entry is the mechanism
  for the rest.

## Migration Plan

1. `Codec/Sound.lean` maths (§1): the independence proofs first, because four prose
   sites depend on them existing.
2. `Codec/Packed.lean` + `Codec/Combinators.lean` laws (§2, §3), with the proof notes
   from §D3.
3. `basen` (§5, §6): delete dead defs, port the check, bump the pin, run every gate.
4. Prose (§4 README anchors, §7 Axioms, §8 lessons) — after the code, so every
   corrected sentence points at something that now exists.
5. Gates everywhere, then archive.

## Open Questions

- **Should the length-changing carrier be built?** Yes eventually; not here (§D4). It
  needs an owner decision because it changes what `[S3]`/`[S4]` may ship.
- **Is `relRepeat_induction`'s zero-caller status a defect?** The audit raised it as
  "available-but-unused". Recorded in the ledger as a known state, not a task: the
  principle's existence _is_ the least-fixpoint property, so its being unused does not
  weaken the claim. No action.
