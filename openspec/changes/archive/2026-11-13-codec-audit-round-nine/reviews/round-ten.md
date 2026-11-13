# Round ten — the adversarial review of round nine's own work

This file exists because the code cites reviewer ids **27 times** and the reports
themselves lived in `/tmp`, which is not under git history. `AGENTS.md` is explicit: a reviewer's
report that only lives in `/tmp` is a citation to a file that will not exist for the next
reader. So the findings whose ids appear in the source are recorded here, in place.

**Repo scope:** `lean-codec` only. Each reviewer ran read-only (`grep`/`git`/`python3`, and
`nix develop --command lake env lean /tmp/x.lean` for `#print axioms`/`#check`/`#eval`);
none ran `lake build`, none modified a file.

**Four passes**, each attacking the previous pass's fixes rather than the original tree —
because that is where the defects were. The pattern is worth stating up front: **every
pass found defects in the fixes from the pass before**, including the final one, and
three of them were defects _introduced by the fix for the previous defect_.

| pass | axis                                         | found                                                                  | landed as                       |
| ---- | -------------------------------------------- | ---------------------------------------------------------------------- | ------------------------------- |
| 1    | paper/README departures; gate arms; numbers  | 2 MUST / 4 SHOULD / 5 NITPICK; 5 MUST / 11 SHOULD / 5 NITPICK; 8 terms | `5c0a1bc`, `41e2d21`            |
| 2    | the pass-1 fixes + theorem statements        | 2 MUST (proof axis); 1 MUST + 5 SHOULD + 4 NITPICK                     | `8835519`, `3d67387`            |
| 3    | the pass-2 fixes; prose written that session | 6 MUST / 5 SHOULD / 4 NITPICK; 4 MUST / 4 SHOULD / 3 NITPICK           | `bc795af`, `6aec86b`, `9b34a98` |
| 4    | the pass-3 fixes                             | this file's residue                                                    | see below                       |

## How to read an id

Every citation in the source is `review P<pass>-<axis><n>`, and **the id is unique across
all four passes** — that is the whole point of the scheme, because the first version of
this file reused `A-1` for three different findings and `M-1` for three more. The axis
letters are:

| letter | axis                                                                  |
| ------ | --------------------------------------------------------------------- |
| `G`    | gate arms and the theorem/definition partition                        |
| `A`    | the footprint vocabulary (pass 2's series — **not** pass 1's numbers) |
| `NB`   | numbers and build claims                                              |
| `PA`   | PAPER.md / README departures                                          |
| `D`    | the proof/docstring axis                                              |
| `M`    | mirror and drift                                                      |
| `N`    | prose nitpicks                                                        |

So `P1-NB4` is pass 1, a numbers/build finding; `P2-A4` is pass 2, a vocabulary finding;
`P3-M4` is pass 3, a mirror finding. A letter `b` suffix (`P1-PA1b`, `P2-G07b`) marks a
second finding the same pass filed in the same family.

## Every id cited in the source, and what closed it

Verified by extracting every `review P…` from `README.md`, `Axioms.lean`, `flake.nix`,
`Bench.lean`, `scripts/gen-axioms.lean` and `Codec/*.lean` and requiring a row here. **27
ids, 27 rows.**

### Pass 1 — gate arms (`P1-G`)

| id       | finding                                                                                                                                             | closed by                                            |
| -------- | --------------------------------------------------------------------------------------------------------------------------------------------------- | ---------------------------------------------------- |
| `P1-G02` | the `_ => true` footprint fallthrough was called "compile-time-shaped"; a `String` match cannot be exhaustive                                       | a label list + a classifier-walking arm              |
| `P1-G03` | `mentionsFootprint` scanned raw text while `looksLikeAxiomList` scanned joined text, so a wrapped literal was blind to one and visible to the other | both call `joinDoc`; the exemption list fell 2 → 1   |
| `P1-G04` | the census comment claimed `Codec.Bench.cRefByteMany` was walked; `Axioms.lean` imports `Codec`, never `Bench`                                      | measured statement + a printed note                  |
| `P1-G07` | the allowlist footprint decomposition was **printed-only**, so a law could rotate between buckets green                                             | `expectedAllowlistFootprints`, asserted term by term |
| `P1-G08` | `findFrom.induct`'s promotion rationale claimed its _type_ names `Codec.findFrom`; measured, it names no `Codec` constant                           | corrected; the guard relabelled a regression net     |
| `P1-G11` | "the only allowlisted name with a non-empty footprint" — measured, 43 of 82 are                                                                     | corrected                                            |

### Pass 1 — numbers and build claims (`P1-NB`)

| id        | finding                                                                                                                       | closed by                                            |
| --------- | ----------------------------------------------------------------------------------------------------------------------------- | ---------------------------------------------------- |
| `P1-NB1`  | `README` said `~10.5–11.6×`; `11.6` is producible from no same-run pair. **Introduced while fixing the padded-range defect.** | `10.5–11.5×`, both terms shown                       |
| `P1-NB4`  | **`checks.bench` could not build**: `nativeBuildInputs = [ pkgs.git ]` → `lake: command not found` (exit 127)                 | toolchain inputs, writable copy, `set -euo pipefail` |
| `P1-NB6`  | `README` quoted a 10-line gate output with **six stale values**                                                               | replaced with the 14 lines from a green build        |
| `P1-NB8`  | "`48 %` off" is `(0.045 − 0.03)/0.03 = 50.0 %`                                                                                | corrected, with the mixing that produced 48 % named  |
| `P1-NB10` | `~64–67 ns/call` mixes a run minimum into a median range                                                                      | `65–67` (the two run medians)                        |
| `P1-NB11` | "a `~55 ns/step` decode" is a point for a `51.1–54.9` range                                                                   | range quoted                                         |

### Pass 1 — PAPER/README departures (`P1-PA`)

| id        | finding                                                                                                                                                                                      | closed by                                    |
| --------- | -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | -------------------------------------------- |
| `P1-PA1`  | `[S5]` said the paper closes its `nil` rule at `True`; `PAPER.md:433-439` + `:647` show `nil $ pure ()` with `pure x = Rel [(x, "")]` — the empty string. **The "departure" did not exist.** | rewritten; no departure claimed              |
| `P1-PA1b` | the same false paper claim in `relRepeat`'s module docstring                                                                                                                                 | rewritten                                    |
| `P1-PA3`  | `[D4]` said the `Normal` layer's normalizer is `norm : Bytes n → Bytes n`; the layer is parametric and no such function exists                                                               | parametric form; three surviving sites fixed |

### Pass 2 — the footprint vocabulary (`P2-A`)

| id       | finding                                                                                                                                                           | closed by                                                         |
| -------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------- | ----------------------------------------------------------------- |
| `P2-A1`  | four copies of the vocabulary (phrase array, classifier's inline list, label array, adjudicating `match`) with no arm comparing any pair                          | **copies deleted**; one `footprintVocabulary`, everything derived |
| `P2-A2`  | `recognised` was _defined_ as `mentioningLiteral − blind − exempt`, making the "reconciliation identity" the tautology `x−y+z+y+z=x` — unfalsifiable              | `mentionedAndRecognised`, accumulated by the walk                 |
| `P2-A4`  | the eight theorem-suffix names lived in **three** copies                                                                                                          | `theoremNameSuffixes`, one array, read by all three readers       |
| `P2-A8`  | the exemption list's backward check could not distinguish "the entry matched" from "never reached", and asserted the first cause                                  | two distinct failure texts; a non-resolving entry also fails      |
| `P2-A13` | `footprintClassifications` was validated by **key only**, so a right-key/wrong-class remap was green — and on the `.choice` row no tree inhabitant could catch it | semantics-written probes in both directions; mutation-tested      |

### Pass 2 — proof/docstring (`P2-D`, `P2-F`, `P2-G`)

| id        | finding                                                                                                                                               | closed by                                                                      |
| --------- | ----------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------ |
| `P2-D9`   | `emptyConsumesByte` stated its footprint as prose ("the usual `propext` and `Quot.sound` pair"), which no phrase recognises — a claim read by nothing | written as a backticked literal; the arm now reads it                          |
| `P2-F13`  | _(the class-table capability check, same code as `P2-A13`; cited where the fix is)_                                                                   | as `P2-A13`                                                                    |
| `P2-G07b` | two undisclosed duplicate laws (`drop_zero_eq_id` ≡ `Suffix.drop_zero`; `bytesToArray_size` ≡ `decodeWholeBytes_size`)                                | disclosed in place; not deleted, because deleting moves the asserted partition |

### Pass 2 — PAPER/README (`P2-PA`)

| id       | finding                                                                                                       | closed by                                   |
| -------- | ------------------------------------------------------------------------------------------------------------- | ------------------------------------------- |
| `P2-PA1` | `[S5]`'s replacement overcorrected into a claim about the paper's `True` closure that the paper does not make | corrected to the `nil $ pure ()` derivation |

### Pass 3 — mirror (`P3-M`)

| id      | finding                                                                                                                                                                                                     | closed by                                                                            |
| ------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------ |
| `P3-M4` | `mirrorSelfCheck` checked only _inside_ the generator, while its docstring claimed the cross-file comparison was "what `lake build` does" — false for the undercounting direction that already cost a round | docstring corrected **and** a real `checks.mirror` that runs the generator and diffs |

### Pass 4 — prose (`P4-N`)

| id      | finding                                                                                                                                           | closed by                                 |
| ------- | ------------------------------------------------------------------------------------------------------------------------------------------------- | ----------------------------------------- |
| `P4-N1` | "length-preserving **at any instantiation**" — a `List UInt8` normalizer that shortens typechecks fine (and `Codec/Normal.lean:97` said the same) | restricted to the `Bytes n` instantiation |
| `P4-N4` | `[D4]`'s "bijection … not claimed" **under**claimed: the four-law set exists                                                                      | corrected                                 |

### Findings filed but not cited in the source

Kept here so the next round does not re-derive them: `P1-G05`/`P1-G09`/`P1-G10`/`P1-G12`–
`P1-G15` (gate, closed or documented as latent), `P1-NB2`/`P1-NB3`/`P1-NB5`/`P1-NB7`/
`P1-NB9`/`P1-NB12`–`P1-NB14` (numbers), `P2-A3`/`P2-A5`/`P2-A6` (vocabulary),
`P2-M1`/`P2-M2` (the `Functional`-at-`alt` finding and the entry-point provenance),
`P2-S3` (the `6 ns/step` in a docstring), `P4-N2`–`P4-N13`. `P4-N3` is **open** — see the
next section.

## Note on `P4-N3` (not closed, and deliberately)

`26.97–28.56` (filed as `P4-N3`) is quoted as "across all three decode tables" and does splice two lanes
(`decodeFullArray` and `decodeWhole`) from two sessions. The two lanes are the same
decoder by a proved equality (`decodeWhole_eq`), so the figure is _arithmetically_ sound,
but it is a cross-table interval of exactly the kind this document forbids. It is left
open here rather than silently fixed because **the correct fix is a re-run**, and the owner
has deferred benchmarking (`tasks.md` 2.1/2.3). Recorded so the next session does not have
to re-derive it.

## What this round's reviews establish, beyond the individual findings

1. **A check is only as good as what enters it** — and a fix is a check. Every pass found
   the previous pass's fix defective, four passes deep.
2. **A claim scoped by a path or a grep is only as good as the path** (F-1, G-04). Both
   times the evidence command excluded the file that falsified the claim.
3. **An assertion can be a tautology and look like a decomposition** (A-2′). Writing
   `recognised` as the residual of the other two counts made the identity unfalsifiable.
4. **The most dangerous table row is the one the tree cannot exercise** (F-13): the
   `Classical.choice` class has no inhabitant, so only a semantics-written probe can
   validate it.
