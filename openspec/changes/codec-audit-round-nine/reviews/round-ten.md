# Round ten — the adversarial review of round nine's own work

This file exists because the code cites it **thirteen times** and the reports themselves
lived in `/tmp`, which is not under git history. `AGENTS.md` is explicit: a reviewer's
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

## The findings, by id, with what each one was and what closed it

### Numbers (prefix `A-`)

| id   | finding                                                                                                                                           | closed by                                           |
| ---- | ------------------------------------------------------------------------------------------------------------------------------------------------- | --------------------------------------------------- |
| A-1  | `README` said the gap was `~10.5–11.6×`; `11.6` is producible from no same-run pair. **Introduced while fixing the padded-range defect.**         | `10.5–11.5×`, both terms shown                      |
| A-2  | `AGENTS.md` said the def counts were `140 = 111 + 29`; they are `140 = 115 + 25`                                                                  | corrected                                           |
| A-3  | `44 of 83` allowlisted theorems footprinted; the allowlist has 82 entries, so `43 of 82`                                                          | corrected                                           |
| A-4  | **`checks.bench` could not build**: `nativeBuildInputs = [ pkgs.git ]`, so `lake: command not found` (exit 127) — red from the day it was written | `flake.nix`; see F-12                               |
| A-5  | the flat `~10–11×` quoted in two places after the paragraph declaring it wrong                                                                    | both corrected to `~10.5–11.5×`                     |
| A-6  | `README` quoted a 10-line gate output with **six stale values**                                                                                   | replaced with the 14 lines from a green build       |
| A-7  | floor "`~15–18` cold"; `18` is in no table of either document                                                                                     | `15`, the bare cell                                 |
| A-8  | "`48 %` off" is `(0.045 − 0.03)/0.03 = 50.0 %`                                                                                                    | corrected, with the mixing that produced 48 % named |
| A-9  | `~19.6–22.0×` excludes its own lower endpoint `19.55`                                                                                             | `~19.55–21.96×`                                     |
| A-10 | `~64–67 ns/call` mixes a run minimum into a median range                                                                                          | `65–67` (the two run medians)                       |
| A-11 | "a `~55 ns/step` decode" is a point for a `51.1–54.9` range                                                                                       | range quoted                                        |
| A-12 | "`~27–28 ns/step`" excludes the cells `26.97` and `28.56`                                                                                         | range quoted                                        |
| A-13 | `AGENTS.md`'s "4 quantities, 14 values, 4 explicitly withdrawn" — the sentence marks exactly **one** withdrawn                                    | the bullet now refuses to state a total             |
| A-14 | header table's `thmInfo 769` read as a census row while `defnInfo` is only in the mention proxy                                                   | noted in the arm's own comment                      |

### Gate arms (prefix `G-`)

| id   | finding                                                                                                                                                                      | closed by                                                                |
| ---- | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------ |
| G-01 | after §5.3a's fix, `Bytes.ext_iff`'s docstring said ``Footprint: `Quot.sound` alone`` — a spelling **no** phrase recognises, so the claim went from checked to **invisible** | rewritten as a bare literal; the arm now reads it                        |
| G-02 | the `_ => true` fallthrough was called "compile-time-shaped"; a `String` match cannot be exhaustive                                                                          | `footprintClaimLabels` + a classifier-walking arm                        |
| G-03 | `mentionsFootprint` scanned raw text while `looksLikeAxiomList` scanned joined text, so a wrapped literal was blind to one and visible to the other                          | both call `joinDoc`; the exemption list fell from 2 entries to 1         |
| G-04 | the census comment claimed `Codec.Bench.cRefByteMany` was walked; `Axioms.lean` imports `Codec`, never `Bench`                                                               | comment replaced with the measured statement + a printed note            |
| G-05 | the eight theorem-suffix names lived in **three** copies                                                                                                                     | `theoremNameSuffixes`, one array                                         |
| G-06 | `classifyFootprintClaim` returns the first list-order match, so `axiom-free` can mis-label a two-claim sentence                                                              | longest-match-first ordering; documented                                 |
| G-07 | the allowlist footprint decomposition was **printed-only**, so a law could rotate between buckets green                                                                      | `expectedAllowlistFootprints`, asserted term by term                     |
| G-08 | `findFrom.induct`'s promotion rationale claimed its _type_ names `Codec.findFrom`; measured, it names no `Codec` constant                                                    | corrected; the guard kept and relabelled a regression net                |
| G-09 | the same docstring said five gated laws name `Codec.findFrom`; measured six (`findByte_spec` omitted)                                                                        | corrected                                                                |
| G-10 | `expectedDefDoc = 11` under-counted footprint-mentioning `def` docstrings (13 once newlines are joined)                                                                      | 13                                                                       |
| G-11 | "the only allowlisted name with a non-empty footprint" — measured, 43 of 82 are                                                                                              | corrected                                                                |
| G-12 | the `authored` exemption arm could not detect a later suffix match                                                                                                           | `wouldDrop` printed; the arm reports the dead code rather than hiding it |
| G-13 | `coveredBy` summed across promotion pairs                                                                                                                                    | noted; single-entry list today, and the arm names the risk               |
| G-14 | `exclusions ∩ gatedNames` unchecked                                                                                                                                          | recorded as latent (`exclusions` is empty)                               |
| G-15 | `looksLikeAxiomList`'s own vocabulary is a four-name whitelist — the denominator is a list too                                                                               | documented as "broader, not complete"                                    |

### The vocabulary, passes 2–3 (prefix `A-`, second series)

| id   | finding                                                                                                                                                                                                     | closed by                                                             |
| ---- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | --------------------------------------------------------------------- |
| A-1′ | `everyEmittedLabelIsAdjudicated` walked `footprintClaimPhrases` — a **copy** — never the classifier's inline list, and never the adjudicating `match`. Four copies, zero arms comparing them                | **all copies deleted**; one `footprintVocabulary`, everything derived |
| A-2′ | `recognised` was _defined_ as `mentioningLiteral − blind − exempt`, making the "reconciliation identity" the tautology `x−y−z+y+z=x` — an assertion that could never fire                                   | `mentionedAndRecognised`, accumulated by the walk                     |
| A-3′ | the two text views still differed on six realistic spellings                                                                                                                                                | `joinDoc` shared                                                      |
| A-4′ | `mirrorSelfCheck` checked only _inside_ the generator, while its docstring claimed the cross-file comparison was "what `lake build` does" — false for the undercounting direction that already cost a round | docstring corrected **and** a real `checks.mirror` added (F-13)       |
| A-5′ | `namesSelf`'s "self wins if named anywhere in the prefix" mis-attributes on incidental mention                                                                                                              | 0 live cases; shape recorded as unguarded                             |
| A-6′ | —                                                                                                                                                                                                           | see A-6 above                                                         |

### The theorem statements (prefix `M-`/`S-`, pass 2)

| id  | finding                                                                                                                                                              | closed by                                                       |
| --- | -------------------------------------------------------------------------------------------------------------------------------------------------------------------- | --------------------------------------------------------------- |
| M-1 | `Functional` is **not** a congruence for `alt`, and nothing recorded where it fails (the tree only documents `Unambiguous`/`RelAligned` at `seq`)                    | `Codec.alt_not_functional`, `[propext]`, gated                  |
| M-2 | the README said the single-value entry point is "tied to the specification"; that law is `Array`-only, and the `Bytes` bridge is a two-step composition nobody names | corrected, with the grep a reader can run                       |
| S-3 | `decodeWhole`'s docstring carried a `6 ns/step` figure — a value `AGENTS.md` lists as **withdrawn** — plus two loaded-session cells                                  | all three removed; the docstring says why no figure lives there |

### Prose (prefix `F-`, pass 4)

| id   | finding                                                                                                                                                                              | closed by                                                                  |
| ---- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ | -------------------------------------------------------------------------- |
| F-1  | "there is no `Normalizer` value constructed anywhere", citing `grep -rn Normalizer Codec/` — **the path excluded `Bench.lean:61`**, which constructs one                             | both halves stated; "a claim scoped by a path is only as good as the path" |
| F-2  | "length-preserving **at any instantiation**" — a `List UInt8` normalizer that shortens typechecks fine                                                                               | softened to the `Bytes n` instantiation                                    |
| F-3  | `26.97–28.56` splices two lanes from two sessions                                                                                                                                    | — (see note below)                                                         |
| F-4  | "review M-1" cited with no in-repo artifact behind it                                                                                                                                | **this file**                                                              |
| F-5  | `[D4]`'s "bijection … not claimed" **under**claims: the four-law set exists                                                                                                          | corrected                                                                  |
| F-6  | `[S3]`'s `takeWhile` law count omitted two of six                                                                                                                                    | corrected                                                                  |
| F-7  | `Codec/Normal.lean:97` still carried the refuted `norm : Bytes n → Bytes n` — a third site                                                                                           | corrected                                                                  |
| F-8  | README never mentions `Codec.alt_not_functional`, a law this round added                                                                                                             | added                                                                      |
| F-9  | "it is `rfl`" printed beside a `[propext, Quot.sound]` footprint                                                                                                                     | corrected                                                                  |
| F-10 | `relTakeWhile`'s explicit `n` lifted into `[D4]` without noting the decoders' `n` is implicit                                                                                        | corrected                                                                  |
| F-11 | an incident parenthetical cites the round, not the pass                                                                                                                              | corrected                                                                  |
| F-12 | `checks.bench` also built in a read-only `${self}`, and `runCommand`'s body does not run under `set -e`, so a failing `grep` exited 0                                                | `cp` to a writable tree + `set -euo pipefail`; mutation-tested             |
| F-13 | `footprintClassifications` — the new "one table" — was validated by **key only**, so a right-key/wrong-class remap was green; on the `.choice` row no tree inhabitant could catch it | semantics-written probes in both directions; mutation-tested               |

## Note on F-3 (not closed, and deliberately)

`26.97–28.56` is quoted as "across all three decode tables" and does splice two lanes
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
