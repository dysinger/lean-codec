# Tasks

## 1. Axiom gate (root cause — do this first)

- [x] 1.1 Add `Axioms.lean` as a `@[default_target]` `lean_lib` in
      `lakefile.lean`, mirroring `../lean-basen/Axioms.lean`: a `#guard_msgs` (or
      `#print axioms` + guard equivalent) block covering every public theorem, so
      `lake build` fails on a footprint outside `[propext, Quot.sound]`
- [x] 1.2 Enumerate the theorem set programmatically rather than hand-listing it, so
      a newly added theorem is gated by default and cannot be silently omitted;
      record the enumeration mechanism in `Axioms.lean`'s module docstring
- [x] 1.3 Record the single current exclusion — `findByte_spec` with its measured
      `[propext, Classical.choice, Quot.sound]` — **by name, with a reason**, so the
      gate's first green run documents today's true state (this exclusion is removed
      by §2.2)
- [x] 1.4 Verify the gate is load-bearing: perturb one theorem's footprint (swap a
      cited definition for one reaching classical logic) and confirm `lake build`
      fails naming the declaration; restore
- [x] 1.5 Confirm `lake build` still exits 0 on the unmodified tree and that the gate
      adds no new warnings (`-DwarningAsError` still applies to it)

## 2. `findByte` axiom leak (P0)

- [x] 2.1 Reimplement `Codec.findByte` (`Codec/ByteSlice.lean`) constructively —
      explicit `Nat`/`USize` recursion over the array instead of
      `Array.findIdx?` — so no `Decidable` instance with a classical route is
      consulted. `Codec/ByteSlice.c` is unchanged: the C contract is still
      `memchr`-shaped, and this is a Lean-body change only
- [x] 2.2 Remove the §1.3 exclusion once `findByte_spec` measures
      `[propext, Quot.sound]` (or `[propext]`, matching its siblings)
- [x] 2.3 Update `findByte_spec`'s docstring to the **measured** footprint, and keep
      the honest limit: `#print axioms` sees the Lean body, never the C
- [x] 2.4 Update `README.md`'s Performance-section sentence that repeats the wrong
      `[propext]` claim, so prose and measurement agree
- [x] 2.5 Verify the emitted IR still calls the C symbol rather than the Lean body
      (`.lake/build/ir/Codec/ByteSlice.c`), so the seam was not silently unwired
- [x] 2.6 If 2.1 turns out to cost an unreasonable proof, fall back to design D2(A):
      keep `findIdx?`, state the exclusion with its measured footprint, and describe
      it as **excluded**, never clean. Record which branch was taken

## 3. Docstrings that assert what is not true

- [x] 3.1 `Codec/Sound.lean:910` cites `relUnambiguous_of_relAligned` as proved; it
      does not exist. Write the lemma if it is true; if it is **false**, prove the
      refutation and correct the docstring (design D4). Never leave the citation
      dangling either way
- [x] 3.2 `Codec/DecodeOne.lean` header promises the committed decoder "equals the
      unique result" — unproved, and the two ingredient lemmas take each other's
      conclusions as hypotheses. State and prove the composition under
      `Functional d ∧ Unambiguous d`; at minimum prove the `Codec.byte` instance
      (design D3's `decodeOne_byte_eq`, ~6 lines) and a general gated form where
      reachable
- [x] 3.3 If the general composition in 3.2 is not reachable, correct the module
      header to claim only what is proved (soundness + the two halves) and record the
      general form as open. Do not keep advertising an unproved theorem
- [x] 3.4 `Codec/DecodeOne.lean:168` presents `decodeArray_functional_byte` as a
      `decodeArray`-level `Functional` instance; it is the mirror shape (fixed length
      index, variable values). Restate the docstring, or add the genuine instance
- [x] 3.5 Re-grep every docstring that says "proved as `X`" / "see `X`" and confirm
      each named declaration resolves — the audit found three in this family, and the
      cheap check is one pass over the tree

## 4. Coverage gaps

- [x] 4.1 Add `emptyConsumesByte` — `empty` is the only `Codec` constructor without a
      `ConsumesByte` witness, so a downstream `d | empty` codec still hand-proves
      productivity at that node, contradicting `Sound.lean:126-147`'s claim that
      `seqConsumesByte`/`isoConsumesByte` closed this
- [x] 4.2 Add a concrete `MeasureDecreases` supplier (a two-state counter codec; the
      audit's reviewer did this in ~20 lines at `[propext, Quot.sound]`).
      `MeasureDecreases` is the only hypothesis family with zero suppliers while
      being satisfiable, and the repo's own standard (`Sound.lean:733-742`) says such
      a family gets a witness
- [x] 4.3 Confirm both new witnesses are `[propext, Quot.sound]`-only and that the
      gate from §1 covers them automatically

## 5. `README.md` corrections (every claim below was falsified against the code)

- [x] 5.1 `[S3]`: add the shipped `takeWhile` triple
      (`relTakeWhile`/`decodeTakeWhile`/`encodeTakeWhile`,
      `Codec/Combinators.lean:774-810`) to the inventory of what core ships, noting
      it is `UInt8`-specialised and that no named format is defined in core
- [x] 5.2 `[S4]`: correct the dual's types to the code —
      `foldl : Iso (α × β) α → Iso (α × List β) α`,
      `foldr : Iso (β × α) α → Iso (α × List β) α`. The README's `Iso ([α], β) β` is
      not the code, so the stated reason for type-incoherence must be restated in
      terms of the step's argument order
- [x] 5.3 `packedCands`: two tables give `k=1` as both 86 ns and 75 ns (and `k=2` as
      106 and 95) for the same lane. Keep one, or label each with its run conditions;
      recompute the stated per-candidate delta from the surviving figures
- [x] 5.4 `[D4]` lay-terms paragraph: it reinstates the "`unapply` cannot choose"
      diagnosis that the `[D4]` block above it explicitly disavows. Correct it to the
      `↔`-quantified-over-every-`a` form
- [x] 5.5 `[D7]`: `chainl1` needs four things, not three — `MeasureDecreases` is a
      separate argument from `Iso.foldl`
- [x] 5.6 Scope: replace the stale `lean-binary` with `lean-basen`
- [x] 5.7 Re-read the whole README against the audit's list and confirm no other
      contradicting figures remain — the README's own rule is that an internal
      inconsistency between two numbers is a legitimate defect

## 6. Gates

- [ ] 6.1 `nix develop --command lake build` — zero `sorry`, zero warnings, gate green
- [ ] 6.2 `nix develop --command lake build bench` — bench still compiles and links
- [ ] 6.3 `nix develop --command openspec validate --all`
- [ ] 6.4 `nix flake check` (detached with `nohup`, never foregrounded)
- [ ] 6.5 Commit per task family (gate / findByte / docstrings / coverage / README),
      individual files only, printing `git diff --cached --name-only` before each
