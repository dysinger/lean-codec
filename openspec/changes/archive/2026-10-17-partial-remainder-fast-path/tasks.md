# Tasks

> The plan: wire the shipped `byteSlice` Layer-2 trust seam onto a
> **partial-remainder commit** — a `USize`-indexed `commitRemainder a c := byteSlice
(ByteArray.mk a) c` — with a definitional refinement law `commitRemainder_spec`, a documented
> `decodeArrayFast := decodeArray` re-exposure, and a byte-for-byte bench lane. The `ByteSlice`/C
> trust is a runtime contract (invisible to Lean), **not** a proof step. No new carrier; no change
> to `decode`/`encode`'s `Bytes n` return type; no new equality to `decode d`. Every numeric figure
> `[measured]`, never hand-typed.

> **Status (this session): planned and independently reviewed.** The four artifacts (proposal,
> spec deltas, design, tasks) are authored and `openspec validate` passes (change valid; `--all`
> 6 passed / 0 failed). A skeptical review of the first draft found three Criticals and a citation
> error, all fixed in a from-scratch rewrite: (1) the two "no second carrier" requirements are now
> explicitly **MODIFIED** (relaxed, with existing scenarios carried over), not dodged; (2)
> `commitRemainder` is `USize`-indexed so its spec is `rfl` — no `Nat ↔ USize` roundtrip, no
> `System.Platform.numBits` premise; (3) the law is honestly framed as definitional, with the
> refinement to `decode d` being the pre-existing `decodeArray_eq`, not new work; and the F\*
> citation is corrected (F\* threads a cursor, no commit-time `memcpy`). Implementation starts here.

## 1. The commit and the re-exposure (definitions)

- [x] 1.1 Add `commitRemainder (a : Array UInt8) (c : USize) : ByteArray := byteSlice
(ByteArray.mk a) c` in `Codec/ByteSlice.lean` — the single `memcpy` commit, `USize`-indexed
      (matching `byteSlice`'s index, so no `Nat ↔ USize` roundtrip and no `System.Platform.numBits`
      premise). Document it as the first library consumer of the trust seam, still excluded from the
      `#print axioms` gate.
- [x] 1.2 Add `decodeArrayFast {α} (d : Codec α) (a : Array UInt8) (i : Nat) : List (α × Nat) :=
decodeArray d a i` in `Codec/Packed.lean` — a documented rename (not a re-implementation)
      stating the "decode yields `Nat` cursors, no materialization during decode" contract, and that
      the `Nat` cursor is a fixed binding decision (task 3.1).

## 2. The refinement law

- [x] 2.1 Prove `commitRemainder_spec (a : Array UInt8) (c : USize) : commitRemainder a c =
ByteArray.mk (a.extract c.toNat a.size)` by `rfl` (definitional: unfold `byteSlice`'s body;
      `(ByteArray.mk a).data = a` and the `.size` coincidence are `rfl`). Confirm `#print axioms
Codec.commitRemainder_spec` ⇒ `[propext, Quot.sound]` (no `byteSlice` axiom — the C trust is
      runtime-only and invisible to Lean).
- [x] 2.2 Record (no new proof) that the refinement to `decode d` remains the existing
      `decodeArray_eq`: `decodeArrayFast := decodeArray`, and the commit composes at the call site via
      the caller's `Nat → USize` conversion. Add no theorem equating anything to `decode d`.

## 3. Bench

- [x] 3.1 Add `benchCommitRemainder n` committing a **mid-buffer** `USize` cursor `c = (n / 3).toUSize`,
      value-checking the committed `ByteArray` byte-for-byte against
      `ByteArray.mk (src.extract c.toNat src.size)` (never a length check), reporting ns/op + MiB/s as
      a distinct Layer-2 lane against the calibrated `memcpy` baseline. Wire it into `main`'s size
      sweep.

## 4. Gate

- [x] 4.1 `lake build` zero `sorry`/warnings; `#print axioms Codec.roundtrip` ⇒ `[propext,
Quot.sound]`; `#print axioms Codec.commitRemainder_spec` ⇒ `[propext, Quot.sound]` (definitional).
- [x] 4.2 Run the bench, record the `commitRemainder` lane's `[measured]` figures, and confirm the
      partial value check passes byte-for-byte. Update `README.md` §Performance and `AGENTS.md` to
      state the partial-remainder surface honestly (Layer 1 proven, Layer 2 the `byteSlice` commit,
      never conflated), preserving the `[D#]`/`[S#]` anchors and the two-layer framing.
