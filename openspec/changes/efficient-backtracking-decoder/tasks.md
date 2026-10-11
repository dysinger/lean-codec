# Tasks

## 1. Full-consumption repetition decoder (Tier A)

- [ ] 1.1 Add `decodeFull {α} (p : Codec α) (h : ConsumesByte p) (s : Bytes) : Option (List α)`
  in `Codec/Decode.lean`, defined by explicit `WellFounded.fix` on `s.length` (the same
  `ConsumesByte` guard as `decodeRepeat`), returning `some xs` for the unique full
  consumption with `[]` remainder, `none` otherwise. Verify: `lake build` clean (zero
  sorries/warnings) and `#eval decodeFull Codec.byte byte_consumesByte [1,2,3]` ⇒
  `some [1,2,3]`.
- [ ] 1.2 Prove `decodeFull_spec` — `decodeFull p h s = some xs ↔ ∃ (ys : List α), decodeRepeat p h s` contains `(xs, [])` (or the equivalent reverse direction), by
  induction on `s.length` reusing `decodeRepeat_eq`. Verify: `#print axioms Codec.decodeFull` ⇒ `[propext, Quot.sound]`.
- [ ] 1.3 Add `decodeRepeatFull` (the `Option`-valued, accumulator/fused "many" decode)
  and prove `decodeRepeatFull_eq` against `decodeRepeat` restricted to full consumption.
  Verify: `lake build` clean and `#eval` smoke test on a multi-element `byte` list.

## 2. Fused (non-re-traversing) single-step decoder

- [ ] 2.1 Add `decodeFast {α} (d : Codec α) (s : Bytes) : List (α × Bytes)` — a
  `flatMap`/append-fused re-staging of `decode` that does not re-traverse shared prefixes
  (list-fusion of the `alt` append and `seq` nested `flatMap`). Verify: `lake build`
  clean, `#eval decodeFast Codec.byte s = decode Codec.byte s`.
- [ ] 2.2 Prove `decodeFast_eq : decodeFast d s = decode d s` by induction on `d` using
  `List.flatMap_assoc`/`List.map_append`/`List.mem_*` equations only (no solver). Verify:
  `#print axioms Codec.decodeFast` ⇒ `[propext, Quot.sound]`.

## 3. Transfer the existing laws (no new semantics)

- [ ] 3.1 Add the transfer lemmas to `Codec/Sound.lean`: `decodeFast_spec`, `bidir_decodeFast`,
  `roundtrip_decodeFast`, `decodeFull_spec`, `decodeRepeatFull_spec` — each a one-line
  rewrite through `decodeFast_eq`/`decodeFull_spec` into the existing `decode_spec`/`bidir`/
  `roundtrip`/`decodeRepeat_spec`. Verify: `lake build` clean; `#print axioms` of each
  transfer lemma ⇒ `[propext, Quot.sound]` (no new induction).
- [ ] 3.2 Confirm no existing theorem statement changed and `lake build` (the proof gate)
  still reports zero sorries/warnings. Verify: `grep -rn "sorry\|admit\|axiom" Codec/` empty.

## 4. Benchmark leg + record the speedup

- [ ] 4.1 Extend `Bench.lean` with `decodeFull`/`decodeRepeatFull`/`decodeFast` timing legs
  (reusing `timeBatch`), run `nix build '.#bench'`, and record the new numbers against the
  §10.5 baseline (`decodeRepeat byte [16384]` ≈ 13.8 s → target sub-second for the
  full-consumption ask). Verify: the benchmark's full-consumption leg is an order of
  magnitude faster and its a correctness assertion (`xs` recovered byte-exactly) holds.
- [ ] 4.2 Update the §10.5/§10.6 notes in `tasks.md` (ledger) and `AGENTS.md` handoff with
  the measured speedup, and note the Tier B (memoizing chart) remains a separate change.

## 5. Integration gate

- [ ] 5.1 `nix build '.#checks.<system>.lean'` and `nix build '.#bench'` both green;
  `nix fmt` leaves no staged-file reformat (pre-commit hook clean). Verify: all three
  derivations (`native`, `bench`, `check`) build; working tree clean.
