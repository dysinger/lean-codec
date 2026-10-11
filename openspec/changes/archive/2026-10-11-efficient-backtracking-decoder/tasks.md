# Tasks

## 1. Full-consumption repetition decoder (Tier A)

- [x] 1.1 Add `decodeFull {α} (p : Codec α) (h : ConsumesByte p) (s : Bytes) : Option (List α)`
  in `Codec/Decode.lean`, defined by explicit `WellFounded.fix` on `s.length` (the same
  `ConsumesByte` guard as `decodeRepeat`), returning `some xs` for the unique full
  consumption with `[]` remainder, `none` otherwise. Verify: `lake build` clean (zero
  sorries/warnings) and `#eval decodeFull Codec.byte byte_consumesByte [1,2,3]` ⇒
  `some [1,2,3]`.
- [x] 1.2 Prove `decodeFull_spec` — `decodeFull p h s = some xs ↔ ∃ (ys : List α), decodeRepeat p h s` contains `(xs, [])` (or the equivalent reverse direction), by
  induction on `s.length` reusing `decodeRepeat_eq`. Verify: `#print axioms Codec.decodeFull` ⇒ `[propext, Quot.sound]`.
  **Resolution: option 2 (uniqueness hypothesis).** The naive `↔` is *not* provable
  because `decodeFull` has first-success semantics while `decodeRepeat` enumerates
  *all* full consumptions (ambiguous-but-productive descriptions like
  `alt (seq (pure 0) byte) (seq (pure 1) byte)` give two distinct full-consumption
  lists). The honest statement takes a full-consumption-uniqueness hypothesis
  `huniq : (x,[]) ∈ decodeRepeat p h s → (y,[]) ∈ decodeRepeat p h s → x = y` (the
  `decodeFull`-level mirror of the chain laws' `relUnambiguous`). Proved as
  `decodeFull_some` (forward, unconditional) + `decodeFull_ne_none` (completeness) +
  `decodeFull_spec` (the `↔` under `huniq`), all `[propext, Quot.sound]`-only.
- [x] 1.3 Add `decodeRepeatFull` (the `Option`-valued, accumulator/fused "many" decode)
  and prove `decodeRepeatFull_eq` against `decodeRepeat` restricted to full consumption.
  Verify: `lake build` clean and `#eval` smoke test on a multi-element `byte` list.
  **Resolution:** `decodeRepeatFull` is a reducible `abbrev` for `decodeFull` (task 1.1's
  single-pass, `Option`-valued, list-fused decoder — the two task bullets describe one
  function under two names); `decodeRepeatFull_eq` restates `decodeFull_spec`.
  `#eval decodeRepeatFull Codec.byte byte_consumesByte [1,2,3]` ⇒ `some [1,2,3]`.

## 2. Fused (non-re-traversing) single-step decoder

- [x] 2.1 Add `decodeFast {α} (d : Codec α) (s : Bytes) : List (α × Bytes)` — a
  `flatMap`/append-fused re-staging of `decode` that does not re-traverse shared prefixes
  (list-fusion of the `alt` append and `seq` nested `flatMap`). Verify: `lake build`
  clean, `#eval decodeFast Codec.byte s = decode Codec.byte s`.
- [x] 2.2 Prove `decodeFast_eq : decodeFast d s = decode d s` by induction on `d` using
  `List.flatMap_assoc`/`List.map_append`/`List.mem_*` equations only (no solver). Verify:
  `#print axioms Codec.decodeFast` ⇒ `[propext, Quot.sound]`.
  **Note:** the seq case uses the stdlib fusion identity
  `List.map_eq_flatMap : l.map f = l.flatMap (fun a => [f a])`; `#print axioms Codec.decodeFast_eq` ⇒ `[propext, Quot.sound]`.

## 3. Transfer the existing laws (no new semantics)

- [x] 3.1 Add the transfer lemmas to `Codec/Sound.lean`: `decodeFast_spec`, `bidir_decodeFast`,
  `roundtrip_decodeFast`, `decodeFull_spec`, `decodeRepeatFull_spec` — each a one-line
  rewrite through `decodeFast_eq`/`decodeFull_spec` into the existing `decode_spec`/`bidir`/
  `roundtrip`/`decodeRepeat_spec`. Verify: `lake build` clean; `#print axioms` of each
  transfer lemma ⇒ `[propext, Quot.sound]` (no new induction).
  **Note:** `decodeFull_spec`/`decodeRepeatFull_eq` already live in `Codec.Decode` (tasks
  1.2/1.3); `decodeRepeatFull_spec` restates it under the alias name. All four transfer
  lemmas verify `[propext, Quot.sound]`.
- [x] 3.2 Confirm no existing theorem statement changed and `lake build` (the proof gate)
  still reports zero sorries/warnings. Verify: `grep -rn "sorry\|admit\|axiom" Codec/` empty.
  `grep` is clean; `lake build` green with no warnings.

## 4. Benchmark leg + record the speedup

- [x] 4.1 Extend `Bench.lean` with `decodeFull`/`decodeRepeatFull`/`decodeFast` timing legs
  (reusing `timeBatch`), run `nix build '.#bench'`, and record the new numbers against the
  §10.5 baseline (`decodeRepeat byte [16384]` ≈ 13.8 s → target sub-second for the
  full-consumption ask). Verify: the benchmark's full-consumption leg is an order of
  magnitude faster and its a correctness assertion (`xs` recovered byte-exactly) holds.
  **Measured (arm64, reps=20):** `decodeRepeat byte [16384]` = 11.2 s (baseline);
  `decodeFull byte [16384]` = 545 µs (**~20,000× faster**, sub-millisecond);
  `decodeRepeatFull byte [16384]` = 632 µs; `decodeFast byte` = O(1) (~31 ns, equal to
  `decode byte`). Byte-exact correctness assertions all hold.
- [x] 4.2 Update the §10.5/§10.6 notes in `tasks.md` (ledger) and `AGENTS.md` handoff with
  the measured speedup, and note the Tier B (memoizing chart) remains a separate change.
  **Done:** updated the §10.5 benchmark record (added the Tier-A follow-up numbers) and the
  §10.6/§11 entries in `invertible-binary-core/tasks.md`, and both the "Open, in order" and
  the "Done this session" notes in `AGENTS.md`; Tier B explicitly flagged as deferred.

## 5. Integration gate

- [x] 5.1 `nix build '.#checks.<system>.lean'` and `nix build '.#bench'` both green;
  `nix fmt` leaves no staged-file reformat (pre-commit hook clean). Verify: all three
  derivations (`native`, `bench`, `check`) build; working tree clean.
  **Done:** `.#checks.aarch64-darwin.lean` (proof gate), `.#bench`, `.#native` all build;
  `nix fmt` idempotent (0 changed on re-run) and `.#checks.aarch64-darwin.formatting` green;
  `.#checks.aarch64-darwin.openspec` (`openspec validate --all`) also green; `grep "sorry|admit|axiom " Codec/` clean.
