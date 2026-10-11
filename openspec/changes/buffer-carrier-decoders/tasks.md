# Tasks

## 1. The indexed array-carrier decoder (run-model)

- [ ] 1.1 Add `decodeArray {α} (d : Codec α) (a : Array UInt8) (i : Nat) : List (α × Nat)`
  in `Codec/DecodeArray.lean`, the *same* structural recursion as `decode` but reading
  `a[i]` (via `a.getD i 0` or `a[i]'h`) and returning a `Nat` remainder index instead of a
  `Bytes` remainder. Verify: `lake build` clean (zero sorries/warnings) and
  `#eval decodeArray Codec.byte #[1,2,3] 0` ⇒ `[(1, 1)]` after a single `byte` peel.
- [ ] 1.2 Prove `decodeArray_eq` — the F\*-style refinement against the list spec, in the
  membership/remainder form:
  `(x, j) ∈ decodeArray d a i ↔ (x, a.data.drop j) ∈ decode d (a.data.drop i)` (or the
  equivalent function-level `decodeArray d a i = (decode d (a.data.drop i)).map …`),
  by induction on `d` using `Array`/`List` lemmas (`Array.getElem?_eq_data_get?`,
  `List.drop`, `List.map_*`) only — no solver. Verify: `#print axioms Codec.decodeArray_eq` ⇒
  `[propext, Quot.sound]`.

## 2. The array-accumulating encoder (run-model)

- [ ] 2.1 Add `encodeArray {α} (d : Codec α) (x : α) : Option (Array UInt8)` in
  `Codec/EncodeArray.lean` (or alongside `decodeArray`), the same structural recursion as
  `encode` but materializing the `Array` result (list-accumulate internally, fold once at the
  end). Verify: `lake build` clean and `#eval encodeArray Codec.byte (1 : UInt8)` ⇒
  `some #[1]`.
- [ ] 2.2 Prove `encodeArray_eq` — `encodeArray d x = some a ↔ encode d x = some a.data`
  (or the `Option.map (·.data)` form), by induction on `d` using `List.append`↔`Array`
  lemmas (`List.toArray_append`, `Array.data_toArray`, …). Verify:
  `#print axioms Codec.encodeArray_eq` ⇒ `[propext, Quot.sound]`.

## 3. Transfer the existing laws (no new semantics)

- [ ] 3.1 Add to `Codec/Sound.lean`: `decodeArray_spec`, `encodeArray_rel`,
  `roundtripArray` — each a one-line rewrite through `decodeArray_eq`/`encodeArray_eq` into
  the existing `decode_spec`/`encode_rel`/`roundtrip`. Verify: `lake build` clean; `#print axioms` of each ⇒ `[propext, Quot.sound]` (no new induction).
- [ ] 3.2 Confirm no existing theorem statement changed and `lake build` (the proof gate)
  reports zero sorries/warnings. Verify: `grep -rn "sorry\|admit\|axiom " Codec/` empty.

## 4. The full-consumption array repetition decoder (Tier-B analogue)

- [ ] 4.1 Add `decodeFullArray {α} (p : Codec α) (h : ConsumesByte p) (a : Array UInt8) (i : Nat) : Option (List α × Nat)` in `Codec/DecodeArray.lean`, the carrier-swapped
  analogue of `decodeFull` — well-founded on the *remaining length* `a.size - i`, same
  `ConsumesByte` guard, single `Option` thread (no all-prefix list). Verify: `lake build`
  clean; `#eval decodeFullArray Codec.byte byte_consumesByte #[1,2,3] 0` ⇒ `some ([1,2,3], 3)`.
- [ ] 4.2 Prove `decodeFullArray_spec` — under the full-consumption-uniqueness hypothesis
  (`huniq`, the same `decodeFull`-level mirror of `relUnambiguous`), `decodeFullArray p h a i = some (xs, j) ↔` the array decode fully consumes `a` to `xs`. Verify:
  `#print axioms Codec.decodeFullArray_spec` ⇒ `[propext, Quot.sound]`.

## 5. Benchmark leg + record the carrier speedup

- [ ] 5.1 Extend `Bench.lean` with `decodeArray`/`encodeArray`/`decodeFullArray` timing legs
  (reusing `timeBatch`), run `nix build '.#bench'`, and record the numbers against the §10.5
  list-carrier baseline (`decode byte` ~30–100 ns/op; `decodeFull byte [16384]` = 545 µs).
  Verify: a correctness assertion (values recovered byte-exactly) holds and the array-carrier
  leg is measurably faster than the list-carrier leg (order: the ~5–20× carrier win).
- [ ] 5.2 Update the `AGENTS.md` handoff and the `invertible-binary-core/tasks.md` ledger with
  the measured carrier speedup, and note the FFI/compiler tier remains a separate, deferred change.

## 6. Integration gate

- [ ] 6.1 `nix build '.#checks.<system>.lean'` and `nix build '.#bench'` both green; `nix fmt`
  leaves no staged-file reformat. Verify: `native`/`bench`/`check` derivations build; working
  tree clean.
