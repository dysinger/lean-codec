# Tasks

## 1. Shared lift

- [ ] 1.1 Add `BaseN/Lift.lean` (or `BaseN/Core.lean`) with `liftEncode`/`liftDecode`
      and the one `Nat↔UInt8<256` bridge lemma (`toByte n …`, `.toNat` transparency
      for `n < 256`), proved `[propext, Quot.sound]`-only.

## 2. Re-express the simple bases via the lift

- [ ] 2.1 `BaseN/Base2` — supply `Nat` digit codec + bijection; inherit `UInt8`
      `encode`/`decode`/`roundtrip` from the lift; delete its bespoke `UInt8` lift
      and `toByte_valTo*`.
- [ ] 2.2 `BaseN/Base4` — same.
- [ ] 2.3 `BaseN/Base8` — same (keep the `> 255` overflow rejection in `decodeN`).
- [ ] 2.4 `BaseN/Base10` — same (keep overflow rejection).
- [ ] 2.5 `BaseN/Base16` — same (keep case-insensitive decode).

## 3. Re-express the block bases via the lift (preserve 5.1)

- [ ] 3.1 `BaseN/Base32` — share the `UInt8` lift/bridge; keep its `Nat`-level block
      `decodeN` + the terminal-padding (`rest = []`) guards from 5.1.
- [ ] 3.2 `BaseN/Base64` — same; keep the in-progress `rest = []` guards (finish the
      5.1 fix across `decodeN`/`decodeN_cons*`/`decode`).

## 4. Facade + bench + gate

- [ ] 4.1 Update `BaseN.lean` facade imports if names move; ensure all seven bases
      still re-export `encode`/`decode`/`roundtrip`.
- [ ] 4.2 `Bench.lean` byte-exact vectors still `rfl`; no import churn.
- [ ] 4.3 `lake build` zero `sorry`/warnings; `#print axioms BaseN.roundtrip` and each
      `BaseN.Base{X}.roundtrip` = `[propext, Quot.sound]`; `nix flake check` green;
      commit + push.

## Out of scope (recorded so it cannot drift)

- No `Codec/` change; no `satisfy`/`sum`; no BE/LE; no fixed-width; no `varint`.
