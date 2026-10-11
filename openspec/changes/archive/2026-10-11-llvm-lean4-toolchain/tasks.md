# Tasks

## 1. Toolchain override (the LLVM-enabled lean4)

- [x] 1.1 Add the LLVM-enabled `lean4` override: `llvmPackages_19.llvm` in
      `buildInputs` and `lib.cmakeBool "LLVM" true` in `cmakeFlags`. Verify
      `nix build '.#checks.<system>.lean'` builds the overridden toolchain and
      `nix develop -c lean --features` reports LLVM (not `[]`).
- [x] 1.2 Wire the override into every path: `default.nix`'s `lean4` argument and
      `flake.nix`'s `devShells.default.packages`. Verify the dev shell's `lean` and the
      `native`/`check`/`bench` derivations all resolve to the same LLVM-backed store
      path (`readlink -f $(nix develop -c which lean)`).

## 2. Link fix + proof gate

- [x] 2.1 Fix the `libc++` link gap so `lake build bench` (C backend) links against
      the C++ runtime. Verify `lake build bench` completes and `#eval` of an
      `Array.push`/`Array.get!`/`Array.size` micro-exercises O(1) (use a `Bench.lean`
      leg or a scratch `lake env lean` `#eval` that times a 1 MiB `Array.size` — it
      should drop to ~O(1), not the O(n) `List.length` observed this session).
- [x] 2.2 Confirm the proof gate is still clean. Verify `nix build
'.#checks.<system>.lean'` green with zero `sorry`/warnings and the axiom record
      unchanged (`#print axioms Codec.decodeArray_eq` ⇒ `[propext, Quot.sound]`).

## 3. Re-measure the carrier win

- [x] 3.1 Run `./result/bin/bench` on a 1 MiB / 16384 synthetic input and record
      `decodeArray`/`encodeArray`/`decodeFullArray` against the §10.5/Tier-A baselines.
      Verify `decodeArray byte` is O(1) indexed access (the ~16.8 µs `Array.size` walk
      measured this session should drop to ~100 ns), confirming the buffer+cursor
      run-model is now genuinely fast in the extracted C.
- [x] 3.2 Update `AGENTS.md` handoff and `invertible-binary-core/tasks.md` ledger with
      the new numbers and the resolved "toolchain was the blocker, not the algorithm"
      finding; note the FFI/compiler tier remains deferred. Verify the docs are
      consistent with the measured figures.

## 4. Integration gate

- [x] 4.1 `nix build '.#checks.<system>.lean'` and `nix build '.#bench'` both green;
      `nix fmt` leaves no staged-file reformat. Verify `lake build` (the proof gate)
      clean, working tree staged per the repo's per-file commit convention.
