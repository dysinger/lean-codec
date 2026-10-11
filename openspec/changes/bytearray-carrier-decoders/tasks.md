# Tasks

## 1. ByteArray carrier (the packed run-model)

- [ ] 1.1 Add `Codec/DecodeByteArray.lean` defining `decodeByteArray {α} (d : Codec α)
    (a : ByteArray) (i : Nat) : List (α × Nat)` — the same structural recursion as
      `decode`, reading `a[i]` (the `O(1)` `lean_byte_array_get`) in the `byte` case
      instead of cons-peeling — plus `Codec/EncodeByteArray.lean` (or one combined
      module) defining `encodeByteArray {α} (d : Codec α) (x : α) : Option ByteArray`
      via `ByteArray` extension/accumulation instead of `List` append. Verify
      `lake build` compiles with zero `sorry`/warnings.
- [ ] 1.2 Prove the carrier refinement laws in the **function-level** form (lesson 2):
      `decodeByteArray_eq : decodeByteArray d a i = (decode d (a.data.toList.drop i)).map
    (fun (x,r) => (x, i + (a.data.toList.drop i).length - r.length))` and the
      analogous `encodeByteArray_eq`, routed through the reducible `ByteArray.data`
      (never the opaque `ByteArray.toList`). Verify `#print axioms
    Codec.decodeByteArray_eq` ⇒ `[propext, Quot.sound]`.
- [ ] 1.3 Add the three transfer laws to `Codec/Sound.lean` (`decodeByteArray_spec`,
      `encodeByteArray_rel`, `roundtripByteArray`), stated so each `Bytes`-level law
      transfers by rewriting via `decodeByteArray_eq`/`encodeByteArray_eq`. Verify the
      proof gate `nix build '.#checks.<system>.lean'` stays green and the axiom record
      stays `[propext, Quot.sound]`.

## 2. Varbinary (the motivating hot path)

- [ ] 2.1 Port the F\* LEB128 varint as the `Bytes`-level spec: `varint : Iso Nat Bytes`
      in a new module (e.g. `Codec/VarBinary.lean`), `apply` = `varint_encode_go`
      (7 data bits/byte, `% 128` pieces, continuation high bit), `unapply` =
      `varint_decode_go`, with `varint.law` proved once (the LEB128 roundtrip). Verify
      `#print axioms Iso.varint.law` (or equivalent) ⇒ `[propext, Quot.sound]`.
- [ ] 2.2 Add the `ByteArray`-carrier varbinary run-model: `decodeVarint : ByteArray →
    Nat → List (Nat × Nat)` and `encodeVarint : Nat → ByteArray`, the same reads/
      writes over `a[i + k]`/`ByteArray.push`, and prove `decodeVarint_eq`/
      `encodeVarint_eq` tie them to `varint` through the §1 carrier equality. Verify
      `lake build` clean and the roundtrip (`decodeVarint (encodeVarint n) 0` yields
      the original `n`) in a scratch `#eval`.
- [ ] 2.3 Add `Bench.lean` legs measuring `decodeByteArray byte` / `decodeVarint` /
      `encodeVarint` against the `List` (`decode byte`) and `Array UInt8`
      (`decodeArray byte`) baselines; `nix build '.#bench'` and run on a 1 MiB / 16384
      synthetic input. Verify the `ByteArray` carrier is genuinely O(1)-indexed in the
      extracted C and record the before/after figures.

## 3. Documentation + integration gate

- [ ] 3.1 Update `AGENTS.md` handoff and `invertible-binary-core/tasks.md` ledger with
      the measured figures and the "`ByteArray` is the densest stdlib carrier; the
      toolchain was the blocker, now the carrier is the last lever" finding; note the
      author-FFI/compiler tier remains deferred. Verify the docs are consistent with
      the measured numbers and keep the `[D#]`/`[S#]` anchor table unchanged (no new
      departure/strengthening).
- [ ] 3.2 `nix build '.#checks.<system>.lean'` and `nix build '.#bench'` both green;
      `nix fmt` leaves no staged-file reformat; `lake build` (the proof gate) clean;
      working tree staged per the repo's per-file commit convention.
