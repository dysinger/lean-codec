# Tasks

## 1. ByteArray carrier (the packed run-model)

- [x] 1.1 Add `Codec/DecodeByteArray.lean` defining `decodeByteArray {α} (d : Codec α)
(a : ByteArray) (i : Nat) : List (α × Nat)` — the same structural recursion as
      `decode`, reading `a[i]` (the `O(1)` `lean_byte_array_get`) in the `byte` case
      instead of cons-peeling — plus `Codec/EncodeByteArray.lean` (or one combined
      module) defining `encodeByteArray {α} (d : Codec α) (x : α) : Option ByteArray`
      via `ByteArray` extension/accumulation instead of `List` append. Verify
      `lake build` compiles with zero `sorry`/warnings.
- [x] 1.2 Prove the carrier refinement laws in the **function-level** form (lesson 2):
      `decodeByteArray_eq : decodeByteArray d a i = (decode d (a.data.toList.drop i)).map
(fun (x,r) => (x, i + (a.data.toList.drop i).length - r.length))` and the
      analogous `encodeByteArray_eq`, routed through the reducible `ByteArray.data`
      (never the opaque `ByteArray.toList`). Verify `#print axioms
Codec.decodeByteArray_eq` ⇒ `[propext, Quot.sound]`.
- [x] 1.3 Add the three transfer laws to `Codec/Sound.lean` (`decodeByteArray_spec`,
      `encodeByteArray_rel`, `roundtripByteArray`), stated so each `Bytes`-level law
      transfers by rewriting via `decodeByteArray_eq`/`encodeByteArray_eq`. Verify the
      proof gate `nix build '.#checks.<system>.lean'` stays green and the axiom record
      stays `[propext, Quot.sound]`.

## 2. Varbinary (the motivating hot path)

- [x] 2.1 Port the F\* LEB128 varint as the `Bytes`-level spec: `varint : Iso Nat Bytes`
      in a new module (e.g. `Codec/VarBinary.lean`), `apply` = `varint_encode_go`
      (7 data bits/byte, `% 128` pieces, continuation high bit), `unapply` =
      `varint_decode_go`, with `varint.law` proved once (the LEB128 roundtrip). Verify
      `#print axioms Iso.varint.law` (or equivalent) ⇒ `[propext, Quot.sound]`.
- [x] 2.2 Add the `ByteArray`-carrier varbinary run-model: `decodeVarint : ByteArray →
Nat → List (Nat × Nat)` and `encodeVarint : Nat → ByteArray`, the same reads/
      writes over `a[i + k]`/`ByteArray.push`, and prove `decodeVarint_eq`/
      `encodeVarint_eq` tie them to `varint` through the §1 carrier equality. Verify
      `lake build` clean and the roundtrip (`decodeVarint (encodeVarint n) 0` yields
      the original `n`) in a scratch `#eval`.
- [x] 2.3 Add `Bench.lean` legs measuring `decodeByteArray byte` / `decodeVarint` /
      `encodeVarint` against the `List` (`decode byte`) and `Array UInt8`
      (`decodeArray byte`) baselines; `nix build '.#bench'` and run on a 1 MiB / 16384
      synthetic input. Verify the `ByteArray` carrier is genuinely O(1)-indexed in the
      extracted C and record the before/after figures.

## 3. Documentation + integration gate

- [x] 3.1 Update `AGENTS.md` handoff and `invertible-binary-core/tasks.md` ledger with
      the measured figures and the "`ByteArray` is the densest stdlib carrier; the
      toolchain was the blocker, now the carrier is the last lever" finding; note the
      author-FFI/compiler tier remains deferred. Verify the docs are consistent with
      the measured numbers and keep the `[D#]`/`[S#]` anchor table unchanged (no new
      departure/strengthening).
- [x] 3.2 `nix build '.#checks.<system>.lean'` and `nix build '.#bench'` both green;
      `nix fmt` leaves no staged-file reformat; `lake build` (the proof gate) clean;
      working tree staged per the repo's per-file commit convention.

## 4. Native index recursion (correction — the packed win was forfeited)

Tasks 1.1–1.3 shipped `decodeByteArray`/`decodeFullByteArray` **by composition** over
the `Array` carrier (`decodeArray`/`decodeFull`), which re-materializes `a.data.toList`
and runs the _list_ decoder — so no byte is ever read from the packed `uint8_t*` and
the carrier delivers no speedup (`decodeFullByteArray` ≈ `decodeFull` ≈ the list cost).
Re-open the carrier as a **native index recursion** (reading `a[i]`), and make the
`Array` full-consumption decoder native too (same composition bug, decision #2).

- [x] 4.1 Rewrite `Codec/DecodeByteArray.lean`'s `decodeByteArray` as a **native index
      recursion**: `decodeByteArrayRel d a i` structurally identical to `decode`, with
      the `byte` case `if h : i < a.size then [(a[i], 1)] else []` (the O(1)
      `lean_byte_array_get!`), sequing recursing `i + m`; public `decodeByteArray d a i
= (decodeByteArrayRel d a i).map (fun (x,n) => (x, i+n))`. Prove
      `decodeByteArrayRel_eq : decodeByteArrayRel d a i = decodeArrayRel d a.data i`
      (via `a[i] = a.data[i]` = `ByteArray.getElem_eq_getElem_data`, no new induction),
      so `decodeByteArray_eq`/`decodeByteArray_spec` still transfer. Zero `sorry`, `[propext, Quot.sound]`.
      **DONE** — native `decodeByteArrayRel`/`decodeByteArray` + `decodeByteArrayRel_eq`/
      `decodeByteArray_eq`/`decodeByteArray_byte` live in `DecodeByteArray.lean`; the bridge lemmas
      `decodeByteArrayRel_pos`/`decodeByteArrayRel_le_size`/`decodeByteArrayRel_bounds` (productivity/
      bounds witnesses) are proved. (The native `decodeFullByteArray` definition plus the
      `decodeFullByteArray_lt` well-foundedness witness are also in place; the full spec proof
      followed in 4.2.)
- [x] 4.2 **DONE.** Prove the native `decodeFullByteArray` full-consumption spec. The
      native `WellFounded.fix` recursion (on `a.size - i`, reading `a[i]`) is proved
      against `decodeRepeat` in the membership form — the index mirror of `decodeFull_spec`,
      with the same `huniq` hypothesis. Shipped in `DecodeByteArray.lean`: the candidate
      correspondence `mem_decodeByteArrayRel_to_decode`/`mem_decodeByteArrayRel_of_decode`/
      `drop_of_mem_decode_byteArray` (threading the relative-consumed `Nat` against the `Bytes`
      remainder through `decodeByteArrayRel_eq`/`decodeArrayRel_eq` + `drop_add_length_of_append`),
      the step lemmas `decodeFullByteArrayStep_some`/`decodeFullByteArrayStep_ne_none` (mirrors of
      `decodeFullStep_some`/`decodeFullStep_ne_none`), the forward/completeness laws
      `decodeFullByteArray_some`/`decodeFullByteArray_ne_none`, and the membership-form
      `decodeFullByteArray_spec` (`decodeFullByteArray p h a i = some (xs,j) ↔ (xs,[]) ∈
decodeRepeat p h (drop i) ∧ j = a.size`). The base case of `decodeFullByteArray` returns
      `(a.size)` (not `i`) so the end index equals the full buffer length, matching
      `decodeFullArray`/the `Bench.lean` `j = n` expectation. `#print axioms
Codec.decodeFullByteArray_spec` ⇒ `[propext, Quot.sound]`.
- [x] 4.3 **DONE.** Made `decodeFullArray` (`Codec/DecodeArray.lean`) native — a
      `WellFounded.fix` on `a.size - i` reading `a[i]` (not `decodeFull p h (a.toList.drop i)`),
      proved equal to the `Bytes` spec. Removes the same `.toList` materialization on the
      `Array` carrier (decision #2: no composition over `decodeFull`). Shipped: the bounds
      lemmas `decodeArrayRel_pos`/`decodeArrayRel_le_size`/`decodeArrayRel_bounds`, the
      candidate correspondence `mem_decodeArrayRel_to_decode`/`mem_decodeArrayRel_of_decode`/
      `drop_of_mem_decode` (routed directly through `decodeArrayRel_eq`, no `ByteArray.data` step),
      the native `decodeFullArray_lt`/`decodeFullArrayStep`/`decodeFullArray`, and the step/forward/
      completeness laws `decodeFullArrayStep_some`/`decodeFullArray_some`/`decodeFullArrayStep_ne_none`/
      `decodeFullArray_ne_none` + `decodeFullArray_spec` (membership form, same `huniq` hypothesis).
      `#print axioms Codec.decodeFullArray_spec` ⇒ `[propext, Quot.sound]`.
- [x] 4.4 **DONE.** Re-benchmarked. The extracted C now reads packed bytes via the O(1)
      primitives (no `.toList` in the hot path): `DecodeByteArray.c` uses `lean_byte_array_size` + `lean_byte_array_fget` (line 172–183), `DecodeArray.c` uses `lean_array_get_size` +
      `lean_array_fget_borrowed`. `#eval` cross-check `decodeFullByteArray byte [1,2,3] 0 =
some ([1,2,3], 3)` == `decodeFullArray` == `decodeFull`; `decodeVarint (encodeVarint

12345678. 0 = [(12345678,4)]`. Figures (arm64, reps=20): `decodeByteArray byte [1 MiB]`      = **83 ns** (was ≈ 0.4 ms compositional — ~4800×),`decodeFullByteArray byte [8192]`=
      ~298 µs and`decodeFullArray byte [8192]`= ~302 µs (native, but full-consumption is
      result-list-construction-bound so matches`decodeFull` ~271 µs — honest, no carrier
          win on the list-building path, no regression).

- [x] 4.5 **DONE.** Re-verified the integration gate: `lake build` (zero `sorry`/warnings),
      `nix build '.#checks.aarch64-darwin.lean'` (proof gate) + `nix build '.#bench'` both
      green; `nix build '.#checks.aarch64-darwin.openspec'` and
      `.#checks.aarch64-darwin.formatting` also green. Axiom record unchanged
      (`#print axioms Codec.roundtrip` / `Codec.decodeFullByteArray_spec` /
      `Codec.decodeFullArray_spec` ⇒ `[propext, Quot.sound]`). Refreshed the `AGENTS.md`
      handoff and the `invertible-binary-core/tasks.md` §10.6 ledger with the native-rewrite
      state and the measured figures (see 4.4).

## 5. Standing representation decision (recorded, follow-up deferred)

- [x] 5.1 State the **run-model commitment** in the `README.md` (new
      `Representations — two byte types, two jobs` section) and in this change's
      `proposal.md`/`design.md` (decision #6): `Bytes = List UInt8` is the proof
      substrate, `ByteArray` is the committed run-model, and `Array UInt8` is demoted
      to a non-canonical stepping stone. Grounded in the measured figures
      (`decodeByteArray` ~112 ns vs `decodeArray` ~14.7 µs; `encodeByteArray` ~52 ns vs
      `encodeArray` ~441 ns — `Array UInt8` is strictly dominated).
- [ ] 5.2 (follow-up, out of scope here) mechanically remove the `Array UInt8` carrier
      (`Codec/DecodeArray.lean`/`EncodeArray.lean` + their `Sound.lean` transfer laws)
      once nothing downstream references it. Recorded as a separate follow-up, not
      folded into this change's proof work.
