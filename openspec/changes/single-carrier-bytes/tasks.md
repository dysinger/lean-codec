# Tasks

> **Session status (pause point):** tasks 1.1–1.3 (substrate), 2.1 (decode/
> decodeRepeat/ConsumesByte), 2.2 (encode/encodeRepeat) are **done and compile**
> clean (`lake build Codec.Codec Codec.Decode Codec.Encode`, zero warnings),
> `[propext, Quot.sound]`-only. The remaining work (2.3 prefix-arithmetic helpers,
> 3.1–3.3 the Sound/Combinators law re-derivations, 4.1–4.3 deletions/VarBinary/
> lakefile/Bench, 5.1–5.2 gate/docs) is **not started**. `Codec/Sound.lean`,
> `Codec/Combinators.lean`, `Codec/VarBinary.lean` and the transfer modules are
> still the **old `List UInt8` substrate** and will not build against the new
> `Codec/Codec`/`Decode`/`Encode` until re-derived — the tree is intentionally in
> an atomic-change intermediate state. Key design decisions made this session are
> recorded in the task notes below and in `design.md`.

> Replace the `Bytes := List UInt8` / `ByteArray` / `Array` / `Buffer` two-tier
> representation with a single length-indexed `Bytes n := Fin n → UInt8`, then
> delete the transfer modules and their `Classical.choice`-leaking lemmas. Verify
> by `lake build` (zero `sorry`/warnings) and `#print axioms Codec.roundtrip`
> ⇒ `[propext, Quot.sound]` (zero `Classical.choice`) at every step.

## 1. Substrate: the length-indexed byte string

- [x] 1.1 In `Codec/Codec.lean`, replace `abbrev Bytes := List UInt8` with
      `abbrev Bytes (n : Nat) : Type := Fin n → UInt8` and add the `Suffix n`
      record (`consumed : Nat`, `remainder : Bytes (n - consumed)`), the empty
      `Bytes 0`, the single-byte `Bytes 1`, and a `Fin`-shift/prefix lemma; verify
      `lake build Codec.Codec` compiles with the new substrate in place.
- [x] 1.2 Prove the finitary equality and indexing facts: `s₁ = s₂ ↔ ∀ i : Fin n,
    s₁ i = s₂ i` (via `funext`), `Bytes n` equality is decidable, and the
      single-byte read `s ⟨0, _⟩` reduces; verify `#print axioms` on these lemmas
      is `[propext, Quot.sound]` (no `Classical.choice`) and `lake build` stays clean.
- [x] 1.3 Re-state `Rel` and `relRepeat` over `Bytes n` (whole-string relation with
      `n` implicit, `seq` by a finitary `Fin` split); verify the `Rel_iso`/`Rel_seq`/
      `Rel_alt`/`Rel_empty`/`Rel_pure`/`Rel_byte`/`relRepeat` defs compile with
      `lake build Codec.Codec`.

## 2. Decoder / encoder over the single carrier

- [x] 2.1 Re-derive `decode d (s : Bytes n) : List (α × Suffix n)` and the
      productive `decodeRepeat`/`ConsumesByte` (well-founded on `n`) over `Bytes n`;
      verify `lake build Codec.Decode` and the `byte`/`pure`/`seq`/`alt`/`iso` cases
      reduce as expected with a temporary `#eval` smoke test.
      **Scope note:** the `decodeFull`/`decodeRepeatFull` full-consumption _spec_
      proofs (`decodeFull_some`/`decodeFull_ne_none`/`decodeFull_spec` and the
      `decodeFullStep_*` lemmas) are **not** carried over. `decodeFull` is not a
      spec requirement (the spec defines `decode`/`decodeRepeat`/`encode`/
      `encodeRepeat` and the laws, never `decodeFull`), and it is the Tier-A
      efficiency optimization only. The efficient `decodeFull` _definition_ and
      `decodeFull_zero` are retained; `Sound.decodeRepeatFull_spec` is dropped with
      it. If full-consumption efficiency is re-added, re-prove those over the `Suffix`
      carrier.
      **Design refinement (`Suffix` shape):** `Suffix n` is `{ remaining : Nat,
    hle : remaining ≤ n, bytes : Bytes remaining }` — the spec's
      `({m : Nat} × Bytes m)` with the `m ≤ n` witness — rather than the design's
      `{ consumed, remainder : Bytes (n - consumed) }`, because `seq` composes two
      suffixes by threading `m₂ ≤ m₁ ≤ n` transitively with no `Nat.sub` re-derivation
      of `(n - c₁) - c₂` (see design.md §Decisions note added).
- [x] 2.2 Re-derive `encode d x : Option ({n : Nat} × Bytes n)` and `encodeRepeat`
      (Fin-sum concat, O(n) in the type index); verify `lake build Codec.Encode`
      and that `encode Codec.byte` returns the length-1 singleton and `encodeRepeat`
      returns the summed length.
- [ ] 2.3 Re-prove the `decode_suffix` / prefix-arithmetic helper lemmas the
      `seq`/repetition laws need, in the `Suffix`/`Nat.sub` form (the analogue of
      `drop_add_length_of_append`/`flatMap_congr`); verify each lemma's
      `#print axioms` is `[propext, Quot.sound]`.

## 3. Laws over the single carrier (no `Classical.choice`)

- [ ] 3.1 Re-prove `decode_spec`, `bidir`, `encode_rel`, `decode_encode`,
      `roundtrip`, `productive_iff_consumesByte` over `Bytes n`; verify
      `#print axioms Codec.roundtrip` ⇒ `[propext, Quot.sound]` and `lake build`
      is clean of `sorry`.
- [ ] 3.2 Re-prove the repetition laws `decodeRepeat_spec`/`encodeRepeat_rel` and
      the chain converses over `Bytes n`; verify their `#print axioms` reports
      `[propext, Quot.sound]` (zero `Classical.choice`) with `lake build` green.
- [ ] 3.3 Re-derive `Codec/Combinators.lean` (the `sepBy`/`chainl1`/`chainr1`/
      finite combinators) over `Bytes n`; verify `lake build Codec.Combinators`
      compiles and the `_spec`/`_rel`/converse laws close.

## 4. Delete the transfer tier

- [ ] 4.1 Delete `Codec/DecodeArray.lean`, `Codec/EncodeArray.lean`,
      `Codec/DecodeByteArray.lean`, `Codec/EncodeByteArray.lean`,
      `Codec/DecodeByteArraySlice.lean`, `Codec/EncodeByteArraySlice.lean`,
      `Codec/ExternFastPath.lean`, `Codec/ExternFastPath.c`, `Codec/Buffer.lean`;
      drop their imports from the root `Codec.lean`; verify `lake build` compiles
      with only the remaining modules.
- [ ] 4.2 Simplify `lakefile.lean` (drop the `externFastPathO` target and
      `moreLinkObjs`; keep `@[default_target] lean_lib codec`) and rewrite
      `Bench.lean` to drop the array/byte-array/slice/extern lanes and add a
      `Bytes`-substrate lane (scalar-index read, empty-remainder roundtrip,
      encode length); verify `lake build bench` links and the bench runs byte-exactly.
- [ ] 4.3 Re-derive `Codec/VarBinary.lean` (LEB128 `varint`) over `Bytes n`; verify
      `lake build Codec.VarBinary` and `roundtripVarint`/`decodeVarint_eq`/
      `encodeVarint_eq` close `[propext, Quot.sound]`.

## 5. Integration gate + docs

- [ ] 5.1 `lake build` (zero `sorry`/warnings) and `#print axioms Codec.roundtrip`
      ⇒ `[propext, Quot.sound]` (zero `Classical.choice`); run
      `nix build .#checks.<system>.lean` + `.#bench` (detached, polled) and confirm
      both green after `git add` of any new/removed modules.
- [ ] 5.2 Update the README anchors `[D#]`/`[S#]` and the "Representations" section
      to record the single length-indexed carrier and the "carrier split was the
      defect, not the strategy" lesson, and update the `AGENTS.md` handoff (done/
      open) accordingly; verify the docs no longer reference `List UInt8`/`Buffer`/
      `ByteArray` as the substrate.
