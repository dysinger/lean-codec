# Tasks

> **Session status (pause point):** tasks 1.1–1.3 (substrate), 2.1 (decode/
> decodeRepeat/ConsumesByte), 2.2 (encode/encodeRepeat), and **2.3 (prefix-arithmetic
> helpers)** are **done and compile** clean (`lake build Codec.Codec Codec.Decode
Codec.Encode`, zero warnings), `[propext, Quot.sound]`-only. 2.3 landed `prepend_assoc`
>
> - `prepend_single_bdrop` plus the substrate lemmas `Rel_cast`/`Rel_cast_symm`/
>   `bdrop_splice`/`prepend_eq_of_eq_splice` (all proven, zero `sorry`). **Task 3.1
>   (`Sound.lean`) is in progress**: the file is fully re-stated over the length-indexed
>   carrier and typechecks (`lake build Codec.Sound` — only `sorry` warnings); `encode_rel`,
>   `decode_seq_mem`, and `decode_spec`'s `iso`/`alt`/`empty` cases are proven; the rest
>   (`decode_spec` `seq`/`pure`/`byte`, `bidir`, `decode_encode`, `roundtrip`,
>   `productive_iff_consumesByte`, repetition + converses) are clean `sorry` markers.
>   `Codec/Combinators.lean`, `Codec/VarBinary.lean` and the transfer modules are still
>   the **old `List UInt8` substrate** and will not build against the new
>   `Codec/Codec`/`Decode`/`Encode` until re-derived — the tree is intentionally in
>   an atomic-change intermediate state. Key design decisions are recorded in the
>   task notes below and in `design.md`; the continuation plan is in `AGENTS.md`.

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
- [x] 2.3 Re-prove the `decode_suffix` / prefix-arithmetic helper lemmas the
      `seq`/repetition laws need, in the `Suffix`/`Nat.sub` form (the analogue of
      `drop_add_length_of_append`/`flatMap_congr`); verify each lemma's
      `#print axioms` is `[propext, Quot.sound]`.
      **Status: COMPLETE.** Landed and proven in `Codec/Codec.lean` (`lake build Codec.Codec`
      clean, zero warnings, zero `sorry`): `prepend_assoc` (the `seq`-case reassociation,
      with the required `h : t₂.prepend s₂ = t₁.bytes` hypothesis — the handoff's naive form,
      sans `h`, is false) and `prepend_single_bdrop` (the `byte`-case reconstruction
      `(Suffix.drop 1 s).prepend (single (s ⟨0, ·⟩)) = s`). Also landed the supporting
      substrate lemmas the `Sound` re-derivation needs: `Rel_cast`/`Rel_cast_symm` (the
      `Rel` length-cast transport, `subst`-closed), `bdrop_splice`, and
      `prepend_eq_of_eq_splice`. The full cast library (from the prior session's handoff)
      is unchanged (`splice_add`, `cast_fin_symm`, `cast_bytes_val'`, `cast_bytes_val_symm`,
      `Nat.eq_irrel`, `concat_assoc`, `sub_sub_add`).
      **Status (2.3 — cast library DONE + `prepend_assoc` ~90%, still not landed).**
      This session landed the full missing cast library, all `[propext, Quot.sound]`
      (or axiom-free) and building clean (`lake build Codec.Codec`, zero warnings):

      - `splice_add {n m} (hm : m ≤ n) : m + (n - m) = n` — the **named** cast proof
        used by `splice`/`splice_apply`/`prepend_apply`, replacing the inline
        `show … by rw [Nat.add_comm]; exact …`. This is the root-cause fix: the inline
        proof was a `have`-wrapped term that `rw`/`simp` could not structurally match
        against a cast-reduction lemma's `e : n = m` binder; the named constant can.
      - `concat_assoc {a b c} (s₁ : Bytes a) (s₂ : Bytes b) (s₃ : Bytes c) :
        concat s₁ (concat s₂ s₃) = cast (congrArg Bytes (Nat.add_assoc a b c))
        (concat (concat s₁ s₂) s₃)` — the **clean `+`-associativity content** of
        `prepend_assoc`, `<+`-only, no `Nat.sub`; closes by
        `apply Bytes.ext; intro i; unfold concat; rw [cast_bytes_val' (e := Nat.add_assoc a b c)];
        simp; by_cases …; omega`.
      - `cast_fin_symm {n m} (e : m = n) (i : Fin n) : cast (Eq.symm (congrArg Fin e)) i = ⟨i.val, …⟩`
        and `cast_fin_symm_val`/`cast_fin_val` (the `.val` variants) — the `.symm`-aware
        `Fin`-index casts (`splice`/`prepend` produce `Eq.symm (congrArg Fin e)`, which the
        positive-form `cast_fin` does not match).
      - `cast_bytes_val_symm {n m} (e : n = m) (f : Bytes m) (i : Fin n) :
        (cast (Eq.symm (congrArg Bytes e)) f) i = f ⟨i.val, …⟩` — the `.symm`-aware
        `Bytes` cast (`Suffix.prepend` casts its `bytes` along `(Nat.sub_sub_self hle).symm`).
      - `cast_bytes_irrel {n m} (e₁ e₂ : n = m) (s : Bytes n) : cast (congrArg Bytes e₁) s =
        cast (congrArg Bytes e₂) s` — cast-independence via `Nat.eq_irrel`.

      **`prepend_assoc` statement (CORRECTED — needs the `h` hypothesis; the handoff's
      naive form is false):**
      ```lean
      theorem prepend_assoc {n} (t₁ : Suffix n) (t₂ : Suffix t₁.remaining)
          (s₁ : Bytes (n - t₁.remaining)) (s₂ : Bytes (t₁.remaining - t₂.remaining))
          (h : t₂.prepend s₂ = t₁.bytes) :
        (Suffix.trans t₁ t₂).prepend
          (cast (congrArg Bytes (sub_sub_add n t₁.remaining t₂.remaining t₁.hle t₂.hle)) (concat s₁ s₂))
          = t₁.prepend s₁
      ```
      (The suffix region reads `t₂.bytes` on the LHS but `t₁.bytes` on the RHS; `h`
      bridges them. Without `h` the theorem is false.)

      **Proven reduction recipe (validated piece-by-piece):**
      `apply Bytes.ext; intro i;` then `unfold Suffix.trans Suffix.prepend; dsimp;`
      `rw [splice_apply]`×2; `unfold concat`; `repeat rw [cast_fin_symm]` (closing the
      two `splice_add` side goals); then case-split `i.val < n - t₁.remaining`:
      - `hlt` (the `s₁` prefix): `rw [cast_bytes_val' (e := sub_sub_add …)]; simp`
        closes by `s₁ ⟨i.val⟩ = s₁ ⟨i.val⟩`.
      - `¬hlt`: `rw [← h]` (replace `t₁.bytes` with `t₂.prepend s₂`),
        `simp [Suffix.prepend]`, `rw [cast_bytes_val']`×2 to push the `.symm` `bytes`
        cast through, `rw [splice_apply]`, `unfold concat`, `repeat rw [cast_fin_symm]`,
        then case-split `i.val - (n - t₁.remaining) < t₁.remaining - t₂.remaining`:
        - (`s₂` region) `omega` + `cast_bytes_val'` + `simp` closes to `s₂ = s₂`.
        - (`t₂.bytes` region) the two `cast (Suffix.prepend._proof_2 …) t₂.bytes` reads
          differ only in the cast proof (`Nat.le_trans t₂.hle t₁.hle` vs `t₂.hle`); close by
          `Nat.eq_irrel` on `Nat.sub_sub_self …` + `Fin.ext` + `Nat.sub_sub` + `omega`
          (the arithmetic `i.val - (n - t₂.remaining) = i.val - (n - t₁.remaining) -
          (t₁.remaining - t₂.remaining)` is `Nat.sub_sub` ∘ `sub_sub_add`).
      **The one remaining wrinkle:** in the deep-suffix case the two `_proof_2` casts
      are at *different* length types (`t₂ : Suffix t₁.remaining` gives `t₁.remaining -
      (t₁.remaining - t₂.remaining) = t₂.remaining`, while `trans t₁ t₂ : Suffix n` gives
      `n - (n - t₂.remaining) = t₂.remaining`), so the final closure must reduce BOTH
      reads to the bare `t₂.bytes` at a `Fin t₂.remaining` index via `cast_bytes_val'`
      *before* `Fin.ext`/`omega` — not `cast_bytes_irrel` between the two lengths. The
      proof is structurally complete; this last cast-transport order is the finisher.
      `prepend_single_bdrop` (the `byte`-case lemma) is analogous and unstarted.

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
