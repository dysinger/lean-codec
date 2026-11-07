# Tasks — `basen-uppercase-prepass`

**Direction.** Work top-down. §1 establishes the two mutation tests **before**
anything is deleted, because the failure this change can introduce is silent
corruption, not a type error.

**Starting state** (`./lean-basen` @ `0c1ae21`, gates green):

```
Base16/Base16.lean  1191 lines, 67 theorems — 24 of them the case-folding tier
Base32/Base32.lean  3973 lines, 122 theorems — no case tier; rejects lowercase
Base64/Base64.lean  3488 lines, 103 theorems — lowercase letters are DATA
```

```
Base32.decodeFullB32 "MY======"  → some …     (uppercase accepted)
Base32.decodeFullB32 "my======"  → none       (lowercase rejected)
Base64.decodeFullB64 "TWFu"      → some "Man"
Base64.decodeFullB64 "twfu"      → some (a DIFFERENT value)
```

## 1. Establish the safety tests first (blocking)

- [ ] 1.1 **Base64 exclusion test.** Prove or `#eval` that uppercasing a base64
      payload changes its decoded value — `TWFu` → `Man` vs `twfu` → something else.
      This makes the exclusion a measured fact. Commit it as a permanently failing
      assertion (`example` expecting `≠`) so a later "helpful" addition of the
      pre-pass to base64 breaks the build.
- [ ] 1.2 **Per-base mutation of the pre-pass.** After §2, disable `upperBytes` for
      base16 and require the lowercase vector to fail / the gate to fail; repeat for
      base32. If either mutation passes, the change is not made.
- [ ] 1.3 Record the alphabet evidence per base with the measurement that settles it
      (`b32ToVal` has no `97–122` branch; `b64ToVal` maps `97–122` → 26–51).

## 2. The pre-pass

- [ ] 2.1 `upperByte : UInt8 → UInt8` — `a`–`z` → `A`–`Z`, everything else fixed.
      `upperBytes {n} : Bytes n → Bytes n := fun i => upperByte (s i)`.
- [ ] 2.2 `upperBytes_idem` — the idempotence proof. `[propext, Quot.sound]`-only.
- [ ] 2.3 `upperByte_fixed_of_not_lower` and `upperByte_lower` — the two behaviour
      lemmas the decoders need. Keep this set **small**; if a proof needs a fifth
      lemma about `upperByte`, stop and ask whether the pre-pass or the decoder is
      wrong.

## 3. Wire base16 through the core mechanism

- [ ] 3.1 `decodeHexFold s := decodeFull hexElem hexConsumesByte (upperBytes s)` —
      i.e. `decodeNormal upperNormalizer hexBlockIsoF`, using `Codec/Normal.lean`'s
      `decodeNormal_encode` rather than a local chain.
- [ ] 3.2 `decodeHexFold_lowercase_eq` — the one behavioural theorem: `"6f"` and
      `"6F"` decode alike.
- [ ] 3.3 `decodeHexFold_of_fixed` — on already-uppercase input it agrees with the
      strict decoder (`decodeNormal_of_fixed` supplies this).
- [ ] 3.4 **Delete** the parallel tier: `hexBlockIsoF` (no caller outside the tier),
      `fill_foldList`, `hexBlockApply_foldList`, `hexBlockApply_foldList_ne`,
      `foldNormalizer`, `hexToNibble_foldByte_true/_false/_value`,
      `hexNibbleValid_foldByte`, `decodeHexBlockFold_both_cases`,
      `decodeHexBlockFold_case_insensitive`, `foldList_hexBlockUnapply`,
      `foldByteBytes_idem`, `foldByte_of_hexDigit`, `foldByteBytes_of_encodeHex` —
      keeping only what 3.1–3.3 need. **Regenerate `Axioms.lean` afterwards**; the
      gate will name every deleted pin.
- [ ] 3.5 Correct the two RFC misquotes (`Base16.lean:14`, `:641`) to §8's own
      wording, and mark lowercase acceptance as optional.

## 4. Base32

- [ ] 4.1 `decodeB32Fold s := decodeFullB32 (upperBytes s)`, plus the one theorem
      that `"my======"` and `"MY======"` decode alike.
- [ ] 4.2 Confirm the strict `decodeFullB32` still rejects lowercase (it does today:
      measured), so the widening is purely additive.

## 5. Base64 — explicitly not done

- [ ] 5.1 Record in `Base64.lean`'s docstring **why** it has no case pre-pass: its
      alphabet is all 64 symbols including 26 lowercase letters, so case is data.
      Point at §1.1's measurement.

## 6. Gates, bench, prose

- [ ] 6.1 Regenerate `basen`'s `Axioms.lean`; header numbers moved with the `expected*`
      constants; every remaining law pinned.
- [ ] 6.2 Bench vectors: base16 `"6F"`/`"6f"`, base32 `"MY======"`/`"my======"`,
      base64 `"TWFu"` (and the negative: `"twfu"` must NOT equal it).
- [ ] 6.3 `basen` README: state the pre-pass shape, the base64 exclusion **with its
      reason**, and the corrected RFC wording.
- [ ] 6.4 `lake build`, `lake build bench`, `nix build '.#bench'`, `nix fmt`,
      commit per family, print `git diff --cached --name-only`.
- [ ] 6.5 Bump `lean-basen`'s `codec` pin only if `codec` changed.

## 7. Measured outcome to record when closed

- [ ] 7.1 Record the net theorem delta (expected ≈ −24 +8) and the line delta, and
      whether `hexBlockIsoF` really had no caller. If the count differs from the
      estimate, say so in the ledger — do not quietly move the number.

## 8. Recorded, not in this change

- **`basen-nat-iso`** (the numeric codec) is a separate change and its premise is
  under review: `basen` is "base-N byte encodings", and a numeral is not one. Do not
  start it from here.
- **Whitespace trimming and leading-zero stripping** are the same normaliser pattern.
  They belong with whatever numeric codec is eventually built, and should reuse
  `upperNormalizer`'s shape rather than invent a second mechanism.
