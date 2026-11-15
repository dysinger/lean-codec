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

- [x] 1.1 **Base64 exclusion test.** Prove or `#eval` that uppercasing a base64
      payload changes its decoded value — `TWFu` → `Man` vs `twfu` → something else.
      This makes the exclusion a measured fact. Commit it as a permanently failing
      assertion (`example` expecting `≠`) so a later "helpful" addition of the
      pre-pass to base64 breaks the build.
- [x] 1.2 **Per-base mutation of the pre-pass.** After §2, disable `upperBytes` for
      base16 and require the lowercase vector to fail / the gate to fail; repeat for
      base32. If either mutation passes, the change is not made.
- [x] 1.3 Record the alphabet evidence per base with the measurement that settles it
      (`b32ToVal` has no `97–122` branch; `b64ToVal` maps `97–122` → 26–51).

## 2. The pre-pass

- [x] 2.1 `upperByte : UInt8 → UInt8` — `a`–`z` → `A`–`Z`, everything else fixed.
      `upperBytes {n} : Bytes n → Bytes n := fun i => upperByte (s i)`.
- [x] 2.2 `upperBytes_idem` — the idempotence proof. `[propext, Quot.sound]`-only.
- [x] 2.3 `upperByte_fixed_of_not_lower` and `upperByte_lower` — the two behaviour
      lemmas the decoders need. Keep this set **small**; if a proof needs a fifth
      lemma about `upperByte`, stop and ask whether the pre-pass or the decoder is
      wrong.

## 3. Wire base16 through the core mechanism

- [x] 3.1 `decodeHexFold s := decodeFull hexElem hexConsumesByte (upperBytes s)` —
      i.e. `decodeNormal upperNormalizer hexBlockIsoF`, using `Codec/Normal.lean`'s
      `decodeNormal_encode` rather than a local chain.
- [x] 3.2 `decodeHexFold_lowercase_eq` — the one behavioural theorem: `"6f"` and
      `"6F"` decode alike.
- [x] 3.3 `decodeHexFold_of_fixed` — on already-uppercase input it agrees with the
      strict decoder (`decodeNormal_of_fixed` supplies this).
- [x] 3.4 **Delete** the parallel tier: `hexBlockIsoF` (no caller outside the tier),
      `fill_foldList`, `hexBlockApply_foldList`, `hexBlockApply_foldList_ne`,
      `foldNormalizer`, `hexToNibble_foldByte_true/_false/_value`,
      `hexNibbleValid_foldByte`, `decodeHexBlockFold_both_cases`,
      `decodeHexBlockFold_case_insensitive`, `foldList_hexBlockUnapply`,
      `foldByteBytes_idem`, `foldByte_of_hexDigit`, `foldByteBytes_of_encodeHex` —
      keeping only what 3.1–3.3 need. **Regenerate `Axioms.lean` afterwards**; the
      gate will name every deleted pin.
- [x] 3.5 Correct the two RFC misquotes (`Base16.lean:14`, `:641`) to §8's own
      wording, and mark lowercase acceptance as optional.

## 4. Base32

- [x] 4.1 `decodeB32Fold s := decodeFullB32 (upperBytes s)`, plus the one theorem
      that `"my======"` and `"MY======"` decode alike.
- [x] 4.2 Confirm the strict `decodeFullB32` still rejects lowercase (it does today:
      measured), so the widening is purely additive.

## 5. Base64 — explicitly not done

- [x] 5.1 Record in `Base64.lean`'s docstring **why** it has no case pre-pass: its
      alphabet is all 64 symbols including 26 lowercase letters, so case is data.
      Point at §1.1's measurement.

## 6. Gates, bench, prose

- [x] 6.1 Regenerate `basen`'s `Axioms.lean`; header numbers moved with the `expected*`
      constants; every remaining law pinned.
- [x] 6.2 Bench vectors: base16 `"6F"`/`"6f"`, base32 `"MY======"`/`"my======"`,
      base64 `"TWFu"` (and the negative: `"twfu"` must NOT equal it).
- [x] 6.3 `basen` README: state the pre-pass shape, the base64 exclusion **with its
      reason**, and the corrected RFC wording.
- [x] 6.4 `lake build`, `lake build bench`, `nix build '.#bench'`, `nix fmt`,
      commit per family, print `git diff --cached --name-only`.
- [x] 6.5 Bump `lean-basen`'s `codec` pin only if `codec` changed. **Not bumped** —
      `codec` did not change. The pre-pass went into `BaseN.Common` precisely so that it
      would not have to: `upperBytes` is a concrete alphabet operation, and `codec` ships
      no concrete format (`[S3]`). What `codec` supplies is the mechanism
      (`Normalizer`/`decodeNormal`), which both bases now use rather than re-derive.

## 7. Measured outcome to record when closed

- [x] 7.1 Record the net theorem delta (expected ≈ −24 +8) and the line delta, and
      whether `hexBlockIsoF` really had no caller. If the count differs from the
      estimate, say so in the ledger — do not quietly move the number.

      **MEASURED, and the estimate was wrong in both directions.**

      | quantity | estimate | measured |
      | --- | --- | --- |
      | gate universe | ≈ −24 + 8 = −16 | **722 → 698, net −24** |
      | `Base16.lean` decls | 67 → ~50 | **88 → 53** |
      | `hexBlockIsoF` callers | "none outside the tier" | **confirmed: none** |
      | `Base32` | additive only | **confirmed: 121 → 124** |

      The `+8` estimate was too low and the `−24` too high *individually*, and they
      happened to net close to right — which is exactly the shape of accident that
      makes an estimate untrustworthy rather than vindicated. Measured: **29 pins
      deleted** from the tier, **+18** added across `Common` (6), `Base16` (9 net) and
      `Base32` (3), and `hexBlockIsoF` off the definition allowlist (17 → 16).

      `Base16.lean`'s 88 → 53 counts `theorem`+`def` lines: 29 tier declarations deleted,
      2 added (`decodeHexFold` kept, `upperByte_of_hexDigit` / `upperBytes_of_encodeHex`
      added), and the section header rewritten.

      **The `+8` was wrong because it counted *required* laws rather than *incidental*
      ones.** The pre-pass needs `upperByte_toNat`, `upperByte_lower`,
      `upperByte_eq_self_of_not_lower`, `upperByte_idem`, `upperBytes_idem` — five, not
      the three the estimate's `upperBytes_idem` + two behaviour lemmas implies — and the
      shared location means `upperNormalizer` is a `Prop`-valued **`theorem`**, which the
      compiler enforces and an estimate would not have guessed.

## 8. Recorded, not in this change

- **The numeric codec** is now `basen-radix` (2026-11-13), which **supersedes and
  retires `basen-nat-iso`** — the base-10-only slice of the same layer. Do not start
  `basen-nat-iso` from here: it no longer exists. `basen-radix` adds a radix-generic
  `digitVal`/`toNat`/`ofNat` over `Nat` for bases 2/4/8/10/16/32/64.
- **Whitespace trimming and leading-zero stripping** are the same normaliser pattern.
  They belong with the numeric codec, and `basen-radix`'s `trimFor` (its task 2.1) is
  where they land. **Check whether it reuses `upperNormalizer`'s shape before inventing a
  second mechanism** — this note is the reason that check exists, and `basen-radix` was
  authored without seeing it.
