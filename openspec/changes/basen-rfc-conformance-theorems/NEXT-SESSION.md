# Next session plan — `basen-rfc-conformance-theorems`

Status snapshot at handoff (2026-10-20): **14 → 15 of 17 tasks done.**
Task 4.3 (the per-base converse) is now **landed in `../lean-basen`** (uncommitted
at handoff — commit it first, see §0). Tasks remaining: **4.5** (facade dispatch)
and **5.3** (commit/push + `openspec/changes/lean-basen/` update).

## 0. Commit the already-done 4.3 work first

`../lean-basen` has uncommitted changes (3 files) that are **complete and
verified** and must be committed before 4.5/5.3:

- `BaseN/Base32.lean`, `BaseN/Base64.lean` — swapped the strict parsers
  `parseB32`/`parseB64` from the _lenient_ block decoder to the **canonical**
  `b32BlockApply`/`b64BlockApply` (re-encode-checked), so non-canonical
  dropped-bit blocks (`"AB=="`, `"AAAB===="`) are now rejected and the converse
  is _true_; added `b32BlockApply_canonical`/`b64BlockApply_canonical`,
  `parseB32_inv`/`parseB64_inv`, and `decodeB32Strict_inverse`/
  `decodeB64Strict_inverse`.
- `Bench.lean` — converse vectors.

Gate already green: `lake build`, `lake build bench` zero `sorry`/warnings;
`#print axioms` of the four new laws = `[propext, Quot.sound]`. Commit these three
files individually (no `git add -A`).

## 1. Task 4.5 — the `Base`-indexed facade dispatch (open signature decision)

The three theorem families exist per base; only the **facade dispatch** is
missing. The blocker is a _signature_ decision, not a proof: the three shapes
have irreducibly different carriers.

| shape        | value        | decode                                                    | encode                                               |
| ------------ | ------------ | --------------------------------------------------------- | ---------------------------------------------------- |
| B2/4/8/10/16 | `List UInt8` | `decodeFull {x}Elem {x}ConsumesByte n s` (over `Bytes n`) | `encode{X} : List UInt8 → Option (Sigma n, Bytes n)` |
| B32          | `B32`        | `decodeB32Strict : List UInt8 → Option B32`               | `encodeB32Strict : B32 → List UInt8` (total)         |
| B64          | `B64`        | `decodeB64Strict : List UInt8 → Option B64`               | `encodeB64Strict : B64 → List UInt8` (total)         |

**Proposed (recommended): Option 1 — a `Base.val : Base → Type` family** with a
`List UInt8`-normalized decode/encode surface (fixed-width via `BaseN.Bridge`),
then `Base.decode_encode_inverse`/`Base.encode_injective` as dependent statements
`cases`-ing over all seven `Base` constructors. This is the faithful "base-tagged
but plain-valued" dispatch: the radix lives on the `base` _index_, never on the
value. Alternatives: (Option 2) three per-shape non-dependent re-exports with no
carrier bridge (smaller, but the five fixed-width bases stay un-unified); (3)
something else the user has in mind.

**Decision needed from the user before implementing.**

## 2. Task 5.3 — commit, push, update the sibling ledger

After 4.5 is signed off: (a) commit 4.5 files, (b) push `../lean-basen`, (c) mark
5.3 in `tasks.md` and reflect the facade in
`openspec/changes/lean-basen/` (its `tasks.md` §4.1 already says "no roundtrip
dispatch"; update it to note the net-new converse/injectivity dispatch).

## 3. `Nat.toDigits` — investigated, _not_ adoptable in the proven encoders

The user asked to "utilize `Nat.to…` functions where possible without slowing
things down." **Finding: not adoptable in the encoders (would both slow them and
change their semantics); usable only as an optional _display_ layer.** Verified
against Lean 4.34.1 core (`Init/Data/Repr.lean`):

- `Nat.toDigits base n : List Char` is **LSB-first, variable-width, zero-_un_-
  padded**, and `digitChar` hard-stops at `≥16` (`'*'`). The fixed-width encoders
  need **MSB-first, fixed-width, zero-padded** `List UInt8` (e.g.
  `octBlockUnapply 0x01 = ['0','0','1']` vs `Nat.toDigits 8 1 = ['1']`;
  `base2` needs 8 bits, `Nat.toDigits 2 0x66` yields 7).
- Alphabet mismatch: base16 needs **uppercase** `A-F`, `digitChar` emits
  **lowercase** `a-f`; base32/64 use _custom_ alphabets (`A-Z2-7`,
  `A-Za-z0-9+/`) that `digitChar` does not express.
- Type mismatch: codec values are `List UInt8` (ASCII bytes), `Nat.toDigits`
  returns `List Char` (needs a `Char.toUInt8` map).
- So replacing the bespoke `valToX`/`bitAt`/`*BlockUnapply` builders would add a
  reverse + left-pad + `Char→UInt8` map over the _same_ boxed `Nat` div/mod — a
  pure slowdown (extra cons-cell churn), not a simplification.
- There is **no** `Nat.ofDigits` (parse-back) in core; the digit→value direction
  also stays bespoke.

If a human-facing/base-rendering helper is wanted (e.g. `render b n : String` via
`Nat.toDigits b n`), it is a **non-law-bearing convenience**, live it outside the
proven `Codec` surface (like the lowercase-accepting hex facade is a non-goal).
Not required by any spec requirement.
