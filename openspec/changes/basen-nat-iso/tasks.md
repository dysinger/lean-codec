# Tasks — `basen-nat-iso`

**Direction.** Work top-down. §1 decides the type; nothing else can be proved
before it is settled, because a strict `Iso` over raw `Bytes n` is _false_
(`"001"` is a valid `Bytes 3` that no `Nat` maps to).

**Measured state of the tree this change starts from** (`./lean-basen` @ `5946af9`,
`./lean-codec` @ `8c0c7dd`; both `lake build` green):

```
encodeDig [0x01]        → 3 digit bytes   ("001")
encodeDig []            → 0 digit bytes   ("")
decodeRepeat  "001"     → [[], [1]]                  (two answers)
decodeRepeat  "000001"  → [[], [0], [0,1]]           (three answers)
decodeFull    "001"     → some [1]                   (unique at full consumption)
decodeFull    "01"      → none                       (2 is not a multiple of 3)
grep -rn 'Nat → List UInt8|List UInt8 → Nat' BaseN/ → (no hits)
```

**There is no `Nat`/`Int`-valued codec anywhere in either repo.** This is new work
on a proved foundation, not a repair.

## 1. Settle the type (blocking — nothing below can start)

- [ ] 1.1 Decide the codomain of the strict `Iso`. Raw `Bytes n` is **not** an
      option (proved false by `"001"`); the choices are a canonical-digit subtype,
      a `Slice`-style refinement, or a `Normal`-quotient. Record the choice with the
      measurement that forced it.
- [ ] 1.2 Write the **`"01"`-rejection witness** first and confirm it fails to
      typecheck if the decoder stops rejecting. A decoder that accepts `"01"` while
      `enc 1 = "1"` makes `Iso.law` false, so this witness is the proof's foundation,
      not a test.
- [ ] 1.3 Decide `Nat`-only vs `Integer` (proposal §"Decisions" 1). If `Integer`,
      settle `-0` in the same task — it is the same defect one level up.

## 2. The strict codec

- [ ] 2.1 `natDigits : Nat → List UInt8` — minimal decimal digits, `0 ↦ "0"`,
      `1 ↦ "1"`, no padding.
- [ ] 2.2 `natOfDigits : List UInt8 → Option Nat` — rejects empty, rejects a
      leading `0` unless the list is exactly `"0"`, rejects non-digits.
- [ ] 2.3 The two round-trip equations `natOfDigits (natDigits n) = some n` and
      `natDigits (natOfDigits ds) = ds` **on the canonical domain only** — the
      second is false off it, and saying so is the point.
- [ ] 2.4 `Iso.ofTotal`-style construction, or a hand-built `Iso` if the domain is
      partial. Every law `[propext, Quot.sound]`-only, verified with `#print axioms`.

## 3. The lenient layer (outside the `Iso`)

- [ ] 3.1 A `normalize` that trims leading zeros (and the empty string to `"0"` if
      that is the chosen reading), proved idempotent — the `Normalizer` law.
- [ ] 3.2 `decodeNatLenient ds = decodeNat (normalize ds)`, with the theorem that it
      agrees with the strict decoder on canonical input. Base16's `decodeHexFold`
      is the precedent: the fold is **outside** the `Iso`, so `law` is untouched.
- [ ] 3.3 State explicitly what leniency **cannot** express: a lax spelling that
      differs in _length_ is still a different byte string, so the normalizer is a
      trimmer, not an equivalence-class quotient (`fstar-codec` `[W9]` records the
      same bound).

## 4. Gate, bench, prose

- [ ] 4.1 Regenerate `basen`'s `Axioms.lean`; every new law pinned, and the header
      numbers moved with the `expected*` constants.
- [ ] 4.2 Bench vectors: `0`, `1`, `9`, `10`, `"01"`, `""`, and a multi-digit value,
      each value-checked. The `"01"` and `""` rows must show **rejection**.
- [ ] 4.3 `basen` README: replace the "scope is digit encodings, not numeric ones"
      note with what now exists, and keep the leading-zero rule as the reason the
      strict/lax split is drawn where it is.

## 5. Gates

- [ ] 5.1 `lean-basen`: `lake build` (every gate line), `lake build bench`,
      `nix build '.#bench'`.
- [ ] 5.2 `nix fmt`, then commit per task family, individual files, printing
      `git diff --cached --name-only`.
- [ ] 5.3 Bump `lean-basen`'s `codec` pin only if `codec` changed; otherwise no pin
      churn.

## 6. Recorded, deliberately not in this change

- **`Integer`**, if §1.3 scopes to `Nat` first — a follow-on change with its own
  `-0` witness.
- **The other six bases.** Base 2/4/8/16/32/64 numeral codecs are the same shape and
  should follow once decimal is proved; doing seven at once hides a wrong shape
  seven times.
- **`varint`/LEB128.** Overlong forms are the same defect class (`[0x80;0x00]` vs
  `[0x00]`) but a different wire format; separate change.
