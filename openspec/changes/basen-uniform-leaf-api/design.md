# Design

## Context

See `proposal.md` — Why. All seven `basen` bases share one shape: a `Nat`-level
fixed-width digit codec (`encodeN`/`decodeN`) plus a `UInt8` lift that is
verbatim-duplicated seven times (`encode`/`decode`/`roundtrip` + the
`toByte_valTo*`/`*_lt_256` correspondence lemma). This change factors that lift
once so a leaf is _only_ its digit math.

## Goals / Non-Goals

**Goals:**

- One shared lift: `encode = lift.enc encodeN`, `decode = lift.dec decodeN`,
  `roundtrip` proved once, parameterized by the `Nat`-level codec + per-digit facts.
- Seven bases reduced to a `Nat`-level codec + a digit bijection.

**Non-Goals:**

- No core-`Codec` change, no new primitives, no behavior change.
- **No BE/LE, fixed-width, or `varint` codecs** — neither here nor in core `codec`.
  These arrive later in their own packages (varint → a `vbin` package, etc.), not
  in `basen` and not baked into `codec`. This is `basen`-internal only.

## Decisions

### D1 — The shared shape is a `List Nat` codec lifted pointwise

Every base is `encodeN bs = bs.flatMap (fun b => digitList b)` and `decodeN` a
group-and-fold, i.e. a `Nat`-level codec of `List Nat`. The `UInt8` lift is:

```lean
-- generic, in one place
def liftEncode (codeWord : Nat → List Nat) (bs : List UInt8) : List UInt8 :=
  bs.flatMap (fun b => (codeWord b.toNat).map toByte)

def liftDecode (codeWordInv : List Nat → Option (Nat × List Nat))
    (bs : List UInt8) : Option (List UInt8) :=
  -- traverse bs, map each byte to its codeWordInv at Nat level, lift results
```

The key fact that makes the lift correct for _all_ bases is the already-proved
per-base invariant: **every digit byte is ASCII `< 256`**, so
`(toByte n).toNat = n` (via `UInt8.toNat_ofNat'` + `Nat.mod_eq_of_lt`) and
`UInt8.ofNat_toNat`. This is exactly the `toByte_valTo*`/`*_lt_256` lemma
currently copied per base, lifted to one parameterized lemma.

### D2 — Each base supplies a `Nat`-level `codeWord` + bijection

Each `BaseN.BaseX` keeps and exposes:

- its digits (`bitsOf`/`bitsVal`, `nibbles`, octal/10 triples, 5-bit/6-bit blocks),
- `encodeN`/`decodeN` (the `Nat`-level codec, unchanged),
- the per-digit `<->val` bijection and `*valid`/`*_lt_256` facts (already present),

and _delegates_ the `UInt8` surface to the shared lift. Its `roundtrip` becomes
`liftRoundtrip (encodeN) (decodeN) (decodeN_encodeN …) …` — or, more directly,
the `roundtripN` theorem each base already proves is _transported_ by the lift
to `roundtrip (UInt8)` once.

### D3 — The `Nat ↔ UInt8 <256` bridge is proved once

One theorem `liftCodeWord_lt_256 : (∀ b < 256, codeWord b ⊆ ascii<256) → …`
captures the `toByte`/`.toNat` transparency; each base supplies the
`codeWord b < 256` fact (already `valTo*_lt_256`). No base re-proves the
`UInt8.ofNat`/`toNat` plumbing.

### D4 — The 5.1 terminal-padding fix is orthogonal and preserved

base32/64's `rest = []` guards stay in their `decodeN` (`Nat` level, untouched);
the lift does not affect them. The lift's `decode` is total over `decodeN`'s
`Option`, so rejection is whatever `decodeN` says.

## Risks / Trade-offs

- **[Generic `decode` lift is slightly less direct than hand-unrolled]** — the
  lift's `decode` is a `List`-traversal with an `Option`-fold; the per-base
  hand-rolled `decode` is replaced by it. If the lift makes a proof _harder_ for
  a specific base (e.g. base32/64's block recursion), that base may keep a
  thinner bespoke `decode` for the `Nat` level while _still_ sharing the `UInt8`
  lift — the point is to share the `UInt8`↔`Nat` bridge, not to force one
  `decode` body.
- **[Not over-abstracting]** — do not add `satisfy`/`sum`/fixed-width now; keep
  the lift restricted to what the seven bases actually share. If a clean lift
  does not fall out, we stop and re-scope (the goal is _less_ code, not a
  clever abstraction).

## Migration Plan

1. Add `BaseN/Lift.lean` (or `BaseN/Core.lean`) with `liftEncode`/`liftDecode`
   and the one `Nat↔UInt8<256` bridge lemma, proved `[propext, Quot.sound]`.
2. Re-express `BaseN.Base2/4/8/10/16` as the lift + their `Nat` codec/`codeWord`;
   verify `lake build` and byte-exact vectors unchanged.
3. Re-express `BaseN.Base32/64` (the block-recursing two) — sharing the `UInt8`
   bridge while keeping their `Nat`-level block `decodeN`; preserve the 5.1
   terminal-padding guards.
4. Delete the seven duplicated `UInt8` lifts and `toByte_valTo*`/`*_lt_256`
   lemmas; update `BaseN.lean` facade and `Bench.lean` imports if names move.
5. Gate: `lake build` zero `sorry`/warnings; `#print axioms BaseN.roundtrip` and
   each `BaseN.Base{X}.roundtrip` = `[propext, Quot.sound]`; byte-exact vectors
   still `rfl`; `nix flake check` green; commit + push.

## Open Questions

None — this is a pure de-duplication; behavior and laws are unchanged.
