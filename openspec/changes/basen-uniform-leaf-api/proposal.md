# Proposal

## Why

The seven `basen` bases (`BaseN.Base2/4/8/10/16/32/64`) are each a **bespoke**
copy of the same four functions:

```lean
encodeN : List Nat → List Nat          -- digit-map each byte
decodeN : List Nat → Option (List Nat) -- group-and-fold, reject bad input
encode  : List UInt8 → List UInt8      -- the *same* UInt8 lift in every base
decode  : List UInt8 → Option (List UInt8)  -- the *same* UInt8 lift in every base
```

Only the `Nat`-level digit math differs (bits / quartets / octal triples /
decimal triples / hex nibbles / 5-bit / 6-bit blocks). The `UInt8` lift — map
`b.toNat` to digit bytes via `toByte`, validate via `*.toNat`, fold back, the
`toByte_valTo*`/`*_lt_256` correspondence lemma — is **verbatim duplicated in
all seven files**, and each base re-proves its `roundtrip` from scratch.

That is the bad smell: a leaf format should be a _thin_ parameterization of one
shared combinator, not seven near-identical function sets. This change factors
the shared lift so each base is `encode = liftDig encodeN`, `decode = liftDig
decodeN`, and the `Nat↔UInt8<256` bridge is proved **once**, not seven times.

## What Changes

- Introduce one shared "digit-list over `List UInt8`" lift in the `basen`
  package (e.g. `BaseN.Core` or `BaseN.Lift`) that, given a `Nat`-level
  `encodeN : List Nat → List Nat` and `decodeN : List Nat → Option (List Nat)`
  (with the per-digit `<→val` facts), produces the `UInt8`-level
  `encode : List UInt8 → List UInt8` and `decode : List UInt8 → Option
(List UInt8)` **and** their `roundtrip`, parameterized once.
- Rewrite each of the seven bases to supply only its `Nat`-level codec + the
  per-digit bijection lemmas, and inherit `encode`/`decode`/`roundtrip` from the
  shared lift.
- Delete the seven copies of the `UInt8` lift and the seven near-identical
  `toByte_valTo*`/`*_lt_256` lemmas.

This is **not** a change to the core `Codec` (no `satisfy`/`sum`/fixed-width
primitives are added yet). It is the minimal factorization that makes the
`basen` leaves uniform _within the `basen` package_ — the first concrete
de-bespoking, to be observed before deciding whether/when the core `codec`
gains real leaf primitives.

## Capabilities

### New Capabilities

- `basen`: a single shared digit-list-over-`List UInt8` lift, so every base is a
  thin `Nat`-level codec parameterized into one uniform `encode`/`decode`/
  `roundtrip`.

### Modified Capabilities

- `basen`: the seven leaf modules are re-expressed as instances of the shared
  lift (same behavior, same roundtrip laws, `[propext, Quot.sound]`-only), with
  the duplicated `UInt8` lift and `Nat↔UInt8<256` lemmas removed.

## Impact

- **Code**: seven files shrink to their `Nat`-level digit core + a per-digit
  bijection; one new shared lift module holds the `UInt8` bookkeeping.
- **Proofs**: the `roundtrip` is proved once over the lift; each base supplies
  its `decodeN (encodeN bs) = some bs` and per-digit facts. `#print axioms` stays
  `[propext, Quot.sound]`.
- **No behavior change**: byte-exact vectors still hold; the 5.1 terminal-padding
  fix is orthogonal and preserved.

## Non-Goals

- No new core-`Codec` primitives (`satisfy`/`sum`/fixed-width ints) yet.
- No change to `codec` itself.
- **Explicitly out of scope (now and later, unless a future package needs them):**
  big-endian / little-endian word codecs (`word16be/le`, `word32be/le`), fixed-width
  integer codecs, `varint`/LEB128, `satisfy`/predicate-byte. These belong in their
  own downstream packages (e.g. `lean-vbin` for varint), never baked into core
  `codec` or `basen`. This change is **internal to `basen` only** and touches
  nothing under `Codec/`.
