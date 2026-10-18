# Proposal

## Why

`lean-basen` proves the **roundtrip** law (`decode (encode bs) = some bs`) for
all seven bases, but that is only _half_ of RFC 4648 conformance. RFC 4648 (and
this package's own spec for base2/4/8/10) also demands that the **decoder
reject** every malformed input — wrong alphabet byte, `=` in an illegal
position, wrong arity, and (for the padded bases) any data _after_ the terminal
`=` — and that the **encoder be canonical** (its output is exactly the RFC
alphabet with `=` only at the terminal positions).

Today:

- **No rejection theorems exist.** The F* reference (`fstar-basen`) proves
  `decode [invalid] = none`, `decode [pad-first] = none`, `decode [bad-length] =
none` per base; the Lean port dropped every one of them. The decoders _mostly_
  reject correctly by accident (the `none` branches), but that is asserted by
  construction, never proved, and is **not** covered by the gate.
- **Non-terminal padding is _accepted_.** `Base64.decode "Zg==AAAA"` returns
  `some [..]` and `Base32.decode ("MY======" ++ "AAAAAAAA")` returns `some [..]`
  — the padded-tail branches recurse into `rest` without checking `rest = []`,
  violating RFC 4648 §3.2 ("the `=` only appears at the end").
- **No converse/canonical-uniqueness law.** `decode xs = some ys → encode ys =
xs` is never stated, so nothing proves the encoding is unique (that a single
  byte string has exactly one valid RFC 4648 representation, i.e. that pad
  placement and alphabet choice are forced).

The goal is to make this the **most correct base-`N` package available**: not
just "roundtrips hold" but "the decoder is a _total characterization_ of the
RFC — `decode` succeeds exactly on the RFC-valid inputs and `encode` is the
unique inverse."

## What Changes

Add three families of theorems per base (proved `[propext, Quot.sound]`-only,
zero `sorry`), and fix the one decoder defect they expose:

1. **Canonical encoding** — every encoded byte is in the alphabet
   (`encode`-soundness); for base32/64, `=` appears only in the terminal pad
   positions and the pad count is exactly the RFC §6.7/§4.7 arity.

2. **Decode totality (rejection)** — `decode` returns `none` on every malformed
   input: a byte outside the alphabet, `=` in an illegal (non-terminal)
   position, wrong arity, and — the code fix — any data after the terminal `=`.
   This restores the F* reference's `decode_*_invalid`/`bad_pad`/`bad_length`
   lemma family that the port dropped.

3. **Converse / canonical uniqueness** — `decode xs = some ys → encode ys = xs`
   (whenever the decoder accepts `xs`, it is the _unique_ encoding of `ys` and
   re-encodes byte-exactly). Together with roundtrip this makes `encode` and
   `decode` a partial isomorphism with `encode` injective on byte strings.

## Capabilities

### New Capabilities

- `basen`: the **complete** RFC 4648 conformance contract — per base, in
  addition to the existing roundtrip law, proved theorems that (a) the encoder
  emits only alphabet bytes with terminal-only padding, (b) the decoder rejects
  every malformed input (bad alphabet byte, illegal/non-terminal padding, wrong
  arity, trailing data after `=`), and (c) `decode xs = some ys → encode ys =
xs` (unique canonical inverse). All `[propext, Quot.sound]`-only, zero `sorry`.

### Modified Capabilities

- `basen`: strengthens the existing "decoder rejects malformed input" scenario
  (it currently enumerates only "wrong length or byte outside the alphabet"; it
  must also cover illegal padding and trailing data after `=`) over the same
  `List UInt8` substrate.

## Impact

- **Code**: `BaseN/Base32.lean` and `BaseN/Base64.lean` decode tail branches gain
  a `rest = []` guard (the one behavioural fix); the other bases' decoders should
  already reject (to be _proved_, not assumed).
- **New proofs**: three theorem families × seven bases, plus (for the facade) a
  `Base`-dispatching rejection/converse lemma. `#print axioms` stays
  `[propext, Quot.sound]` for every new law.
- **Bench**: each new rejection/converse law gets a concrete `#eval`/`example`
  vector (matching the F* reference's `decode_*_invalid` vectors), closing
  review findings 5.1, 5.7, 5.10.
- **No substrate, carrier, or axiom-discipline change**: still `List UInt8`,
  still pure Lean, still `[propext, Quot.sound]`.
