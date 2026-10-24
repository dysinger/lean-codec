# Proposal

## Why

`lean-basen` proves the **roundtrip** law for all seven bases, but that is only
_half_ of RFC 4648 conformance. RFC 4648 (and this package's own spec for
base2/4/8/10) also demands that the **decoder reject** every malformed input —
wrong alphabet byte, `=` in an illegal position, wrong arity, and (for the
padded bases) any data _after_ the terminal `=` — and that the **encoder be
canonical** (its output is exactly the RFC alphabet with `=` only at the
terminal positions).

Today, on the **`Codec`-value surface** (all seven bases are now `Codec` values
over `satisfy`/`count`/`iso` + the productive repetition layer, after
`basen-uniform-leaf-api`; there is no bespoke `encode : List UInt8 → List UInt8`
/ `decode : List UInt8 → Option (List UInt8)` and — deliberately — no
`Base`-dispatching facade):

- **No rejection theorems exist.** The F* reference (`fstar-basen`) proves a
  `decode_*_invalid`/`pad_first`/`bad_length` family per base; the Lean port has
  never stated one. The decoders _mostly_ reject correctly by construction (the
  `none`/`match` branches, and the block-`iso` canonical re-encode check in
  `b32BlockApply`/`b64BlockApply`), but that is asserted by construction, never
  proved, and is **not** covered by the gate.
- **Terminal-padding rejection is not established at the run level.** The
  padded bases' element accepts `=` in `b32OrPad`/`b64OrPad` and delegates
  canonicality to the block `iso` (`b64BlockUnapply bs = some cs`). That rejects
  `=` in a _non-terminal position within a block_ (e.g. `Z=g` is not a valid
  4-char block), but the **run-level** case — data after a terminal `=` run,
  e.g. the two-block input `"Zg==" · "AAAA"` where the first block's `=` is
  terminal but a second alphabet-valid block follows — is **accepted by the
  current code** (`decodeFull b64Elem … "Zg==AAAA" = some […]`, because
  `count 4 (satisfy b64OrPad)` fixes the _byte window_, not the value length).
  This is the RFC 4648 §3.2 requirement restated at the run level, and it needs
  a code guard, not just a theorem.
- **No converse / canonical-uniqueness law.** `decode xs = some ys → encode ys
= xs` is never stated, so nothing proves the encoding is unique (that a single
  byte string has exactly one valid RFC 4648 representation, i.e. that pad
  placement and alphabet choice are forced).

The goal is to make this the **most correct base-`N` package available**: not
just "roundtrips hold" but "the decoder is a _total characterization_ of the
RFC — `decode` succeeds exactly on the RFC-valid inputs and `encode` is the
unique inverse."

## What Changes

Add three families of theorems per base (proved `[propext, Quot.sound]`-only,
zero `sorry`), expressed over the **`Codec`-value surface** — the whole-input
decoder is the existing `Codec.decodeFull {x}Elem {x}ConsumesByte`, and the
encoder is `encode{X}`/`encodeB{X}` — plus the one decoder fix they expose:

1. **Canonical encoding** — every encoded byte is in the alphabet
   (`encode`-soundness); for base32/64, `=` appears only in the terminal pad
   positions and the pad count is exactly the RFC §6.7/§4.7 arity for the
   input block's length.

2. **Decode totality (rejection)** — `Codec.decodeFull … = none` on every
   malformed input: a byte outside the alphabet (base16: outside the uppercase
   canonical alphabet — see the case-insensitivity non-goal below), `=` in an
   illegal (non-terminal) position, wrong whole-string arity, and — the type
   fix — any data after the terminal `=` run. For base32/64, the value type is
   changed to the terminal-tail inductive `B32`/`B64`, so the malformed class is
   _unrepresentable_ (there is no term for "tail then more data"); rejection is
   the absence of an inhabitant, not a post-hoc filter. This restores the F*
   reference's `decode_*_invalid`/`bad_pad`/`bad_length` lemma family.

3. **Converse / canonical uniqueness** — `decodeFull … = some v → encode v
reproduces the input` (whenever the decoder accepts a value, it is the _unique_
   canonical encoding and re-encodes byte-exactly), together with
   `encode`-injectivity on the value. Combined with roundtrip this makes
   `encode` and `decode` a partial isomorphism with `encode` injective.

## Capabilities

### New Capabilities

- `basen`: the **complete** RFC 4648 conformance contract — per base, in
  addition to the existing roundtrip law, proved theorems that (a) the encoder
  emits only alphabet bytes with terminal-only padding, (b) the whole-input
  decoder rejects every malformed input (bad alphabet byte, illegal/non-terminal
  padding, wrong arity, trailing data after `=`), and (c)
  `decodeFull … = some ys → encode ys` reproduces the input (unique canonical
  inverse) and `encode` is injective. All `[propext, Quot.sound]`-only, zero
  `sorry`, over the `Codec`-value / `Bytes n` substrate.
- `basen`: proves the **run-level terminal-padding** property the block-`iso`
  canonical check does not cover (RFC 4648 §3.2: no data after the terminal
  `=`), for base32 and base64, by **making the shape unrepresentable**: the
  value type is the terminal-tail inductive `B32`/`B64`, so there is no term
  for a tail followed by data.

### Modified Capabilities

- `codec`: ADD a requirement re-asserting that `many` is **derived** (never a
  `Codec` constructor — a constructor is un-implementable in Lean), and that a
  concrete format surfaces unbounded repetition as a **first-class run value**
  (bundling `relRepeat`/`decodeRepeat`/`encodeRepeat`) so the uniform
  `decode`/`encode` keeps no bespoke per-format function (see `specs/codec/spec.md`).

## Impact

- **Code**: the padded bases' whole-input rejection of trailing data after `=`
  is fixed by **re-typing**: `List (List UInt8)` is replaced by the terminal-tail
  inductive `B32`/`B64` (design §D3), reached by `iso` **after** a composition of
  the full-block `Run` (derived `many`) and the finite terminal-tail `Codec` —
  **not** a single `Codec (List UInt8)` value and **not** a hand-rolled run triple
  (there is no repetition node in the `Codec` AST, so no unbounded whole-input
  description exists). Unbounded repetition is the **derived** `many`
  (`relRepeat`/`decodeRepeat`/`encodeRepeat`, design §D0) — **never** a `many`
  constructor (un-implementable, per the verified universe/definition-order
  cycle). The whole-input roundtrip is the inherited per-component laws plus one
  named block-run/tail split-uniqueness lemma (design §D7). Rejection is
  **structural** (the illegal shape has no inhabitant), there is no flattening
  (no bijective `B64 → List (List UInt8)` exists), and the lenient
  `List (List UInt8)` codecs are deleted.
- **Base16 case-insensitivity** (RFC 4648 §8: a decoder MUST accept both cases)
  is an **explicit non-goal** of this change: the `Codec`-value `hexElem` is a
  strict uppercase bijection, and a case-insensitive decoder is not expressible
  as a strict `Iso` without breaking `Unambiguous`. Recorded, not dropped.
- **New proofs**: three theorem families × seven bases, each stated over the
  base's own `Codec`/`Run` value (no facade, no `Base`-dispatching lemma).
  `#print axioms` stays
  `[propext, Quot.sound]` for every new law.
- **Bench**: each new rejection/converse law gets a concrete `example`/`#eval`
  vector (matching the F* reference's `decode_*_invalid` vectors, re-expressed
  over `Bytes n` via a `Bytes.ofList` helper), closing review findings 5.1 and
  5.7; base16 case-insensitivity (finding 5.10) is recorded as a non-goal, not
  a passing vector.
- **No substrate, carrier, or axiom-discipline change**: still pure Lean, still
  `Bytes n` / `List UInt8` values, still `[propext, Quot.sound]`.
