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
/ `decode : List UInt8 → Option (List UInt8)` facade anymore):

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
   illegal (non-terminal) position, wrong whole-string arity, and — the code
   fix — any data after the terminal `=` run. This restores the F* reference's
   `decode_*_invalid`/`bad_pad`/`bad_length` lemma family that the port dropped,
   re-derived over the run-level decoder.

3. **Converse / canonical uniqueness** — `decodeFull … = some ys → encode ys
reproduces the input` (whenever the decoder accepts `xs`, it is the _unique_
   canonical encoding and re-encodes byte-exactly), together with
   `encode`-injectivity on the block/list value. Combined with roundtrip this
   makes `encode` and `decode` a partial isomorphism with `encode` injective.

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
  `=`), for base32 and base64, via a run-level guard.

### Modified Capabilities

<!-- None that MODIFY an existing requirement header in the synced base spec:
     the synced `basen` spec has no "reject malformed input" / "canonical" /
     "converse" requirement to modify, so this change adds those requirements
     (see the ADDED section in specs/basen/spec.md). It does re-anchor the
     *subject* of the laws from the deleted bespoke facade to the `Codec`-value
     surface, but that is recorded here, not as a MODIFIED delta. -->

## Impact

- **Code**: the padded bases' whole-input rejection of trailing data after `=`
  requires a run-level guard (the block `iso` already rejects _intra-block_
  non-terminal `=`; the _cross-block_ case is accepted by the current code and
  must be fixed). The guard is expressed by splitting the run into a full-block
  prefix + an optional terminal tail block (using `seq`/`alt`/`empty`), or a
  whole-input post-condition theorem — see `design.md` §D3. Either is
  `Bool`-valued and constructive.
- **Base16 case-insensitivity** (RFC 4648 §8: a decoder MUST accept both cases)
  is an **explicit non-goal** of this change: the `Codec`-value `hexElem` is a
  strict uppercase bijection, and a case-insensitive decoder is not expressible
  as a strict `Iso` without breaking `Unambiguous`. Recorded, not dropped.
- **New proofs**: three theorem families × seven bases, plus (for the facade) a
  `Base`-dispatching rejection/converse lemma. `#print axioms` stays
  `[propext, Quot.sound]` for every new law.
- **Bench**: each new rejection/converse law gets a concrete `example`/`#eval`
  vector (matching the F* reference's `decode_*_invalid` vectors, re-expressed
  over `Bytes n` via a `Bytes.ofList` helper), closing review findings 5.1 and
  5.7; base16 case-insensitivity (finding 5.10) is recorded as a non-goal, not
  a passing vector.
- **No substrate, carrier, or axiom-discipline change**: still pure Lean, still
  `Bytes n` / `List UInt8` values, still `[propext, Quot.sound]`.
