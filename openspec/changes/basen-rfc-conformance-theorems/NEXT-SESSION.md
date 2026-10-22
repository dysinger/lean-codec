# Next session — `basen-rfc-conformance-theorems` (re-anchored to the uniform surface)

Status at handoff: **2 / 19 tasks done (0.1, 0.2)**, plus a **facade-first milestone**
landed (uniform `encode`/`decode` over `List UInt8`). The deep base32/64
`Codec`-value reformulation (tasks 1.1/1.3 and everything that depends on it)
remains. Committed in `../lean-basen`; see §"Landed this session".

## The one thing every session must not re-litigate

**`many` is derived, not a constructor.** Both references agree and it is verified
un-implementable in Lean:

- Paper §3.4: `many p = nil $ pure () | cons $ p ∗ many p` — a _derived recursive
  combinator_, never an elementary description.
- F\* `Data.Codec.Types.fst`: no `many` at all — `satisfy_many0`/`count`, `let rec`
  over the finite input; `codec a` is a _record_ of `enc`/`dec`/`roundtrip`.
- Lean: `many {α} (p) (h : Productive p) : Codec (List α)` with a denotational
  `Productive`/`ConsumesByte` field hits the `Codec → witness → Rel/decode → Codec`
  cycle; the mutual-inductive escape is rejected by the universe check (`Codec :
Type → Type 1` vs `Rel : … → Prop`). This is the same wall `11f7072` hit — it was
  _right_ about the impossibility, _wrong_ to fall back to per-format run triples.

**The fix is packaging, not a core change.** `relRepeat`/`decodeRepeat`/`encodeRepeat`
(and `takeWhile`/`sepBy`) are already in `Combinators.lean`, law-bearing,
`[propext, Quot.sound]`-only. The uniform surface is a **`Run` value** (a `structure`
bundling `elem : Codec α` + `step : ConsumesByte elem`, with `decode`/`encode`/`rel`
inherited) + a facade `encode (b : Base)` / `decode (b : Base)`. No `codec`-core change,
no `Codec.rec` conversion, no bespoke per-format function.

## Landed this session (commit in `../lean-basen`)

1. **`Run α`** in `BaseN/Common.lean` (task 0.1) — generic in the element value type
   `α` (fixed-width bases have `α = UInt8`; base32/64 have `α = List UInt8` block).
   Bundles `elem : Codec α` + `step : ConsumesByte elem`; accessors `Run.decodeFull`/
   `Run.decode`/`Run.encode`/`Run.rel` inherit `decodeRepeat`/`encodeRepeat`/`relRepeat`.
2. **Uniform facade** in `BaseN.lean` (task 2.1, facade-half) — `encode (b : Base) :
List UInt8 → List UInt8` (total) and `decode (b : Base) : List UInt8 → Option
(List UInt8)`, one value type `List UInt8`, `cases b` dispatch.
3. **`B32`/`B64 ↔ List UInt8` byte transport** in `BaseN/Base32.lean`/`BaseN/Base64.lean`
   (`b32BytesOf`/`b64BytesOf`/`b32OfBytes`/`b64OfBytes` + `roundtripBytes`),
   `[propext, Quot.sound]`-only. The transport is **bijective** because the
   terminal-tail shape is recoverable from byte length `mod` the block width.
4. **`Bridge.bytesToList`/`Bridge.listToBytes`** for the fixed-width `Bytes n ↔
List UInt8` facade conversion.

`lake build` + `lake build bench` green, zero `sorry`/warnings; `#print axioms` on the
new `roundtripBytes` laws = `[propext, Quot.sound]`.

### The remaining deep work is NOT done (do not claim it is)

The facade currently **wraps the existing strict/parse base32/64 functions**
(`decodeB32Strict`/`encodeB32Strict`/`decodeB64Strict`/`encodeB64Strict`) with the
byte transport. Task 1.1 (delete those bespoke run triples) and 1.3 (re-express
base32/64 as a **`Codec` value** over the full-block `Run` + terminal-tail
`alt`/`iso` onto `B32`/`B64`) are **still open**. That is the next unit of work.

## Next implementation order (remaining §0–§5)

1. **1.1/1.3 (the hard core)** — re-express base32/64 as `Codec` values, deleting
   `parseB64`/`encodeB64Strict`/`relB64Strict`/`decodeB64Strict` (+ base32 analogues).
   The full-block element is a fresh `Codec (List UInt8)` (3 bytes ↔ 4 non-pad chars
   for base64; 5 bytes ↔ 8 non-pad chars for base32); the terminal tail is a finite
   `Codec (List UInt8)` per tail shape (`= ` positions fixed); fold onto `B32`/`B64`
   via `iso`/`alt`. The cross-byte block `Iso.law` backward directions are the hard
   part (3 shapes for base64, 5 for base32) — recoverable from the already-landed
   `b64BlockIso_law`/`b32BlockIso_law` and the `b64BlockDecodeLenient_unapply_{single,
pair,triple}` / `b32BlockDecodeLenient_unapply_{single,…,quintet}` identities
   (see `../lean-basen` commits `71aaad3`/`71aaad3` for the prior `b64Elem : Codec
(List UInt8) := iso b64BlockIso (count 4 (satisfy b64OrPad))` form to mine).
2. **1.2/1.4** — wrap the five fixed-width bases as `Run UInt8` values; their
   `roundtrip`/converse/injectivity/canonical/rejection laws already exist and
   transfer verbatim.
3. **2.2/2.3** — facade `roundtrip (b) (bs)` and `decode_encode_inverse`/
   `encode_injective` over the single `List UInt8` value type.
4. **3.x/4.x** — re-prove the three conformance families per base over the uniform
   `Codec.decode`/`Codec.encode` (rejection / canonical / converse + injectivity);
   the fixed-width halves already have these laws (`decodeFull_canonical`,
   `rejects_invalid_byte`, `rejects_lowercase`, `rejects_odd_arity`, etc.).
5. **5.x** — re-anchor `Bench.lean` to the facade (never the bespoke fns), gate
   `lake build` + `lake build bench`, `#print axioms` = `[propext, Quot.sound]`,
   `nix flake check` green; update `openspec/changes/lean-basen/` §4.1.

## Recall: the re-anchor commit and what it superseded

`lean-codec` `40e88eb` (2026-10-22) re-anchored this change to the uniform surface,
explicitly superseding the `../lean-basen` run-triple commits `bb46230` through
`1cc040e` (the strict/parse base32/64 work). Those strict functions are **still in
the tree** (re-used by the facade-first milestone) and are precisely what tasks
1.1/1.3 delete next.
