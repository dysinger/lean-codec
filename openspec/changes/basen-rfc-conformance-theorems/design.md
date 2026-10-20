# Design

## Context

See `proposal.md` — Why. The `basen` package proves roundtrip for all seven
bases on the **`Codec`-value surface** (after `basen-uniform-leaf-api`), but
nothing is proved about _rejection_, _canonical form_, or the _converse_, and
the padded decoders' **run-level** terminal-padding behaviour is unproved. The
F* reference (`fstar-basen`) that this package ports from proves a
`decode_*_invalid`/`pad_first`/`bad_length` rejection family per base; the Lean
port has never stated one.

### The actual surface (read this before any statement)

Each base is a `Codec` value over `satisfy`/`count`/`iso` plus the productive
repetition layer. Everything is indexed by the `codec` substrate `Bytes n :=
Fin n → UInt8`.

Two groups:

- **Fixed-width bases (2, 4, 8, 10, 16):** element is `Codec UInt8`; the run
  triple is `decode{X} : Bytes n → List (List UInt8 × Suffix n)`,
  `encode{X} : List UInt8 → Option (Sigma fun n => Bytes n)`, and
  `roundtrip (bs : List UInt8) {n : Nat} {s : Bytes n}`. The whole-input
  decoder is `Codec.decodeFull {x}Elem {x}ConsumesByte n s : Option (List UInt8)`.
- **Block bases (32, 64):** element is `Codec (List UInt8)` (a 5-byte / 3-byte
  block). The run triple is `decodeB32`/`decodeB64 :
Bytes n → List (List (List UInt8) × Suffix n)`,
  `encodeB32`/`encodeB64 : List (List UInt8) → Option (Sigma fun n => Bytes n)`,
  and `roundtrip (bs : List (List UInt8))`. The whole-input decoder is
  `Codec.decodeFull b32Elem b32ConsumesByte n s : Option (List (List UInt8))`
  (and the base64 analogue).

There is **no** `encode : List UInt8 → List UInt8` / `decode : List UInt8 →
Option (List UInt8)` facade anymore — that was deleted in
`basen-uniform-leaf-api`. All conformance statements are expressed with
`Codec.decodeFull` (the existing whole-input decoder from `codec`) and the
`encode{X}`/`encodeB{X}` encoders over `Bytes n`.

### What is already proved (do not re-prove)

- Per-base **roundtrip** (`decodeFull (encode bs) = some bs`), all
  `[propext, Quot.sound]`-only.
- Per-base **unambiguity** (`{x}DecodeFull_unambiguous`), used as the
  full-consumption uniqueness hypothesis by `Codec.decodeFull_spec`.
- The **block `iso` canonical check**: `b32BlockApply`/`b64BlockApply` (and the
  fixed-width `{x}BlockApply`) already reject a block whose characters do not
  re-encode to themselves (`b32BlockUnapply bs = some cs`), so _intra-block_
  canonicality — including `=` in a non-terminal position within a block — is
  enforced by construction inside the element.

What is **not** proved, and is this change's work, is the _whole-input_ layer
above the element: alphabet-soundness of the encoder output, the run-level
rejection classes, and the converse/injectivity. **Base16 case-insensitivity is
explicitly out of scope** (see D8): the shipped `hexElem` is a strict
uppercase bijection, and a lowercase-accepting decoder is _not_ a `Codec` value
over a strict `Iso` — see the non-goals.

### Ground truth the plan must respect (verified against shipped code)

- `b64Elem = Codec.iso b64BlockIso (count 4 (Codec.satisfy b64OrPad))` where
  `b64OrPad b = b64Valid b.toNat || b.toNat = 61`. The `count 4` window is a
  **fixed 4-byte** consumption: padding shortens the _decoded value_ (1/2/3
  bytes), it does **not** shorten the _byte window_ (still 4). A 2-char `==`
  block and a 4-char block both consume 4 input bytes.
- Therefore `decodeFull b64Elem b64ConsumesByte 8 ["Zg==AAAA"]` is `some
[f, 0, 0, 0]` — the trailing-data-after-terminal-`=` case is **accepted by the
  current code, deterministically**, not an empirical unknown.

This grounds D3 (the guard is mandatory) and D4 (the rejection lemma for this
class must be proved _after_ the guard is in place, not by a consumption-length
argument that does not hold).

## Goals / Non-Goals

**Goals:**

- Three theorem families per base, `[propext, Quot.sound]`-only, zero `sorry`:
  1. **Canonical encoding** (alphabet-only output; terminal-only padding at the
     whole-input level).
  2. **Decode totality** (reject every malformed input class at the
     `decodeFull` level).
  3. **Converse / uniqueness** (`decodeFull … = some ys` reproduces the input
     under `encode`; `encode` injective on its value).
- The one decoder property they expose — **run-level terminal padding** (RFC
  4648 §3.2: a `=` appears only at the very end of the whole input, never
  followed by another block) — is **accepted by the current code** (see the
  ground-truth note), so a code fix is **mandatory**, and the proof comes after.
- Bench-lane vectors closing review findings 5.1, 5.7, 5.10.

**Non-Goals:**

- No substrate/carrier change (`Bytes n` and `List UInt8` stay).
- No C seam, no `Classical.choice`, no `sorry`, no new axioms.
- **No new `Codec` constructor** for the padding guard — express it with the
  existing `seq`/`alt`/`empty`/`satisfy`/`iso`/`count`/`decodeRepeat`
  combinators, or as a whole-input post-condition theorem (see D3).
- **Base16 case-insensitivity is out of scope** (D8): the `Codec`-value
  `hexElem` is uppercase-only by design, and widening it to accept lowercase
  would break the strict block `Iso`/`Unambiguous` as currently stated.
- No change to base2/4/8/10 _semantics_ (their own spec; just the same
  rejection/canonical _discipline_).
- No re-proving the block-level `iso` laws or the roundtrip/unambiguity laws —
  those are done.

## Decisions

### D1 — Express "decode" as `Codec.decodeFull`, not a new facade

The subject of every rejection/converse theorem is the **whole-input decoder**
`Codec.decodeFull {x}Elem {x}ConsumesByte n s`, for `x` ∈
{`bit`, `quartet`, `oct`, `dig`, `hex`} over `List UInt8` result and
{`b32`, `b64`} over `List (List UInt8)` result. "`decode xs = none`" is stated
as `Codec.decodeFull … (Bytes.ofList xs) = none`; "`decode xs = some ys`" as
`Codec.decodeFull … s = some ys`. We do **not** introduce a fresh
`decode : List UInt8 → Option (List UInt8)` facade; `decodeFull` already
coincides with the old whole-input semantics (it requires the full suffix to be
consumed), and it is the law-governed surface (`Codec.decodeFull_spec`).

Rationale: keep one decoder surface (the proved one), and avoid re-introducing
the deleted bespoke facade this change-chain just removed.

### D2 — Three theorem families, not one "full characterization" mega-lemma

Per base, add:

- **Canonical encoding** — for the fixed-width bases, `encode{X}` output is
  alphabet-only (each byte satisfies the digit predicate); for base32/64,
  `encodeB{X}` output is alphabet-or-pad, with the pad run terminal and of
  exactly the RFC arity for the block length. Formally: for base64, a block of
  length 1 encodes to `2 chars + "=="`, length 2 to `3 chars + "="`, length 3
  to `4 chars` (no `=`), and `=` never precedes a non-`=` in the whole output.
- **Rejection** — one `theorem` per class (`decodeFull … = none`): alphabet
  rejection (byte outside the alphabet), pad-position rejection (`=` where a
  data char is required), arity rejection (whole-input byte count not a whole
  number of code words), overflow rejection (base8/10 digit triple `> 255`),
  and — the new one — **run-level trailing-data rejection** (a `=`-terminated
  block followed by any further data), for the padded bases.
- **Converse / uniqueness** — `decodeFull … = some ys → encode ys = input`
  (canonical inverse) and `encode bs = encode bs' → bs = bs'` (injectivity).

Rationale: three focused families mirror the F* reference, keep each proof
simple, and let the bench lane value-check each class independently. A single
exhaustive "decode valid iff canonical" iff-theorem is assembled from these
families, not proved as one induction.

### D3 — The padded base fix is a **mandatory** run-level guard, not `rest = []`

The historical (`basen-uniform-leaf-api`-era) plan was to add `rest = []` to the
old bespoke `decodeN`/`decode` tail branches. **That code is gone.** The current
padded element is `{b32,b64}Elem = iso {b32,b64}BlockIso (count {8,4}
(satisfy {b32,b64}OrPad))`, and `decodeFull`/`decodeB32`/`decodeB64` run
`decodeRepeat {b32,b64}Elem …` over fixed-width windows.

The block `iso` already rejects `=` in a non-terminal _intra-block_ position.
The **run-level** case — a `=`-terminated block _followed by another_ block — is
**accepted by the current code** (verified: `decodeFull b64Elem … "Zg==AAAA" =
some […]`), because `count 4 (satisfy b64OrPad)` fixes the _byte window_ (4),
not the _value length_. A guard is therefore **required**, not optional.

**How the guard is expressed (this is the key design decision, resolved here):**
the terminal-pad property is a _list-decomposition_ fact — a decoded
`List (List UInt8)` must have shape `[full, full, …, full, tail]` where at most
the **last** block may be padded and a padded block may not be followed by
anything. Two acceptable mechanisms, in order of preference:

1. **Restructure the block run** (preferred, no new constructor): express the
   base32/64 whole-string codec as `many fullBlock` then _at most one_ `tailBlock`
   — i.e. split the padded base into a **full-block element** (5 bytes → 8 chars /
   3 bytes → 4 chars, no `=`) decoded by `decodeRepeat`, followed by an **optional
   tail block** (the 1–4-byte / 1–2-byte tails) expressed with the existing
   `alt`/`seq`/`empty` combinators. This makes "no data after `=`" structural:
   a tail block only ever appears at the end by construction. The value type
   becomes a two-part result (`List (List UInt8) × Option (List UInt8)` or a
   flattened equivalent), so the roundtrip/converse statements are re-phrased;
   the element-level `iso` laws and unambiguity transfers unchanged to each part.
2. **Whole-input post-condition theorem** (only if 1 is too invasive): keep
   `b32Elem`/`b64Elem` as-is and prove a _theorem_ that `decodeFull` returns
   `none` whenever the input decomposes into a padded block followed by data.
   This does **not** change `decodeFull`'s semantics; it refutes the
   trailing-data input after the fact. It preserves the current value type and
   roundtrip, but is a heavier invariant to state and prove (it must reason about
   the `decodeRepeat`/`decodeFull` fixpoint directly).

Either way the guard is **`Bool`-valued** (a decidable predicate on the decoded
list / input), never a `Prop` quantified over `∀ (i : Fin k), …`, so the
rejection proofs stay constructive (`[propext, Quot.sound]`-only, no
`Classical.choice` — see the `lean` skill's `by_contra` prohibition). Roundtrip
is unaffected under mechanism 1 (the encoder emits pad only terminally) and
unchanged under mechanism 2.

### D4 — Rejection proofs reduce to the block `iso` laws + `decodeFull` induction

Because each alphabet is a finite byte set and each rejection class is a
decidable `if`/`match` guard, the rejection theorems reduce to unfolding
`Codec.decodeFull`/`decodeRepeat` and discharging with `decide`/`omega`, reusing
the already-proved `{x}ToVal_valTo{X}`/`valTo{X}_valid`/`valTo{X}_not_pad`
facts and the block `iso` laws. The run-level _trailing-data_ class is proved
**after** the D3 guard is in place: the guard makes the malformed class
structurally rejected, and the theorem is then an unfold of `decodeFull` (for
mechanism 1, the tail block simply cannot consume trailing data; for mechanism
2, the post-condition theorem _is_ the proof).

### D5 — Converse and injectivity follow from roundtrip + unambiguity (+ `Rel` induction)

`decodeFull s = some ys → encode ys = ⟨_, s⟩`: use `Codec.decodeFull_spec` with
the already-proved `{x}DecodeFull_unambiguous` (which gives the uniqueness
hypothesis `decodeFull_spec` needs) to get `relRepeat (Rel {x}Elem) ys s`, then
`encodeRepeat_rel` to get `encode ys = some ⟨n, s⟩`. Note the intermediate
step is **element-level `Rel` induction**: `encodeRepeat_rel` needs
`Rel`-level facts about each element (`encode p x = some t → Rel p x t`), which
follow from the existing `encode_rel`/`Rel_iso`/`Rel_count_satisfy` lemmas — so
this is provable but carries more `Rel`-bridge steps than a one-line chain
(`relRepeat_cast`/`relRepeat_cons`/`Rel_iso`) suggests. `encode`-injectivity is
the companion: `encode bs = encode bs'`, apply roundtrip to both sides to get
`decodeFull (encode bs) = some bs = some bs'`, then `Option.some.inj` /
`{x}DecodeFull_unambiguous` to conclude `bs = bs'`.

### D6 — Proofs live next to the existing per-base code (no new module)

Each base keeps its own `*ToVal_valTo*`/`valTo{X}_valid`/`valTo{X}_not_pad`
helper style; the three new families are added to the same `BaseN.BaseX`
namespace. The facade `BaseN` currently has **no `roundtrip` dispatch theorem**
(only the `inductive Base` + module re-exports), so the `Base`-indexed
`encode_injective`/`decode_rejects`/`decode_encode_inverse` dispatch added here
is **net-new**, written per result shape (`List UInt8` vs `List (List UInt8)`)
and `cases`-ed over `Base`. No new module, no new import surface.

### D7 — Bench lane value-checks every new law with concrete vectors

`Bench.lean` gains, per base, an `example`/`#eval` for each rejection class and
the converse, using the F* reference's concrete vectors (base64 invalid `!`,
pad-first, bad-length, `Zg==AAAA` trailing-data; base32 `MY======AAAAAAAA`;
base8/10 overflow triples) — each re-expressed as a `Bytes n` literal via an
explicit `Bytes.ofList`-style helper (a new, tiny helper; see task 5.1). This
closes 5.1 (non-terminal padding) and 5.7 (smoke subset). **Base16 lowercase
`6f` is _not_ a vector here** (it is out of scope per D8); 5.10 is closed by an
explicit **non-goal note** rather than a passing vector.

### D8 — Base16 case-insensitivity is out of scope

RFC 4648 §8 says a base16 _decoder_ MUST accept both cases, but the shipped
`hexElem` is a strict **uppercase** `Iso` (`hexToNibble` returns `16` for
`a`–`f`), and a lowercase-accepting decoder is _deliberately not_ part of the
`Codec` value (its module header states this). Making it case-insensitive would
require a `satisfy` + _normalizing_ `iso` that is **not a bijection** (two
inputs `A`/`a` map to one nibble), which breaks the strict block `Iso.law` and
`Unambiguous` as currently stated. This change therefore **does not** add a
lowercase `6f` vector or a case-insensitivity theorem; it records the
case-insensitivity as an explicit non-goal and re-scopes the base16 rejection
vectors to the uppercase canonical alphabet. (A future change could add a
separate case-normalizing _facade_ decoder outside the `Codec` value, but that
is not this change's job.)

## Risks / Trade-offs

- **[The run-level terminal-pad guard is the single highest-risk item]** → the
  mechanism (D3) must be settled _before_ the rejection/canonical theorems that
  depend on it. Mechanism 1 (split full-block run + optional tail) is preferred
  but changes the value type and re-phrases roundtrip/converse; mechanism 2
  (post-condition theorem) preserves the value type but is a heavier
  `decodeFull`-fixpoint invariant. Both are `Bool`-valued and constructive.
- **[Exhaustive "valid iff canonical" iff-theorem is large]** → target it as the
  _sum_ of the three families (D2), not a single monster induction.
- **[Two result shapes (`List UInt8` vs `List (List UInt8)`)]** → the facade
  `Base`-dispatched converse/injectivity must handle both; write the dispatch
  per shape and `cases` over `Base`, not a single polymorphic statement.
- **[Base16 case-insensitivity is a deliberate gap vs RFC §8]** → recorded as an
  explicit non-goal (D8), not silently dropped; the rejection vectors are
  uppercase-only.
- **[Overlapping with the existing open review tasks 5.1/5.7/5.10]** → this
  change _implements_ 5.1/5.7 (re-anchored to the Codec-value surface) and
  records 5.10 as a non-goal; the other 5.x polish items remain open in the
  `lean-basen` change.

## Migration Plan

1. Re-anchor the `basen` spec delta and the `lean-basen` task ledger to the
   `Codec`-value surface (this change's own spec delta does it; the `lean-basen`
   ledger's "spit-shine" plan is marked superseded).
2. **Resolve the D3 guard mechanism** for base32/64 (full-block-run + optional
   tail, or post-condition theorem). This is the very first implementation
   decision; settle it before any theorem depends on it.
3. Implement the guard; re-prove base32/64 roundtrip if mechanism 1 changes the
   value type, then prove the run-level terminal-padding rejection theorem.
4. Add canonical-encoding theorems per base (alphabet + terminal pad).
5. Add rejection theorems per base (restore the F* `decode_*_invalid` family
   over `decodeFull`).
6. Add converse + injectivity theorems per base, and the net-new `Base`-dispatched
   facade versions.
7. Extend `Bench.lean` with rejection/canonical/converse vectors (including a
   `Bytes.ofList` helper); gate with `lake build` (zero sorry/warnings),
   `#print axioms` = `[propext, Quot.sound]`, `nix flake check` green.

## Open Questions

- **D3 mechanism (full-block+tail vs post-condition)** is the one real design
  fork; it is decided at implementation time (step 2) based on how invasive the
  value-type change is for the facade/converse proofs. Everything else is pinned:
  the RFC rules are in `rfc4648.md`; base2/4/8/10 semantics are this package's own
  spec. Base16 case-insensitivity is a recorded non-goal (D8), not an open question.
