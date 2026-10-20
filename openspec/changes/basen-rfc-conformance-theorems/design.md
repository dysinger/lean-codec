# Design

## Context

See `proposal.md` — Why. The `basen` package proves roundtrip for all seven
bases on the **`Codec`-value surface** (after `basen-uniform-leaf-api`), but
nothing is proved about _rejection_, _canonical form_, or the _converse_, and
the padded decoders' **run-level** terminal-padding behaviour is unproved. The
F* reference (`fstar-basen`) that this package ports from proves a
`decode_*_invalid`/`pad_first`/`bad_length` rejection family per base; the Lean
port has never stated one.

This change goes further than "prove rejection": it **replaces the base32/64
value type** so that the forbidden shape (a `=`-terminated block followed by
more data) is **not representable at all**, rather than rejected by a rule.

## The core idea: the value type must make illegal states _unrepresentable_

The current base32/64 value type is `List (List UInt8)` — a loose "list of
blocks". It is exactly the wrong type: it can hold `[[0x66], [0, 0, 0]]` (a
1-byte tail followed by a 3-byte full block) with no type-level objection. RFC
4648 §3.2 forbids this (`=` is terminal), so `List (List UInt8)` **admits an
illegal state by construction**. No guard, filter, or post-condition over that
type can be "perfect" — they all _detect and discard_ an already-constructed
illegal value.

The perfect fix is a **value type where the forbidden shape cannot be written**.
Base32/64 get an inductive value type whose _tail_ constructors are terminal
(no continuation field), so "data after a tail" has no term:

```lean
-- base64: full 3-byte blocks, then at most one terminal tail of 1 or 2 bytes
inductive B64 where
  | empty
  | full  (b0 b1 b2 : UInt8) (rest : B64)   -- a full block, then more
  | tail1 (b0 : UInt8)                       -- terminal 1-byte tail
  | tail2 (b0 b1 : UInt8)                    -- terminal 2-byte tail

-- base32: full 5-byte blocks, then at most one terminal tail of 1–4 bytes
inductive B32 where
  | empty
  | full  (b0 b1 b2 b3 b4 : UInt8) (rest : B32)
  | tail1 (b0 : UInt8) | tail2 (b0 b1 : UInt8)
  | tail3 (b0 b1 b2 : UInt8) | tail4 (b0 b1 b2 b3 : UInt8)
```

Because `tail1`/`tail2` have no destination, the _only_ way to represent "a
1-byte block then a 3-byte block" is `full 0 0 0 (tail1 0x66)` — the **valid**
ordering. `Zg==AAAA` (`[[0x66],[0,0,0]]`) has **no inhabitant** in `B64`. This
is "types and theorems dictate impossibility": the decoder's type
`Bytes n → Option B64` makes malformed input return `none` (nothing to invent),
and every `some v : B64` _is_ canonical by construction.

### The actual surface (read this before any statement)

Each base is a `Codec` value over `satisfy`/`count`/`iso` plus the productive
repetition layer, indexed by the `codec` substrate `Bytes n := Fin n → UInt8`.
After this change the bases split into **three** groups by value type:

- **Fixed-width bases (2, 4, 8, 10, 16):** element `Codec UInt8` (one byte per
  element); the run triple `decode{X} : Bytes n → List (List UInt8 × Suffix n)`,
  `encode{X} : List UInt8 → Option (Sigma fun n => Bytes n)`, `roundtrip
(bs : List UInt8)`, whole-input decoder `Codec.decodeFull {x}Elem
{x}ConsumesByte n s : Option (List UInt8)`. These are **unchanged** — `List
UInt8` is their right type and they have no padding/tail concept.
- **Base64:** **new value type `B64`** (above). The strict run triple
  `relB64Strict : B64 → {n} → Bytes n → Prop`,
  `decodeB64Strict : Bytes n → Option B64`,
  `encodeB64Strict : B64 → Option (Sigma fun n => Bytes n)`. The old
  `b64Elem : Codec (List UInt8)` / `decodeB64` / `encodeB64` / `relB64` are
  **deleted** (together with the `bb46230` post-hoc filter).
- **Base32:** **new value type `B32`** (above), with the analogous
  `relB32Strict`/`decodeB32Strict`/`encodeB32Strict`; the old lenient
  `b32Elem`/`decodeB32`/`encodeB32`/`relB32` are **deleted**.

There is **no** `encode : List UInt8 → List UInt8` / `decode : List UInt8 →
Option (List UInt8)` facade anymore (deleted in `basen-uniform-leaf-api`), and
nobody re-introduces one. The strict base32/64 codecs are **run triples** (the
`sepBy`/`takeWhile` pattern), **not** `Codec` values — unbounded `many` is not
an AST node, and a padded block run is not a fixed-width `count k (satisfy p)`.

### Ground truth the plan must respect (verified against shipped code)

- The current `b64Elem = Codec.iso b64BlockIso (count 4 (Codec.satisfy
b64OrPad))` with `b64OrPad b = b64Valid b.toNat || b.toNat = 61`. `count 4`
  fixes the **byte window**, not the decoded value length, so
  `decodeFull b64Elem b64ConsumesByte 8 "Zg==AAAA"` is `some [[0x66],[0,0,0]]`
  — the trailing-data-after-terminal-`=` case is **accepted deterministically**,
  because the value type `List (List UInt8)` cannot forbid it. This grounds the
  type replacement: the fix is not a guard on this type, it is a better type.
- Fixed-width roundtrips and unambiguities are `[propext, Quot.sound]`-proved
  and are **not** re-proved.

## Goals / Non-Goals

**Goals:**

- Replace base32/64's `List (List UInt8)` value with the terminal-tail
  inductive `B32`/`B64`, so **illegal states are unrepresentable**.
- Three theorem families per base, `[propext, Quot.sound]`-only, zero `sorry`:
  1. **Canonical encoding** — every encoded byte is in the alphabet; for
     base32/64 the `=` pads are exactly the RFC arity of the (unique) terminal
     tail, and appear nowhere else.
  2. **Rejection** — `decode… = none` on every malformed input.
  3. **Converse / uniqueness** — `decode = some v → encode v = input`, and
     `encode` injective.
- For base32/64 the rejection is **structural**: malformed input → `none`
  because **no `B32`/`B64` term** represents it, proved by showing the grammar
  relation has no inhabiting value (not by a filter or a `Bool` test).

**Non-Goals:**

- No substrate change (`Bytes n` stays); no C seam, no `Classical.choice`, no
  `sorry`, no new axioms.
- **No new `Codec` constructor.** The strict base32/64 run is a _run triple_
  (`relStrict`/`decodeStrict`/`encodeStrict`), not a `Codec` value.
- **No flattening.** There is no map `B64 → List (List UInt8)` that is a
  bijective `Iso` (a tail can't be distinguished from a full block after the
  fact). The flat type is simply **gone** for base32/64.
- **Base16 case-insensitivity is out of scope** (D8): `hexElem` is a strict
  uppercase bijection.

## Decisions

### D0 — Replace the base32/64 value type with a terminal-tail inductive (the whole fix)

`List (List UInt8)` admits `[[0x66],[0,0,0]]`; `B64`/`B32` above do not. This is
the single change that makes illegal states impossible, and it subsumes every
prior "guard mechanism" (split grammar, post-condition, filter) — there is no
guard, there is a **type**. It is the honest realization of "perfection": the
compiler itself rejects the illegal shape.

### D1 — The strict base32/64 codec is a run triple, not a `Codec` value

Because a padded block run is `full* (tail)?` and unbounded `many` is not a
`Codec` AST node (see the `lean` skill §3), the strict decoder/encoder are a
**run triple** exactly like `relSepBy`/`decodeSepBy`/`encodeSepBy` and
`relTakeWhile`/`decodeTakeWhile`/`encodeTakeWhile`:

- `relB64Strict : B64 → {n : Nat} → Bytes n → Prop` — structural recursion with
  **no** separate "terminal-pad" predicate (the shape is in the value).
- `decodeB64Strict {n} (s : Bytes n) : Option B64` — returns `none` unless `s`
  is a canonical base64 string; driven by the result type's constructors.
- `encodeB64Strict (v : B64) : Option (Sigma fun n => Bytes n)` — a structural
  fold; canonical output _forced_ by the input type.

(The `decodeB32Strict`/`encodeB32Strict`/`relB32Strict` analogues similarly.)

### D2 — The block `Iso`s are arity-fixed and `=`-free on the full block

Each block shape is a **genuine bijection** at a fixed arity (no `b64OrPad`
leniency, no `=`-accepting full block):

- base64 full: `Iso (UInt8 × UInt8 × UInt8) (List UInt8)` — 3 bytes ↔ 4
  alphabet chars (no `=`).
- base64 tail1: `Iso UInt8 (List UInt8)` — 1 byte ↔ `2 chars + "=="`.
- base64 tail2: `Iso (UInt8 × UInt8) (List UInt8)` — 2 bytes ↔ `3 chars + "="`.
- base32 full/tail1..tail4 analogously (5 bytes ↔ 8 chars; `n` bytes ↔ `1+⌈8n/5⌉`
  chars + pad).

These are _restrictions_ of the existing `b64BlockUnapply`/`b64BlockApply` (the
digit math and the `byte0..byte4` extraction identities are reused verbatim);
the `=` is part of the tail `Iso`'s output so it cannot leak into a full block
or a non-terminal position. Each has its `law` proved by the existing per-shape
`b64BlockDecodeLenient_unapply_*` forward identities plus the reverse
`*ToVal_valTo*` reconstruction (the already-proved `b64ToVal_valToB64`/
`valToB64_b64ToVal_of_valid` facts).

### D3 — Rejection is proved by _absence of an inhabitant_, with the decode derived

`decodeB64Strict ("Zg==AAAA" : Bytes 8) = none` is proved by showing there is
**no** `v : B64` with `relB64Strict v (bytes 8)` consuming all 8 bytes. That is
a **type-directed** argument: the only `B64` terms consuming 8 chars are
`full … (empty)` (one block) or `full … (full … ·)` (two blocks) etc.; the
`Zg==` prefix can only be matched by `tail1 0x66` (terminal), which leaves
`AAAA` unconsumed — so no term exists. Mechanically this descends through
`decodeFull_spec` + the run's own relation lemmas + `encode_rel` + a single
forward **`rel_count_satisfy`** lemma (proved once in `BaseN.Common`, see D5),
so the per-block `Rel` facts are obtained from the _encoder_, never assumed.
No `native_decide`, no `hf` hypothesis, no `Classical.choice`.

### D4 — Three theorem families, not one mega-lemma

Per base add (all `[propext, Quot.sound]`-only):

- **Canonical encoding** — fixed-width: `encode{X}` output is alphabet-only;
  base32/64: `encodeStrict` output is alphabet-or-pad with the pad exactly the
  terminal tail's RFC arity.
- **Rejection** — one `theorem` per malformed class (`decode… = none`).
- **Converse / uniqueness** — `decode = some v → encode v = input`, and
  `encode` injective.

The exhaustive "valid iff canonical" iff is the **sum** of these families, not a
single induction.

### D5 — The one new generic lemma: forward `rel_count_satisfy`

Every concrete rejection/canonical/converse proof needs a **forward**
`Rel (count k (satisfy p)) l s` fact from `s = byte-image of l` plus
`∀ b ∈ l, p b`. This is the single missing primitive (the backward
`decodeRepeat_spec`/`relRepeat` direction exists); prove it once in
`BaseN.Common`, parameterized by `p` and `k`, and reuse for all seven bases.
(It carries the `(k+1)-1 = k` length-cast gotcha documented in the `lean` skill.)

### D6 — Proofs live next to the per-base code (no new module)

The fixed-width families stay in their `BaseN.BaseX` namespaces; `B32`/`B64` and
their strict run triples + theorems live in `BaseN.Base32`/`BaseN.Base64`. The
facade `BaseN` (currently no dispatch theorem) gains **net-new** `Base`-indexed
`encode_injective`/`decode_rejects`/`decode_encode_inverse` dispatch, written per
shape and `cases`-ed over `Base` (three shapes: `List UInt8`, `B32`, `B64`).

### D7 — Bench lane value-checks every law with concrete vectors

`Bench.lean` gains, per base, an `example`/`#eval` for each rejection class and
the converse, using the F* vectors (base64 `!`, pad-first, bad-length,
`Zg==AAAA`; base32 `MY======AAAAAAAA`; base8/10 overflow), each re-expressed as
a `Bytes n` literal via a `Bytes.ofList` helper.

### D8 — Base16 case-insensitivity is out of scope

RFC 4648 §8 wants a _decoder_ to accept both cases, but `hexElem` is a strict
uppercase `Iso`; a case-insensitive decoder is not a bijection and is recorded
as a non-goal (lowercase `6f` is a _rejection_, not an accepted alias).

## Risks / Trade-offs

- **[Public type change is the entire point]** → base32/64 value type changes
  from `List (List UInt8)` to `B32`/`B64`; this is deliberate (illegal states
  unrepresentable), and the facade/bench adapt (three shapes). No silent
  backward-compat shim: the lenient codecs are deleted.
- **[Base32 5-shape / base64 3-shape block `Iso` laws]** → each tail arity
  needs its own bijection law; reuse the existing digit identities read
  forward and in reverse (do not use `by_contra`).
- **[Three result shapes]** → the facade dispatch handles `List UInt8`, `B32`,
  `B64` separately.
- **[Base16 case-insensitivity]** → recorded as a non-goal (D8).

## Migration Plan

1. Delete the lenient base32/64 codecs and the `bb46230` filter (revert to the
   pre-filter state, then remove `b32Elem`/`b64Elem`/`decodeB*`/`encodeB*`/
   `relB*`).
2. Define `B32`/`B64` and the arity-fixed block `Iso`s (D2).
3. Implement the strict run triples `relStrict`/`decodeStrict`/`encodeStrict`
   over `B32`/`B64` (D1).
4. Prove rejection (`Zg==AAAA` etc. → `none`) with the decode derived (D3);
   prove strict roundtrip + unambiguity + converse + injectivity.
5. Add canonical/rejection/converse theorems per fixed-width base (D4).
6. Add the net-new `Base`-dispatched facade versions (D6).
7. Extend `Bench.lean` (D7); gate with `lake build` (zero sorry/warnings),
   `#print axioms` = `[propext, Quot.sound]`, `nix flake check` green.

## Open Questions

- **None open.** The value type is resolved (`B32`/`B64` terminal-tail
  inductives); the strict codec is a run triple over them; rejection is
  structural (absence of an inhabitant); no flattening, no filter, no
  post-condition. Base16 case-insensitivity is a recorded non-goal (D8).
