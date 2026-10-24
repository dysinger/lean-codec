# Design — `basen-rfc-conformance-theorems` (re-anchored to the uniform `Codec`-value surface)

## Context

See `proposal.md` — Why. The `basen` package must prove the full RFC 4648
conformance contract (rejection / canonical encoding / converse / injectivity)
on top of the **uniform surface**: every base is decoded and encoded by the
_same_ operation — "only the codec changes" — so decoding base64 and decoding
JSON are the same call, with the _value type_ differing, never the operation
shape.

The synced spec `openspec/specs/basen/spec.md` requires this ("The `basen` bases
are `Codec` values … composed from `satisfy`/`count`/`iso`/`alt`, with unbounded
repetition as the derived `many`, roundtrip via the inherited per-component laws
plus one block-run/tail split-uniqueness lemma for the padded bases, no
bespoke `encode`/`decode`"). A prior change
(`basen-uniform-leaf-api`, commit `11f7072`) walked away from it, declaring the
needed `many` node "type-theoretically impossible" and instead implementing
base32/64 as **bespoke per-format run triples** (`parseB64`/`encodeB64Strict`/
`relB64Strict` and their base32 analogues) with three irreconcilable
carrier/value shapes — `decodeB32Strict`/`encodeB64Strict` a caller must name.
That was a **wrong turn**: the wrong turn was _falling back to per-format
functions_, not the (correct) observation that `many` is not a constructor. This
change corrects it.

The three references settle the shape of `many`:

- **The paper** (PAPER.md §3.4) — `many p = nil $ pure () | cons $ p ∗ many p`:
  `many` is a **derived recursive combinator**, _not_ an elementary description
  alongside `token`/`pure`. Its denotation is the **least** `nil`/`cons` fixpoint.
- **The F\* reference** (`fstar-codec` `Data.Codec.Types.fst`) — there is **no
  `many` at all**; the unbounded run is `satisfy_many0 f : codec (list byte)`, a
  `let rec satisfy_run_scan` over the _finite_ input, and a `codec a` is a record
  of `enc`/`dec`/`roundtrip`.
- **The project's own `lean` skill** (§3) — "Recursive syntax descriptions
  (`many`) are coinductive in the _parser_, inductive in the _denotation_ …
  the correct constructive guard is **well-founded recursion on the consumed
  string**"; "`many` is a derived recursive combinator (paper §3.4), never an AST
  node".

**The verified negative (this change's binding constraint):** `many` **cannot** be
a `Codec` constructor. A denotational witness `Productive p := ∀ x n s, Rel p x
s → n ≠ 0` (or `ConsumesByte`) as a constructor field creates the cycle
`Codec → Productive → Rel → Codec` (the field mentions `Rel`/`decode`, both of
which structurally recurse on `Codec`). Lean rejects the two escapes: mixing a
`def` with an `inductive` in a `mutual` block is forbidden, and a
`mutual inductive Codec (Type 1) + Rel (Prop)` is rejected by the universe check
("all inductive types … must belong to the same type universe"; `Codec : Type →
Type 1` vs `Rel : … → Prop`). A _syntactic_ productivity `def` has the identical
`Codec → productive → Codec` cycle. This is the same wall `11f7072` hit — and it
is **real and verified**. The paper/F\* avoid it precisely because they make
`many` **derived**, not a constructor.

Therefore the uniform surface is recovered the way both references do it: keep
`many` **derived** (the already-proved `relRepeat`/`decodeRepeat`/`encodeRepeat`
triple and its `takeWhile`/`sepBy` specializations in `Combinators.lean`), and
make the **per-base codec a single first-class value** that packages that derived
run together with the fixed-width `count`/`iso` part — one value, one `decode`/
`encode`, no bespoke function.

## The core idea: `many` is derived (already implemented); the base is one _value_

The generic repetition is already, faithfully, in `Codec/Combinators.lean`:

- `relRepeat`/`decodeRepeat`/`encodeRepeat` — the paper's `many`, total (the
  denotation is the least fixpoint; the decoder is well-founded on `n` guarded by
  `ConsumesByte`; the encoder is structural on the value list).
- `takeWhile p = (relTakeWhile, decodeTakeWhile, encodeTakeWhile)` — F\*'s
  `satisfy_many0`, with `decodeTakeWhile_spec`/`encodeTakeWhile_rel` inherited.
- `sepBy p sep = (relSepBy, decodeSepBy, encodeSepBy)` — the paper's `sepBy1`,
  with the same inherited laws.

What is missing is **only the packaging**: a single value per base that a uniform
`encode (b : Base)` / `decode (b : Base)` dispatches over, replacing the bespoke
`decodeB32Strict`/`encodeB64Strict`/`relB64Strict` functions.

### The actual surface this delivers (the whole point)

Each base is **one `Codec`-value surface** (the format is a `Codec` value; `Run` is
only the already-proved repetition wrapper on top of an element, never a second
kind of format), and the facade dispatches over the **single** value type
`List UInt8`. Concretely:

```lean
-- fixed-width bases (2/4/8/10/16): the element IS the `Codec` value; the `Run`
-- is just its repetition wrapper (element `count k (satisfy p) ≫ block iso`)
base2  : Codec UInt8   := count 8 (satisfy isBitDigit) ≫ bitBlockIso   -- + bitRun : Run UInt8
base16 : Codec UInt8   := count 2 (satisfy isHexDigit) ≫ hexBlockIso   -- + hexRun : Run UInt8
-- padded bases (32/64): a COMPOSITION — full-block `Run` (element `b64BlockElem`)
-- then the terminal-tail `Codec` (`b64TailElem`), `iso`-ed to the B64/B32 value
base64 : composition  = b64Run ▸ b64TailElem ▸ (iso b64Iso)   -- value type B64
base32 : composition  = b32Run ▸ b32TailElem ▸ (iso b32Iso)   -- value type B32
```

(The `base{X} : Run` signature in an earlier draft was wrong: it typed each base
as a `Run`, which is only the repetition layer. A `Run α` is `{ elem : Codec α,
step : ConsumesByte elem }` — it cannot name the whole-input `B64`/`B32` format,
which is a block `Run` _plus_ a tail `Codec` _plus_ an `iso`. See the D7
correction.)

with a **uniform facade** (the only entry points):

```lean
def encode (b : Base) (bs : List UInt8) : Option (List UInt8)
def decode (b : Base) (s  : List UInt8) : Option (List UInt8)
theorem roundtrip (b : Base) (bs : List UInt8) : decode b (encode b bs) = some bs
```

There is **no** `decodeB32Strict`/`encodeB64Strict`, **no** per-format function,
**no** three carrier shapes. A caller never names a leaf; the radix lives on the
`Base` index and the value is always `List UInt8`.

> **"`Run`" is a first-class value, not a bespoke function.** It is the F\*
> `codec a` record shape (`enc`/`dec`/`roundtrip`), specialized to a `List UInt8`
> value and realized in Lean as a `structure` bundling the three already-proved
> interpretations (`relRepeat (Rel elem)`, `decodeRepeat elem <witness>`,
> `encodeRepeat elem`), with the laws as the _inherited_ `decodeRepeat_spec`/
> `encodeRepeat_rel` theorems rather than per-combinator re-proofs. It is **not** a
> new `Codec` constructor and **not** a hand-rolled per-format parser.

## Goals / Non-Goals

**Goals:**

1. Package the already-proved derived repetition into a single first-class
   per-base **run value** (`Run`), and a uniform facade `encode (b : Base)` /
   `decode (b : Base)` over `List UInt8`. Delete the bespoke
   `parseB64`/`encodeB64Strict`/`relB64Strict` run triples (and base32 analogues).
   No `many` constructor is added (verified impossible; both references derive it).
2. Re-express all seven bases as run values (fixed-width `count`/`iso`, padded
   over terminal-tail `B32`/`B64` value types so illegal padded states remain
   **unrepresentable**).
3. Re-prove the three RFC-conformance theorem families per base (rejection /
   canonical encoding / converse + injectivity) **over the uniform `decode`/
   `encode`**, not over per-format functions.
4. `[propext, Quot.sound]`-only, zero `sorry`, zero `Classical.choice`, zero
   per-format C.

**Non-Goals:**

- No committed-`|`/single-valued-decode change: `decode` stays list-valued with
  backtracking union (README `[D2]`/`[D3]`; `lean` skill §3). The reverted
  `codec-uniform-api` single-result idea stays out of scope.
- No flattening of `B32`/`B64` back to `List (List UInt8)` (no bijective
  flattening exists; the terminal tail is indistinguishable from a full block
  after the fact).
- No `many` constructor (paper/F\* derive it; a constructor is un-implementable
  in Lean, verified above).
- Base16 case-insensitivity remains a non-goal (D8 below).

## Decisions

### D0 — `many` is **derived**, not a constructor; the run is a **value**

`many`/`satisfy_many0` are realized by the existing `relRepeat`/`decodeRepeat`/
`encodeRepeat` (and their `takeWhile`/`sepBy` specializations), exactly as the
paper (§3.4) and F\* (`satisfy_many0`) do. A first-class **`Run`** bundles the
three interpretations so a consumer holds _one value_, never three names:

```lean
structure Run where
  elem : Codec UInt8                -- the element (or block) description
  step : ConsumesByte elem          -- the productivity witness
  -- decode/encode/rel derived: decodeRepeat elem step / encodeRepeat elem / relRepeat (Rel elem)
```

The fixed-width block `Iso`s (`bitBlockIso`/`quartetBlockIso`/…) are `Codec
UInt8` values via `count k (satisfy p) ≫ <block iso>`; the `Run` wraps them.
The padded bases wrap the full-block element (`count 8 (satisfy b32OrPad) ≫
b32BlockIso`, etc.) plus a terminal-tail `alt`/`iso` onto `B32`/`B64`.

### D1 — The value types stay terminal-tail (`B32`/`B64`), but _as values_, not run triples

The `B32`/`B64` terminal-tail inductives stay (that was the _correct_ part of the
prior design). They are the **value type** of the padded run, realized via `iso`
over the `Run`'s full-block + optional-tail structure. `=`-terminal is enforced
by construction (a `tail*` constructor has no continuation). The illegal state
"full block after a tail" has no term; the decoder returns `none` because no
value relates — proved via `decodeRepeat_spec`/`relRepeat`/`encode_rel`, **not**
via a bespoke `parseB64`.

### D2 — Rejection is `decode <base> bad = none`, structural and uniform

Stated over the uniform decoder (`decode (b) bad` / `Codec.decodeFull <elem>
<witness> n bad`), not a bespoke one. The `Zg==AAAA` class is `none` because no
`B64` value relates (absence of an inhabitant), proved by the run's relation +
`decode_spec`.

### D3 — The facade is uniform (one value type, no `Base.val` family)

```lean
def encode (b : Base) (bs : List UInt8) : Option (List UInt8) -- or total
def decode (b : Base) (s  : List UInt8) : Option (List UInt8)
theorem roundtrip (b : Base) (bs : List UInt8) : decode b (encode b bs) = some bs
```

`cases b` dispatches to each base's `Run`, normalized through `BaseN.Bridge`
(`Bytes n ↔ List UInt8`, already landed). No `Base.val : Base → Type` family, no
value sum type, no three shapes.

### D4 — The one generic lemma (carried over): forward `rel_count_satisfy`

Prove `Rel (count k (satisfy p)) l s` from `s = byte-image of l` + `∀ b ∈ l, p b`,
once in `BaseN.Common`, parameterized by `p`/`k` (carries the `(k+1)-1 = k`
length-cast gotcha). This is the one shared primitive all seven bases need.

### D5 — Bench value-checks the uniform surface (carried over)

`Bench.lean` uses `Codec.decode`/`Codec.encode` (or the facade), never
`decodeB32Strict`. The F\* rejection/canonical/converse vectors survive,
re-spelled over the uniform entry points.

### D6 — Base16 case-insensitivity is out of scope (carried over)

`hexElem` stays a strict uppercase `Iso`. Lowercase `6f` is a rejection, not an
alias.

### D7 — The padded whole-input decoder is a **composition** (full-block `Run` + terminal-tail `Codec`, `iso`-ed to `B64`/`B32`), **not** `head?`/`filterMap`

The first implementation of `decodeFullB64`/`decodeFullB32` (and `encodeB64`/
`encodeB32`) returned a _flattened_ `List UInt8` built by `List.head? ((decodeRepeat
b64BlockElem … s).filterMap …)`. That shape makes the whole-input roundtrip
(`decodeFullB64 (encodeB64 bs) = some bs`) depend on a bespoke
"committed-block-prefix uniqueness" proof (the `head?` picks the first `filterMap`
hit; proving it is the _right_ hit needs the alphabet-vs-`=` pad dichotomy and a
`List.ofFn`/`Fin` cast grind).

**Decision:** re-express the padded whole-input decoder/encoder over a
well-scoped **composition** — the full-block `Run` (`b64Run`/`b32Run`, the derived
`many`) followed by the finite terminal-tail `Codec` (`b64TailElem`/`b32TailElem`),
with the result `iso`-ed to the terminal-tail value type `B64`/`B32` (per D1). The
roundtrip is therefore the **inherited** `decodeRepeat_spec`/`encodeRepeat_rel`/
`decodeFull_spec` laws for the two components **plus one explicit, named
composition lemma** — the block-run/tail split uniqueness (the alphabet-vs-`=` pad
dichotomy disambiguates the block/tail boundary; see the `head?`-replacement note
below).

> **Correction (coherence with D0):** there is **no** single `Codec B64`/`Codec B32`
> value. The `Codec` AST has no repetition node (only `iso`/`seq`/`alt`/`empty`/
> `pure`/`byte`/`satisfy`), and D0 proves `many` cannot be added as one. An
> unbounded "n full blocks + one terminal tail" is **not** a finite `Codec`
> description; it is a _derived composition_ (a `Run` = `many`-of-blocks, then a
> finite tail `Codec`). The value type `B64`/`B32` is reached by `iso` **after** that
> composition, so the whole-input roundtrip is **not** the inherited law _alone_:
> it is the inherited per-component laws composed through a new (but small and
> well-scoped) split-uniqueness lemma. That lemma is unavoidable given D0; D7 does
> not delete it, it gives it a precise shape and location.

This is the correction to the earlier D7 wording ("a single `Codec B64`/`Codec B32`
value … the inherited law, not a new lemma"), which was incoherent with D0: it
promised one AST value where D0 proves none exists. The honest shape is
full-block `Run` `▸` terminal-tail `Codec` `▸` `iso` to `B64`/`B32`, with the
roundtrip law = inherited `decodeRepeat_spec`/`encodeRepeat_rel` (blocks) +
inherited `decodeFull_spec` (tail) + the one split-uniqueness composition lemma.
This removes the flattened `List UInt8`/`head?`/`filterMap` step and makes the
base32 mirror (5 tail shapes) fall out of the same tail-`alt` template. The facade
(`BaseN.lean`) then dispatches `cases b` to `Codec.decodeFull`/`Codec.encode` over
that composition, normalized through `BaseN.Bridge`.

_Consequence for task order:_ 1.4 (roundtrip) is the gate for 2.1 (facade rewire)
→ 1.1 (delete the strict triples) → 2.2, exactly as stated. The re-express here is
the _mechanism_ that makes 1.4 provable **with one named, scoped composition lemma**
(not "no bespoke law", as the earlier wording claimed).

## Risks / trade-offs

- **[Not a `Codec` constructor, by verified necessity]** — this is _not_ a
  compromise against the spec; the spec's "composed from `satisfy`/`count`/`iso`/
  `alt`, with unbounded repetition as the derived `many`" is satisfied by `many`
  being a _derived run_ (as the paper/F\* derive it), and the uniform
  `decode`/`encode` is delivered by the `Run` value + facade. No new core
  constructor, no `Codec.rec` conversion of the law suite (a _reduction_ of the
  risky scope the prior design proposed).
- **[`Run` is a value, so no `induction d` conversions]** — the `Run` bundles the
  already-proved `decodeRepeat`/`encodeRepeat`/`relRepeat`; per-base laws are the
  inherited `decodeRepeat_spec`/`encodeRepeat_rel`, not new `Codec.rec` cases.
- **[Terminal-tail `iso` must be constructed explicitly, plus one composition lemma]** —
  the two new proofs: (a) the `Iso` from the composed `(List full-block · ×
Option tail)` result to `B32`/`B64` (a well-scoped bijection; a tail's arity is
  recoverable from its constructor, not the non-existent `List (List UInt8)`
  flattening); and (b) the **block-run/tail split-uniqueness composition lemma** —
  the one genuinely new roundtrip step that D0 makes unavoidable (there is no
  single `Codec B64` whose roundtrip is the inherited law alone; see D7). Both
  are `[propext, Quot.sound]`-only, using the already-landed pad-dichotomy
  primitives (`b64Char_pad_false` / `not_rel_b64BlockElem_of_pad`) and
  `Rel_count_satisfy_ofFn` (content extraction).
- **[No surface regression]** — `decode` stays list-valued/backtracking (README
  `[D2]`/`[D3]`, `lean` skill §3).

## Implementation order

1. Add the `Run` value (bundle `elem`/`step` + the three inherited interpretations)
   in `BaseN` (downstream `lean-basen`), over the existing `relRepeat`/
   `decodeRepeat`/`encodeRepeat`. Delete the bespoke base32/64 run triples.
2. Re-express the seven bases as `Run` values (fixed-width `count`/`iso`; padded
   over `B32`/`B64`). Apply D4's `rel_count_satisfy`.
3. Restore the facade `encode`/`decode`/`roundtrip`; reanchor `Bench.lean`.
4. Re-prove the three conformance families per base over the uniform surface; gate
   `lake build` + `lake build bench`, `#print axioms` = `[propext, Quot.sound]`,
   `nix flake check` green.

## Open questions

**None.** `many` is derived (paper/F\*); the run is a first-class `Run` value over
the already-proved repetition; the value types (`B32`/`B64`) and the
rejection/canonical/converse families carry over; the facade is uniform over
`List UInt8`.
