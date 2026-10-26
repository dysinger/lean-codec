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

What is missing is **only the packaging**: a single value per base — the
`Codec`/`Run` value itself — replacing the bespoke
`decodeB32Strict`/`encodeB64Strict`/`relB64Strict` functions. There is no
`Base` enum and no dispatcher to add: the caller holds the base's value.

### The actual surface this delivers (the whole point)

Each base is **one `Codec`-value surface** (the format is a `Codec` value; `Run` is
only the already-proved repetition wrapper on top of an element, never a second
kind of format). Concretely:

```lean
-- fixed-width bases (2/4/8/10/16): the element IS the `Codec` value; the `Run`
-- is just its repetition wrapper (element `count k (satisfy p) ≫ block iso`)
base2  : Codec UInt8   := count 8 (satisfy isBitDigit) ≫ bitBlockIso   -- + bitRun : Run UInt8
base16 : Codec UInt8   := count 2 (satisfy isHexDigit) ≫ hexBlockIso   -- + hexRun : Run UInt8
-- padded bases (32/64): a COMPOSITION — full-block `Run` (element `b64BlockElem`)
-- then the terminal-tail `Codec` (`b64TailElem`), `iso`-ed to the B64/B32 value
base64 : composition  = b64Run ▸ b64TailElem ▸ (iso b64Iso)   -- B64 spine over List UInt8
base32 : composition  = b32Run ▸ b32TailElem ▸ (iso b32Iso)   -- B32 spine over List UInt8
```

(The `base{X} : Run` signature in an earlier draft was wrong: it typed each base
as a `Run`, which is only the repetition layer. A `Run α` is `{ elem : Codec α,
step : ConsumesByte elem }` — it cannot name the whole-input `B64`/`B32` format,
which is a block `Run` _plus_ a tail `Codec` _plus_ an `iso`. See the D7
correction.)

These values are decoded/encoded by the **uniform `Codec` operations**
(`Codec.decodeFull`/`Codec.encode`, or `decodeRepeat`/`encodeRepeat` for a run):

```lean
Codec.decodeFull BaseN.Base16.hexElem BaseN.Base16.hexConsumesByte n s
BaseN.Base64.decodeFullB64 s
BaseN.Base32.encodeB32 bs
```

There is **no** `encode (b : Base)` / `decode (b : Base)` facade, **no** `Base`
inductive, **no** `BaseN.Bridge` type-erasure, and **no** `decodeB32Strict`/
`encodeB64Strict`, **no** per-format function, **no** three carrier shapes. A
caller names the base's own value; the radix lives in that value and the value
type is the base's natural type (`UInt8`, `B32`, `B64`).

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
   per-base **run value** (`Run`). There is **no** facade `encode (b : Base)` /
   `decode (b : Base)` over `List UInt8` — the uniform surface is
   `Codec.decode`/`Codec.encode` on each base's value. Delete the bespoke
   `parseB64`/`encodeB64Strict`/`relB64Strict` run triples (and base32 analogues)
   and the `decodeBytes`/`encodeBytes`/`roundtripBytes` shims and the
   `BaseN.Bridge` module. No `many` constructor is added (verified impossible; both
   references derive it).
2. Re-express all seven bases as run values (fixed-width `count`/`iso`, padded
   over the full-block `Run` + terminal-tail composition; the `B32`/`B64` value
   types are the **canonical block/tail spine**, not a type that makes illegal
   padded states unrepresentable).
3. Re-prove the three RFC-conformance theorem families per base (rejection /
   canonical encoding / converse + injectivity) **over the uniform `decode`/
   `encode`**, not over per-format functions.
4. `[propext, Quot.sound]`-only, zero `sorry`, zero `Classical.choice`, zero
   per-format C.

**Non-Goals:**

- No committed-`|`/single-valued-decode change: `decode` stays list-valued with
  backtracking union (README `[D2]`/`[D3]`; `lean` skill §3). The reverted
  `codec-uniform-api` single-result idea stays out of scope.
- No flattening of `B32`/`B64` back to `List (List UInt8)` in the _surface_ (the
  value type is `List UInt8`; `B32`/`B64` is only the canonical split spine, a
  proved total bijective relabeling `b32BytesOf`/`b32OfBytes` — the earlier
  "no bijective flattening exists" claim was false and is withdrawn).
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

### D1 — The `B32`/`B64` inductives stay as the **canonical block/tail spine**, not a run triple

The `B32`/`B64` terminal-tail inductives stay (they are the canonical block/tail
spine — a proved total bijective relabeling of `List UInt8` via `b32BytesOf`/
`b32OfBytes`). They are **not** the value type of the uniform decoder (which is
`List UInt8`); they are the structure used to _specify_ the full-block + terminal-tail
split. A `tail*` constructor has no continuation, so the split is well-scoped, but
this does **not** make "full block after a tail" untypeable — a `List UInt8` freely
admits such a shape, and rejection is the `decodeFullB32`/`decodeFullB64 s = none`
inequation over the composition, **not** an absence of an inhabitant.

### D2 — Rejection is `decodeFullB64`/`decodeFullB32 s = none`, an inequation over the composition

Stated over the uniform decoder (`Codec.decodeFull <elem> <witness> n s` for the
fixed-width bases; `decodeFullB64`/`decodeFullB32 s` for the padded composition),
not a bespoke one. The `Zg==AAAA` class is `none` because the full-block run cannot
consume a block containing `=` (no `b64BlockElem`/`b32BlockElem` value contains `=`)
and the leftover alphabet-only bytes cannot decode as a `b64TailElem`/`b32TailElem`
(which must contain `=`), so `List.head? ((decodeRepeat …).filterMap …) = none` — a
pad-dichotomy **inequation**, not an absence-of-inhabitant argument.

### D3 — No facade: each base is its own `Codec`/`Run` value, decoded/encoded by the uniform `Codec` operations

```lean
-- no `Base` inductive, no `encode (b : Base)`, no `decode (b : Base)`
-- each base is a value; the radix lives in the value, not a dispatch index
Codec.decodeFull BaseN.Base16.hexElem BaseN.Base16.hexConsumesByte n s   -- : Option (List UInt8)
BaseN.Base64.decodeFullB64 s                                              -- : Option (List UInt8)
BaseN.Base32.encodeB32 bs                                                 -- : Option (Sigma … Bytes …)
```

The uniform surface is `Codec.decode`/`Codec.encode` (and `decodeRepeat`/
`encodeRepeat`/`decodeFull` for a run or composition) applied to the base's own
value. There is **no** `Base` enum, no `cases b` dispatcher, no `BaseN.Bridge`
type-erasure, and no `Base.val : Base → Type` family: a runtime radix selector
would be a bespoke per-format function by another name, and has no client. The
value type is `List UInt8` (the whole byte list), with `B32`/`B64` as the
canonical block/tail spine used only to specify the split.

### D4 — The one generic lemma (carried over): forward `rel_count_satisfy`

Prove `Rel (count k (satisfy p)) l s` from `s = byte-image of l` + `∀ b ∈ l, p b`,
once in `BaseN.Common`, parameterized by `p`/`k` (carries the `(k+1)-1 = k`
length-cast gotcha). This is the one shared primitive all seven bases need.

### D5 — Bench value-checks the uniform surface (carried over)

`Bench.lean` uses `Codec.decodeFull`/`Codec.encode` (and `decodeFullB64`/
`encodeB64`/`decodeFullB32`/`encodeB32` for the padded bases), never
`decodeB32Strict`. The F\* rejection/canonical/converse vectors survive,
re-spelled over the uniform entry points.

### D6 — Base16 case-insensitivity: in scope (reversed — task 7.3)

> **Reversal.** This section originally read "Base16 case-insensitivity is out of
> scope (carried over) — `hexElem` stays a strict uppercase `Iso`, lowercase `6f`
> is a rejection, not an alias", and justified it by "a case-insensitive alphabet
> would break `Unambiguous`". **That justification was false.** `Unambiguous`
> (`Codec/Sound.lean`) says one input yields at most one value; folding case
> _before_ decoding is a total function and introduces no alternative results. The
> real constraint is the **canonicality of encode** — one value, one spelling —
> and it is preserved because the encoder keeps emitting uppercase.

The RFC 4648 §8 MUST is now satisfied, without weakening `Iso.law`:
`lean-codec`'s `Codec.Normal` puts the quotient in the **object**
(`Normal (List UInt8) foldList`), so `hexBlockIsoF : Iso UInt8 (Normal (List UInt8)
foldList)` is an ordinary `Iso`. The fold is **upward** (`a`–`f` → `A`–`F`) so the
canonical uppercase encoding is a fixed point — exactly `decodeNormal_encode`'s
`hfix` obligation, discharged as `foldList_hexBlockUnapply`.

Two shapes of the layer, both proved in `BaseN/Base16.lean`:
`decodeHexBlockFold` (one block) and `decodeHexFold` (whole input: `foldByteBytes`
applied to `Bytes n` first, then the strict `hexRun`). The strict `hexElem`/
`hexRun`/`encodeHex` are untouched — only **decoding** widens.

**The §8 widening is a one-directional preservation, not an identity.**
`hexBlockApply (foldList cs) = hexBlockApply cs` is **false**: `['6','f']` is
rejected by the strict `apply` yet folds to the accepted `['6','F']`. The lemma
the `Iso` law needs is `hexBlockApply cs = some b → hexBlockApply (foldList cs) =
some b` (`hexBlockApply_foldList`), with the refutation recorded as
`hexBlockApply_foldList_ne`.

### D7 — The padded whole-input decoder is a **composition** (full-block `Run` + terminal-tail `Codec`, `iso`-ed to `B64`/`B32`); its result is **still flattened via `head?`/`filterMap`**

> **Correction (task 6.5).** An earlier revision of this heading claimed the
> decoder was "**not** `head?`/`filterMap`", and the body below claimed the work
> "removes the flattened `List UInt8`/`head?`/`filterMap` step". **Both claims were
> false.** The shipped `decodeFullB64` (`BaseN/Base64.lean`) and `decodeFullB32`
> (`BaseN/Base32.lean`) are literally
> `List.head? ((decodeRepeat {x}BlockElem … s).filterMap …)`. The shape is
> **retained**. What D8 actually bought is not removal of `head?`/`filterMap` but
> the `tails.length ≤ 1` guard that makes the _chosen_ `filterMap` hit unique —
> `head?` then picks the only candidate. The `head?`-determinism therefore still
> rests on the `boundary_pin`/`head?_eq_some_of_mem_eq`/split-uniqueness machinery,
> exactly as D7 originally described. D7 is a _structural_ statement about which
> `Codec` values are composed, not a claim about the result-carrier shape.

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
whose result is the whole `List UInt8` (the `B64`/`B32` spine only specifies the
full-block/tail split, per D1). The
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
> finite tail `Codec`). The `B64`/`B32` spine is reached by `iso` **after** that
> composition (a relabeling of the `List UInt8` result), so the whole-input roundtrip
> is **not** the inherited law _alone_:
> it is the inherited per-component laws composed through a new (but small and
> well-scoped) split-uniqueness lemma. That lemma is unavoidable given D0; D7 does
> not delete it, it gives it a precise shape and location.

This is the correction to the earlier D7 wording ("a single `Codec B64`/`Codec B32`
value … the inherited law, not a new lemma"), which was incoherent with D0: it
promised one AST value where D0 proves none exists. The honest shape is
full-block `Run` `▸` terminal-tail `Codec` `▸` `iso` to `B64`/`B32`, with the
roundtrip law = inherited `decodeRepeat_spec`/`encodeRepeat_rel` (blocks) +
inherited `decodeFull_spec` (tail) + the one split-uniqueness composition lemma.
This **restructures the decode around** the block-`Run`/terminal-tail split (the
`head?`/`filterMap` shape is **retained** — see the correction at the top of D7;
D8's `≤ 1` guard, not a removal, is what makes it deterministic), and makes the
base32 mirror (5 tail shapes) fall out of the same tail-`alt` template. Each
base is decoded/encoded by `Codec.decodeFull`/`Codec.encode` on its own value —
**no** `BaseN.lean` facade and **no** `BaseN.Bridge` type-erasure.

_Consequence for task order:_ 1.4 (roundtrip) is the gate for 1.1 (delete the
strict triples + shims); then the bench re-anchor (5.1) and the conformance
families (3.x/4.x), exactly as stated — there is **no** facade task.

### D8 — The terminal tail is decoded as **at most one** bounded block (a `≤ 1` guard on `decodeFull`), so the converse holds unconditionally

This is the completion of D7's deferred "substep 6" (the `head?`/`filterMap`
re-shape), and it is **load-bearing**, not cosmetic. The first implementation of
`decodeFullB64`/`decodeFullB32` decoded the terminal tail with
`decodeFull b64TailElem`/`decodeFull b32TailElem`. Because `decodeFull` is
`decodeRepeat` with full consumption, it admits a **multi-block** tail: an input
with data _after_ a terminal `=` that is _itself_ a valid padded tail block —
`"Zg==Zg=="` (two 1-byte blocks `[[f],[f]]`), `"MY======MY======"` (base32) —
decodes successfully to `[0x66, 0x66]`.

That is a genuine RFC 4648 §3.2 rejection failure ("padding … only performed at
the end"), and it makes the **converse** (`decodeFullB64 s = some v → encodeB64 v =
some ⟨n, s⟩`, task 4.3) **false**: `decodeFullB64 "Zg==Zg==" = some [f, f]` but
`encodeB64 [f, f] = "Zm8=" ≠ "Zg==Zg=="` (verified `#eval`).

**Decision (LANDED `../lean-basen` `c0c55cd`):** the whole-input decoder's filter
step adds a **`tail.length ≤ 1` guard** on the result of `decodeFull b64TailElem`/
`decodeFull b32TailElem` (a multi-block tail — `tail.length ≥ 2` — returns `none`,
not `some`). This admits only `tail = []` or `tail = [one 1–2-byte block]`, so:

- data after a terminal `=` (even a valid appendable padded block) is **rejected**
  (completing 3.1/3.2's "any data after the terminal `=`" mandate — the
  `Zg==Zg==`/`MY======MY======` class was previously unproven);
- the converse's tail is a **provable** singleton (the `≤ 1` bound is a conjunct
  of the new `decodeFullB64_some`/`decodeFullB32_some`), so the task-4.3 note's
  "the tail 1–2 bytes" assumption is a fact, not an unstated precondition.

**Why a guard and not the single-element `decode` re-shape:** the re-shape (decode
`b64TailElem` once via `decode`, requiring `t₂.remaining = 0`) changes the tail
value from `List (List UInt8)` to a single `List UInt8`, which ripples through
`decodeFullB64_some`, the whole roundtrip singleton proof, and the rejection
family (re-deriving the `b64_boundary_pin`/`b64_block_run_of_boundary` inputs).
The guard is semantically identical but keeps `decodeFull b64TailElem` (hence
`relRepeat (Rel b64TailElem)` machinery and the boundary pin) intact: the only
surfaced delta is one extra `tails.length ≤ 1` conjunct threaded through
`decodeFullB64_some`/`_mem_encode`/`_roundtrip` and the rejection `rcases`. Both
bases' `lake build` are green, zero `sorry`.

The full-block `Run` `▸` (at-most-one-block) tail (`▸ iso`) composition is precisely the
D7 shape; this change discharges the last deferred piece of D7.

## Risks / trade-offs

- **[Not a `Codec` constructor, by verified necessity]** — this is _not_ a
  compromise against the spec; the spec's "composed from `satisfy`/`count`/`iso`/
  `alt`, with unbounded repetition as the derived `many`" is satisfied by `many`
  being a _derived run_ (as the paper/F\* derive it), and the uniform
  `decode`/`encode` is delivered by the per-base `Codec`/`Run` value — the caller
  calls `Codec.decode`/`Codec.encode`, never a facade dispatcher. No new core
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
3. Reanchor `Bench.lean` to the per-base values (`Codec.decodeFull`/`encodeX`/
   `decodeFullB64`/`decodeFullB32`); delete the strict triples + shims and
   `BaseN.Bridge`.
4. Re-prove the three conformance families per base over the uniform surface; gate
   `lake build` + `lake build bench`, `#print axioms` = `[propext, Quot.sound]`,
   `nix flake check` green.

## Open questions

**None.** `many` is derived (paper/F\*); the run is a first-class `Run` value over
the already-proved repetition; the `B32`/`B64` spine and the
rejection/canonical/converse families carry over; there is **no** facade — each
base is its own `Codec`/`Run` value decoded/encoded by `Codec.decode`/`Codec.encode`.
