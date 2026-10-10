# Proposal: `codec` — invertible binary codecs in Lean 4 (Iso-based, byte-only core)

> OpenSpec planning artifact — NOT committed (`openspec/` is gitignored).
> Task ledger: [`tasks.md`](./tasks.md).

## Goal, restated

Build a **verified, bidirectional codec library in Lean 4** that is a **correct
extension of** Rendel & Ostermann's *"Invertible Syntax Descriptions"*
(Haskell Symposium 2010) — faithful to the paper, more rigorous than it, and
covering a *wider* domain.  **The paper is the spec.**

Requirements, in priority order:

1. **Pure-framework core; byte concrete syntax.**  `codec` has exactly one
   concrete syntax — a byte sequence (`ByteArray`/`UInt8`) — and its core is
   **pure framework: `Iso`, `Codec`, `Rel`, the interpreters, the law
   theorems, and no *domain-specific* leaf codecs** (not even `u8` — the only
   descriptions are the primitives `byte` and `pure`).  Every concrete codec
   (fixed-width `u16le`/`u32be`/…, byte blobs, LEB128 `varint`, length-prefixed
   framing) is a **downstream leaf** built by composition — a leaf `Iso` may
   consume any number of bytes, so there is **no "var-binary" or "text"
   category in core**, only consumers: `lean-binary` (binary leaves) and
   `lean-text` (text/Unicode).
2. **Invertible by construction, with proofs.**  The central abstraction is the
   paper's *partial isomorphism* `Iso α β`, carrying its inverse law as a proof
   field — not a solver-discharged lemma bolted onto a record.
3. **Optimized for speed.**  Real, measurable performance on real inputs, via
   Lean's native `ByteArray`/`UIntN` primitives and C/LLVM extraction — not a
   proof-of-concept list-of-results backtracker.

## The key architectural decision: pure framework; leaves are downstream

The paper treats *character* syntax as primitive (`token : δ Char`, `text`,
`element`/`subset` over `Char`) and never discusses binary.  We **invert the
base type** — bytes are primitive (`byte : Codec UInt8`, a byte-based `Rel`) — and
**stop there.**  `codec`'s core is *pure framework*: `Iso`, `Codec`, `Rel`,
the interpreters, and the laws.  No domain-specific leaf codecs, no `Char`, no `String`, no
UTF-8, no endianness, no `varint`.

Every concrete codec is a **downstream consumer** in a separate package that
depends on the `codec` package and adds, as *new codecs* — values of the exact same
`Iso` type the core defines —

```lean
-- lean-binary (binary leaves)
u8      : Codec UInt8          = subset (fun _ => true) $ byte   -- trivial: one line
varint  : Codec Nat                          -- a primitive Iso, value-dependent arity
u16le   : Codec UInt16 / u32be / u64* / bytes n / lengthPrefix / ...

-- lean-text (text/Unicode combinators on top of bytes)
utf8        : Iso String (List UInt8)     -- the foundational encoding primitive
textLiteral : Codec Unit       -- the paper's `text "…"`, over Codec
identifier  : Codec String     -- the paper's `letter <*> many (letter | digit)`
whitespace  : ...              -- the paper's §6.3 skip/opt/sep spacing
-- …the paper's §6 combinator library, re-based on bytes via utf8
```

(`lean-text` is named for the *domain* — text — not the encoding; its
foundational primitive is `utf8 : Iso String (List UInt8)`, matching Haskell's
`text`/`Data.Text.Encoding` where UTF-8 is one encoding *inside* a text library,
not the library's name.)

and composes them with the byte-level combinators via `$` (`utf8 $ byte`,
`many (utf8 $ byte)`, `lengthPrefix $ varint $ …`).  Because a leaf is **just
another `Iso`/`Codec`**, `codec` needs **zero** awareness that any of this
will exist: no special primitives, no second concrete syntax, no endianness or
Unicode rules.  The *first downstream leaf* (even the `u8` one-liner) is the
acceptance test that the framework is genuinely expressive — the same argument
the paper §5 makes for its own isomorphisms.

This keeps the core minimal and the scope honest: `codec` is a
byte-level invertible-description framework; `lean-binary` and `lean-text` are
its first real consumers.

## What the paper gives us (the actual spec)

- **Partial isomorphisms** (§3.1, §5.1): `Iso α β = α ⇄ β` — `apply : α →
  Option β`, `unapply : β → Option α`, with an inverse invariant.  Composed as
  a **category** (`∘`, `id`), with bifunctor product `×`, `associate`,
  `commute`, `unit`, `element`, `subset`, `inverse`, and `foldl`/`iterate`
  (§5.2/5.3).

- **Syntax descriptions** (§3.4) = one program interpreted polysemantically:
  `$` (IsoFunctor), `*` (ProductFunctor / sequential tuples), `|`/`empty`
  (Alternative / choice), `pure`, `token`.

> **Naming.** The paper calls this layer `Syntax` (its concrete syntax is
> `String`/`Char` — a *text* concept) and its primitive `token` ("relates each
> character with itself", §3.4).  We rename them **`Codec`** and **`byte`**
> because our concrete syntax is a byte sequence — "syntax" and "token" would
> mislead (there is no historical precedent for "syntax" applied to *binary*
> formats; the paper's own §1 defines concrete syntax as "sequences of
> characters").  `Codec` (coder/decoder) and `byte` (one UInt8 ⇄ itself) are
> format-agnostic.  The low-level invertible pair **stays `Iso`** — that is a
> category-theoretic object, not a text notion, and `utf8 : Iso String
> (List UInt8)` reads correctly as "a reversible function between strings and
> bytes."

- **Denotational semantics** (§4.3): a description *is* a relation between
  abstract values and concrete sequences; decode and encode are both "find a pair
  in the relation."

- **Derived combinators** (§6.1): `many`, `text`, `*>`, `<*`, `between`,
  `chainl1`, whitespace/spacing.

## What we deliberately change from the paper, and why

Four **explicit** departures from the paper's *observable semantics* — each
gated and proved, never silent:

1. **Bytes are primitive; the paper's character domain is deferred.**  The
   paper's `token : δ Char` and `String`-based `Rel` become `byte : Codec UInt8`
   and a `ByteArray`-based `Rel`.  Characters/text/Unicode are **not** in
   `codec`; they are recovered by the downstream `lean-text` package (whose
   foundational codec is `utf8 : Iso String (List UInt8)`).  This is a *re-base*
   that adds binary to core while leaving the paper's text domain to a dependent
   package.

2. **Determinism replaces list-of-results backtracking.**  The paper's decoder
   (§4.1) returns `[(α, String)]` (nondeterministic).  Ours is a single result
   returning the remaining bytes, sound and complete **only on the unambiguous
   domain** (`∀ s, at most one x with Rel d x s`) — an explicit predicate proved
   per demo.  (Backtracking and peeking are out of scope.)

3. **`|` becomes committed choice, not full backtracking.**  A consequence of
   determinism (a single result cannot try both branches).  This is a *scope
   constraint*, not a forced re-base: §4.4 observes that real-world predictive
   `|` (Parsec) is a common *deviation* from full backtracking — evidence that
   committed choice is a practical, if narrower, semantics — but determinism is
   the actual reason we adopt it.

4. **Lossless capture — "allowed" bytes are kept, not discarded.**  The paper
   (§3.1, §6.3) models skippable bytes (`ignore`/`skipSpace`) as *lossy*: it
   maps arbitrary whitespace to `unit` and `unit` back to a single blank, and
   therefore admits (§3.1) that a strict isomorphism is impossible, settling for
   "modulo equivalence classes".  We reject that: a run of bytes a codec allows
   is captured as a value and re-emitted verbatim — realized by the existing
   `many (subset p byte)` idiom, **no new primitive** — so `decode (encode x) =
   x` holds byte-for-byte, a true isomorphism.  **No `ignore` in core**: it is
   the one combinator that would reintroduce the loss.

`encode` staying partial (`Option`) is **not** a departure — it is a *kept*
property: `empty`/`pure x`/`subset p` reject out-of-domain values exactly as the
paper's `Maybe` encoder does.  We deliberately do **not** totalize `encode`.

These four are the *only* places we change the paper's observable semantics;
each is called out, gated, and proved.

## Core design (Lean)

### Layer 0 — `Iso` (partial isomorphisms, the category)

```lean
structure Iso (α β : Type) where
  apply   : α → Option β
  unapply : β → Option α
  law     : ∀ a b, apply a = some b ↔ unapply b = some a   -- the inverse law
```

The law is **a field**, so every `Iso` is *correct by construction*; composition
composes laws (a `Category` instance proved once).  This is the paper §7.5's
own open question ("how the invariants of `Iso` values could be encoded in a
dependently typed language") answered.

**The law holds *unconditionally* (no equivalence-class caveat):** because
we drop the paper's lossy primitives — `ignore` and lossy `skipSpace`, which
map many bytes to `()` and thus break the strict invariant — **every** core
combinator is a strict partial isomorphism: `apply a = some b ↔ unapply b =
some a` holds for all `a b` (total isos, `subset`, `many`, `element`, all of
it).  This is itself the *reason* departure #4 (lossless capture) exists: by
never discarding bytes, we never need the paper's "modulo equivalence classes"
weakening.  There is no "coarse law" and no `T0.3` open shape — the strict law
is simply *the* law, and `Category Iso`'s `∘`-closure (T1.2) closes under it.

### Layer 1 — `Codec` (the descriptions, over bytes)

```lean
class Codec (δ) where ...        -- a typeclass (the paper's `Syntax` class)
-- byte : Codec UInt8                      -- ONE primitive description: the byte
-- $ / * / | / empty / pure            -- the paper's combinators, unchanged
```

A single description value, interpreted two ways over a `ByteArray`:

```lean
decode  (d) (s : ByteArray) : Except DecodeError (α × ByteArray)
   -- on failure, DecodeError carries the REMAINING unconsumed bytes;
   -- on success, return the value plus the remaining bytes (paper's `String → [(α,String)]` style, byte-ified)
encode  (d) (x : α)         : Option ByteArray
   -- partial (rejects out-of-domain), builder
```

`decode` returns the **remaining** bytes (not a `Nat` cursor): this is the
paper's own functional style (`Parser (String → [(α, String)]`) where position
is implicit in the returned suffix.  **Backtracking and peeking are out of
scope** (an agreed constraint, not an incidental loss): `decode` is a single
deterministic result (not the paper's `List`), and `|` is committed choice —
no lookahead, no re-running a rejected branch.

`encode` is **partial** (§4.2): `empty`/`pure x`/`subset p` reject out-of-domain
values; the fast `ByteArrayBuilder` lives inside the `some` branch.

**When does `encode` return `none`?**  Exactly when `x` is **out of the
codec's domain** — i.e. the codec does not claim to encode that particular
`x`.  This happens only at the primitive guards, then composes:
- `pure x₀` encodes `x` iff `x = x₀`; otherwise `none`.
- `subset p` encodes `x` iff `p x`; otherwise `none`.
- `c₁ | c₂` returns the first `some` from `c₁` then `c₂` (committed choice);
  `none` only if **both** return `none`.
- `empty` returns `none` for every input; a product returns `none` if any
  component does; `iso $ c` returns `none` if `iso.apply` is undefined.

`none` is therefore **not** an error — it is the type-level statement "this
value is not in my subset", and it is why `encode` is `Option` while `decode`
is `Except DecodeError` (whose `.error` is a *malformed-input* diagnostic with
position).  The `Iso.law`/roundtrip only promise `decode (encode x) = (x, empty)`
for values where `encode x = some s`.

### Layer 2 — `Rel` (denotational semantics = the spec)

```lean
def Rel (d : Codec α) (x : α) (s : ByteArray) : Prop := ...
```

A relation over **whole** byte sequences — a two-argument graph `(x, s)`,
mirroring §4.3 (whose concrete side is `String = [Char]`; ours is `ByteArray`).
`Rel` has no notion of "remaining" — the suffix is private to the `decode`
interpreter, exactly as the paper's `Rel` hides "remaining text" inside its
parser.  (For proof ergonomics we may reason over a spec-level `List UInt8`
model and transport back to `ByteArray` — that is T0.5, a *proof-tactic* concern,
not part of the `Rel` signature itself.)

### Error reporting (in core — not deferred)

A failed decode tells you **where** it failed, because it is useful and the
position is *structural* (provable for free, not an added field + bound lemma):

```lean
inductive DecodeError where
  | unexpectedEndOfInput : ByteArray → DecodeError          -- remaining (empty here)
  | unexpected           : UInt8 → ByteArray → DecodeError  -- offending byte + remaining
  | expected             : ByteArray → ByteArray → DecodeError  -- expected a byte sequence, got a mismatch (of the same length or at end)

def DecodeError.remaining (e : DecodeError) : ByteArray := ...
def DecodeError.position (e : DecodeError) (whole : ByteArray) : Nat :=
  whole.size - e.remaining.size          -- size of the unconsumed prefix
```

The position is the **length of what was *not* consumed** — a consequence of
the return-the-rest design, with `position ≤ size` as a theorem, *not* an
asserted bound.  No `Nat` cursor, no `dec_err_bound` lemma.

Roundtrips are **theorems about `Rel`**, stated once and uniformly (whole input;
`decode` is a total function, `encode` is partial, and the bidirectional law
holds *on the unambiguous domain*):
- **bidirectional (soundness/completeness)**:
  `Unambiguous d → (Rel d x s ↔ decode d s = .ok (x, empty))`,
- **roundtrip**: `encode d x = some s → decode d s = .ok (x, empty)`.

Soundness (right-to-left) is unconditional; completeness (left-to-right) is the
half that needs `Unambiguous` — that is *why* the hypothesis appears on the
bidirectional law and not on the roundtrip.  These two are the *only*
roundtrip-shaped facts core states (T4.2/T4.3).

(Any higher-level codec — e.g. the future `lean-text` — obtains its own
roundtrip **by composition over `$`**, inheriting these laws; core needs no
special semantics for it.)

**Where the equivalence guarantee lives — on *every* codec, by construction.**
The inverse guarantee is *structural and universal*, not a per-combinator or
per-value extra: (a) the `Iso` inverse `law` is a **field**, so no `Iso` can
exist without its proof; (b) every `Codec` is a **composition of `Iso`s** via
`$`/`*`/`|`/`pure`/`byte` — there is no constructor for an *unverified* codec;
and (c) the roundtrip is a **closed theorem** over the single `Codec` type:
`codec_roundtrip : ∀ d x s, encode d x = some s → decode d s = .ok (x, empty)`
(the paper's roundtrip, with encode-success as the well-formedness premise),
proved once (T4.3) and instantiated for every codec for free.  Consequently
**there is no "verified vs unverified" tier** — `Codec` is proof-carrying by
construction, and the guarantee needs no separate wrapper to be surfaced: a
theorem *is* a term in Lean, so callers obtain the proof via `#check
codec_roundtrip` (or the per-`Iso` law) directly.  The guarantee is in the
*types*, not a field to be asserted per value.

### Layer 3 — the core is *pure framework*; no domain-specific leaf codecs

`codec` ships **no domain-specific leaf codecs** — not even `u8`.  The only
descriptions are the two primitives `pure` and `byte : Codec UInt8`, plus the
`$`/`*`/`|`/`empty` combinators.  There is deliberately no `u8`, no endianness,
no `bytes n`, no `varint` — not even as a "courtesy" — because every such leaf
is trivially constructible downstream by composition (`u8` is literally `byte`
with an identity `subset`; `bytes n` is `count n`; `varint` is a primitive `Iso`
in the consumer).  The *first* downstream leaf is the acceptance test that the
framework is genuinely expressive, which is strictly stronger than a seed leaf
buried in core.

There is **no Layer 4**.  Text/string/Unicode (`lean-text`) and the binary leaf
family (`lean-binary`) are both *downstream* packages built by composition, not
core concerns.

## Efficiency (a hard requirement, not deferred)

- **`ByteArray` + return-the-rest** for decoding: O(1) `get!`/`extract`, no
  per-byte boxing, no list backtracking (perf claims unconfirmed until T6
  benchmarks).  No `Nat` cursor — the remaining-bytes value *is* the position.
- **`ByteArrayBuilder`** for encoding: amortized O(1) append.
- **C/LLVM extraction** (`clang` present); `Prop` proofs erase.

**Acceptance test** (belongs to a leaf library — see Scope — not core): a
`#eval`/benchmark of a varint + length-prefixed record roundtrip on a multi-MB
binary input, linear time with small constant, no per-byte boxing — *measurable*,
not asserted.  Core's own acceptance is structural: the roundtrip/`Rel` theorems
close for the `Iso`/`Codec` laws with no leaf codec needed.

## Scope

This deliverable is the **core `codec` library** — small, focused, built for
perfection, 100% provable.  It contains `Iso`, `Codec`, `Rel`, the two
interpreters, error reporting, and the laws.

**Out of scope: every concrete format.**  Leaf libraries (`lean-binary`:
`u8`/endianness/`varint`/`bytes n`; `lean-text`: `utf8`/`text`/whitespace; …)
are **separate git repositories**, each with its own openspec proposal, and are
**not part of this deliverable**.  They are mentioned here only as the intended
*consumers* of the core, to state the direction — never as requirements or
tasks of this repo.

## Dependencies

- **Lean 4.30.0** + **lake 5.0.0** (present), `clang`/`gcc` for extraction.
- **No mathlib.** `ByteArray`, `UInt8/16/32/64`, `Array`, `List`, `Option`,
  `Nat.div/mod`, `Nat.div_add_mod`, `Nat.mod_eq_of_lt` are all stdlib (verified
  via `#check`).  (`Equiv`/`PEquiv` are mathlib; our `Iso` is a *thin, stdlib-
  only* re-derivation of the paper's partial-isomorphism concept, not a reuse
  of any mathlib structure.)

## Risks

| Risk | Likelihood | Mitigation |
|---|---|---|
| `chainl1`/`foldl`-as-`iterate` (§5.2/5.3) subtlest proof | medium | port exactly as paper (`iterate ∘ step`), prove `iterate` once |
| `ByteArray` ops opaque to `simp` for the `Rel` proofs | medium | reason over a spec-level `ByteArray` model and transport (T0.5 is a proof-tactic concern, not part of the signature) |

## Deliverables & accept criteria

1. A `lake`-buildable package `codec` in `./`.
2. `Iso` with a proved inverse law + `Category`/product instances (§5.1).
3. **One byte-only `Codec`** (`$`/`*`/`|`/`empty`/`pure`/`byte : Codec UInt8`) with
   two interpretations: deterministic `decode` (returns value + remaining bytes),
   partial builder `encode`.
4. `Rel` denotational semantics over `ByteArray` + roundtrip/bidirectional
   theorems (no `sorry`, stdlib axioms only).
5. Derived combinators (`many`, `*>`, `<*`, `between`, `chainl1`, `foldl`/`iterate`)
   — **no domain-specific leaf codecs** (`u8`/endianness/`varint`/`bytes n` are all downstream in
   `lean-binary`; `utf8` in `lean-text`).
6. `README.md` stating the guarantee ("one description = one relation; decode and
   encode are its two directions, inverse by construction"), the pure-framework
   scope, and the two downstream consumers (`lean-binary`, `lean-text`).

## Sequencing

```
T0 spike (Iso law + transport) ─▶ T1 Iso + category ─▶ T2 Codec (bytes)
                                ─▶ T3 two interpreters (decode / encode)
                                ─▶ T4 Rel + roundtrip theorems
                                ─▶ T5 derived combinators (no leaves)
                                ─▶ T6 benchmark/extraction ─▶ T7 docs+gate
```

`T5` provides the *generic* combinators (`many`/`*>`/`<*`/`between`/`chainl1`/
`foldl`/`iterate`); leaf codecs (`u8`/endianness/`varint`/`bytes n` in
`lean-binary`, `utf8` in `lean-text`) are **downstream**, not core tasks.

T1 is the only hard dependency (everything builds on `Iso`); T3.3 (unambiguity)
is a hard gate for T4's `Rel` theorems; T5 is the speed story.

## Open questions (resolve in T0; law-shape and byte-core are design decisions)

1. **`Codec` is a typeclass (decided).**  Matches the paper's own §3.4 "class
   of syntax descriptions" and its `IsoFunctor`/`ProductFunctor`/`Alternative`
   superclasses; the two interpreters are instances.  (A `structure` is the
   fallback only if instance resolution proves unusable — not expected.)
2. **`ByteArray` proof strategy (preference recorded).**  Prefer direct `simp`
   over `ByteArray.get!/extract/size`; fall back to a `List UInt8` model +
   transport lemma only if the direct proofs get stuck (ergonomics only; the
   API stays `ByteArray`).  Confirmed empirically during T4, not a blocking T0
   decision.
3. **Exact `Unambiguous d` predicate.**  Its shape is already fixed —
   `Unambiguous d := ∀ s, at most one x with Rel d x s` (see T3.3) — and it is a
   **per-demo proof obligation**, not a library-decidable property.  The only
   residual question is the exact proof *strategy* per demo (image header,
   Protobuf framing), not the predicate itself.
