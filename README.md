# codec

A verified, bidirectional codec library: **one description, two directions.**

`codec` takes Rendel & Ostermann's _"Invertible Syntax Descriptions: Unifying
Parsing and Pretty Printing"_ (Haskell Symposium 2010) and carries it further —
**more dependently typed, more provable, and binary.** The paper gives the idea:
one description, two directions, related by invertibility. `codec` is the same
idea, finished.

## The idea, in one breath

The value-level transformations in a syntax description are **partial
isomorphisms** — a box with two doors, `apply` and `unapply`, that are each
other's inverse (`iso i d` is the `Codec` constructor that wraps one, while
`seq`/`alt`/`empty`/`pure`/`byte`/`satisfy` supply the structure). If you
know how to go _into_ the box, you automatically know how to come back out,
because the two doors are the same fact stated twice. So one description drives
**two directions** at once:

- **decode** — bytes in, value out (the parser);
- **encode** — value in, bytes out (the pretty-printer);

and the two directions are _provably_ inverse, not just documented as such.

Where the paper _states_ that inverse law in prose (and notes, almost as an
aside in §7.5, that it "would be interesting to see" it encoded dependently),
`codec` makes it a **field of the type**: you cannot construct an isomorphism
without its proof, and the roundtrip — `encode d x = some s → (x, []) ∈ decode d s` — is a **closed theorem**, holding **unconditionally** for every
description. Invertibility is enforced by the type system, not by a comment.

`codec` also re-bases the idea from text (`String`/`Char`) onto **bytes**
(`UInt8`), so it covers fixed-width integers, endianness, and image files — with
text rebuilt downstream, _on top of_ bytes.

The proofs live in the code (`Codec/*.lean`, each declaration documented in
place) and the engineering state in `openspec/`; this document is the
**architecture statement** — the complete record of where `codec` stands
relative to the paper, and why.

---

## From the paper to a binary codec

This is the canonical, complete record of every place `codec` departs from the
paper (a _departure_ — an observable-semantics change) or completes it (a
_strengthening_ — no observable-semantics change). Each entry cites the paper's
§ and the Lean symbol that implements it, so a porter can read this one list and
know exactly what to reproduce. Anchors `[D1]`–`[D8]` and `[S1]`–`[S6]` are stable
cross-reference targets, shared with the code and the design docs.

Section numbers below refer to the paper's own sectioning as reproduced in
`PAPER.md` (the paper uses a mix of `§n` and `§n.m`; where a fact lives in a
subsection we cite the subsection).

### Departures (observable-semantics changes)

**[D1] `String`/`Char` → bytes — bytes become the base unit.**
The paper's concrete syntax is textual. The decoder is `Parser (String → [(α,
String)])` (§4.1) and the primitive token is `token` over `Char`; the value graph
is given as `Rel :: [(α, String)]` (§4.3). `codec` targets binary, so the base
unit is `UInt8`, the base string is a byte sequence, and `byte : Codec UInt8` is
the `token` analogue. Text/Unicode is rebuilt downstream (`lean-text`) on top of
bytes, not in core. **One byte-string type, one job** (see
[Representations](#representations-one-length-indexed-byte-string)): the _spec_
substrate is the single length-indexed `Bytes n := Fin n → UInt8`, which is
structurally reducible for proofs **and** a scalar indexed load at runtime — there
is no separate `List` spec and no `ByteArray` run-model slab _for the specification
carrier_ (`decode`/`encode`/`Rel` and the laws). The packed (`Array UInt8`) and
byte-slice (`ByteArray`) carriers in `Codec/Packed.lean`/`Codec/ByteSlice.lean` are
proved-equal or trust-seam _implementations on top of_ that single spec — see
[Performance](#performance-two-proof-layers-and-an-honest-ceiling).

**[D2] The nondeterministic list decoder.** The paper's decoder returns a _list_
of `(value, remaining)` pairs — a relation (§4.1 `Parser (String → [(α, String)])`,
§4.3 "decoding … the graph"). `codec` keeps it that way: `decode` returns all
`(value, remainder)` pairs, and `|` is list concatenation.

**[D3] `|` is the paper's _backtracking union_, not committed choice.**
`decode (d₁ | d₂) s = decode d₁ s ++ decode d₂ s`, matching `Rel (d₁ | d₂) = Rel d₁ ∨ Rel d₂` by construction. (The paper itself treats the two directions asymmetrically: its _parser_ `|` is backtracking union (`++`, §4.1) while its _printer_ `|` is left-biased `mplus` (try left, else right; §4.2). `codec` keeps the **relation** backtracking — that is the single source of truth — and lets `encode` inherit the printer's left-bias naturally, so `Rel` and `decode` agree by construction and nothing rounds through a committed choice.)

**[D4] Lossless capture — a destructive constructor such as the paper's
`ignore` is _impossible_ under strict isomorphism.** The paper (§6.3) defines
`ignore :: α → Iso α ()` and, in its own words, notes it is "again **not a strict
partial isomorphism**": it maps _any_ run of blanks down to a single unit value
and, on printing, emits a **fixed, single** representation back — so an
arbitrary-length whitespace run is not preserved, and the inverse invariant
holds only "modulo equivalence classes" (§3.1) rather than literally. (`skipSpace`
and `optSpace` in §6.3 are the two direct instantiations of `ignore`;
`sepSpace = text " " ∗ skipSpace` composes it — all three share the same
one-way-lossy whitespace shape.) Because every `codec` combinator is a **strict** partial
isomorphism — `Iso.law` is a field, `apply a = some b ↔ unapply b = some a` — we
**cannot follow the paper's destructive constructor**: a lossy `ignore` cannot
inhabit `Iso`, since two distinct inputs mapping to one output make `unapply`
unable to invert both. So instead of relaxing the law to admit `ignore`, a run of
allowed bytes is _captured_ as a value and re-emitted verbatim (realized by
repetition over a `subset p byte` step, not a new primitive). There is therefore
**no `ignore` combinator in core**, and the strict inverse law holds
unconditionally.

**The diagnosis, sharpened (normal forms).** `ignore` cannot inhabit `Iso α S`
_because it is not an `Iso`_ — it is the lossy _half_ of a codec whose honest
object is a bijection with the **quotient of the concrete syntax by the
information-free variation**. A format often accepts several spellings of one
value (RFC 4648 §8: a Base16 decoder MUST accept both `6F` and `6f`, since case
carries no information), so the quotient is `S/~` where `s ~ t ↔ norm s = norm t`
for a total idempotent `norm`. `codec` puts that quotient in the **object** rather
than relaxing the law in the **morphism**, which is the one thing `[S1]` forbids:
`Codec/Normal.lean` supplies `Normal S norm` (the fixed points of `norm`, a type)
and `Normalizer S norm` (carrying `norm`'s idempotence), so
`Iso α (Normal S norm)` is an **ordinary `Iso`** with its `law` still a field. The
lossy direction is `decodeNormal`, the normalizer composed _outside_ the `Iso`: it
accepts input the `Iso` rejects, has no inverse, and is explicitly not a codec
value. Capture-verbatim is then simply the **identity normalizer** — the degenerate
case of the layer, not a prohibition on having one. Two consequences worth stating:
the layer is **length-preserving** (`norm : Bytes n → Bytes n`, so case folding fits
and collapsing a whitespace run does not — that needs a different carrier), and a
codec using it owes the per-instance fact that its encoder emits a normal form,
without which the normalising decoder can fail on its own encoder's output.

**[D5] `|` needs no prefix-disjointness condition.** Some deterministic-parser
designs require `|`'s branches to be _prefix-disjoint_ so at most one can match a
given input. `codec` requires none — and admits none: with `|` as backtracking
union, the branches are tried independently and concatenated, and no prefix
condition could work for repetition anyway (`[]` is a proper prefix of every
non-empty string, so `nil | cons` is never prefix-disjoint).

**[D6] `Codec` is a description _value_, not the §3.4 typeclass.** The paper
embeds syntax descriptions polymorphically (a `Syntax` typeclass, with `$`/`∗`/
`|`/`pure`/`token` as methods). `codec` instead makes `Codec` an inductive AST
(iso`/`seq`/`alt`/`empty`/`pure`/`byte`/`satisfy` as constructors), so a description is an
ordinary value you can hold and **structurally recurse over** — which is what
makes "proved for every description" a real, finite induction rather than a
promise.

**[D7] `iterate` (paper §5.3, the backward-run step of the §5.2 foldl machine) is
deliberately omitted.** Its forward- and
backward-iteration fixpoints need not coincide, so no inverse law exists without
a per-element "chain-isolated in both directions" precondition. We provide
`foldl`/`foldr` directly (well-founded recursion) and omit `iterate` rather than
ship a subtly-unsound law. `foldl` is the combinator `chainl1` actually needs.

**[D8] `pure`/`element`/`subset` carry a _decidable_ witness, not the paper's
`Eq α`/`(α → Bool)`.** The paper's `Eq`/`Bool` checks become `[DecidableEq α]`/
`[DecidablePred p]` — the same _job_ (a check the printer performs), but
_decidable and proof-backed_ rather than a free-form `Eq` or an unverifiable `Bool`.

`encode` being _partial_ is **not** a departure — it is the paper's `Maybe`
printer kept as-is: `empty`/`pure x`/`subset p` reject out-of-domain values, and
we deliberately do **not** totalize it.

### Strengthenings (we complete the paper, without changing its meaning)

**[S1] `Iso.law` is a _field_, and it holds _unconditionally_.** The paper §3.1
states the inverse invariant in prose, unchecked; §7.5 muses about encoding it
dependently. `codec` does it: the law is a required field, and because `[D4]`
removes the lossy `ignore`, the strict law holds for **every** core `Iso` — the
structural ones with no precondition, and `foldl`/`foldr` with a well-foundedness
witness the caller supplies.

**[S2] Format-agnostic naming.** `Syntax`/`parse`/`print`/`token` are the paper's
text vocabulary; on bytes they mislead, so they become `Codec`/`decode`/`encode`/
`byte`. A rename only.

**[S3] Zero domain-specific leaf codecs.** Core ships only the primitive leaves
`byte` and `satisfy` (plus the non-leaf `pure`, which is a value-equality
check, not a format);
every concrete format (`u8`/`utf8`/`varint`/…) lives downstream (`lean-binary`,
`lean-text`). Nothing in core can silently bake in a text- or machine-specific
assumption.

**[S4] `foldl`/`foldr` are _fresh_ well-founded derivations, not `inverse ∘ foldl ∘ inverse`.** The right-fold dual is a distinct definition (the obvious
`inverse ∘ foldl ∘ inverse` is type-incoherent for the step type). Both take a
decreasing-measure witness — a _precondition_, not an unconditional law like the
structural isos.

**[S5] `relRepeat`'s least-fixpoint status is _proved_, not asserted.** The
repetition denotation is the least relation closed under the `nil`/`cons` rules;
an induction principle makes "least fixpoint" a theorem rather than a claim.

**[S6] Unbounded `many` is _semantic_, not a `Codec` value — a strictness
consequence, not a naming choice.** The paper is a **lazy** language, so `Rel`'s
meaning "will generate and concatenate infinite lists" (§4.3) and its two named
list combinators — `many` (§3.4) and `chainl1` (§6.1, itself `foldl f $ arg ∗ many
(op ∗ arg)`) — are ordinary **values**. Lean is **strict**: a finite AST node cannot
contain an unbounded repetition, so `codec` does not try. Repetition lives instead
as **three separate artifacts** — a
denotation (`relRepeat`), a decoder (`decodeRepeat`), and an encoder — rather than
a single `many` value; `chainl1` is re-derived over those three, and `codec`
_additionally_ derives `sepBy`/`chainr1` (one-or-more, zero-or-more) in the same
§6.1 style — the paper defines no `sepBy`/`chainr1`, so these are `codec`'s own
faithful additions, not a reproduction. None of these exist as bare
`Codec`-building symbols. This is the same semantic content for `many`/`chainl1`,
but it is a _language_ difference (laziness vs strictness), not merely a cosmetic
naming change.

Everything else is **kept**, and kept strongly: `Rel` is preserved as the
_specification_ (decoding is the paper's full relation, nothing narrowed on top),
and partial encoding is preserved.

---

## Representations — one length-indexed byte string (the spec substrate)

`codec`'s **specification carrier** is one byte-string type, the length-indexed
`Bytes n := Fin n → UInt8`. The length `n` is part of the _type_, so the byte count is
known without an auxiliary length field. The read `s ⟨i, ·⟩` is a **structural indexed
load** — it reduces under `simp`/`rfl`/`induction` for proofs and lowers to a scalar
indexed load in the emitted IR. There is no second `List UInt8`/`Array`/`ByteArray`/
`Buffer` carrier _for the spec_: every law is stated over `Bytes n`. (The packed
`Array UInt8` and byte-slice `ByteArray` carriers exist only as proved-equal or
trust-seam implementations on top of this spec — see
[Performance](#performance-two-proof-layers-and-an-honest-ceiling).)

|                    | **`Bytes n`** (`= Fin n → UInt8`)                                                             |
| ------------------ | --------------------------------------------------------------------------------------------- |
| **Job**            | the single _specification_ substrate (proof) and its scalar-read run-model                    |
| **Shape**          | a length-indexed function; `s ⟨i, ·⟩` is a structural read, no `List` cons cell               |
| **For the prover** | reducible under `simp`/`rfl`/`funext`; decidable equality is finitary (`funext` over `Fin n`) |
| **At runtime**     | a scalar indexed load — the length `n` is a _type_ index, not a boxed `Nat`                   |

**The decision.** Every law (`Rel`, `decode_spec`, `bidir`, `roundtrip`, …) is stated and
proved over the single `Bytes n`, because that one type is both what the proof assistant
can reduce _and_ what lowers to a scalar indexed load. `decode d (s : Bytes n)` returns
`List (α × Suffix n)` where a `Suffix n` carries the remaining length (a `m ≤ n` witness)
and the remaining `Bytes m`; `encode d x` returns `Option ({n : Nat} × Bytes n)` — the
encoded bytes and their length in one sigma.

The single-carrier collapse is the fix for the defect that the earlier efficiency
attempts shared: they split the carrier (a `List`/opaque `ByteArray` slab pair) and
then paid for `Classical.choice`-leaking `Array.extract`/`Array.toList` transport lemmas
at the seam. One length-indexed byte string removes that split and its leaks for the
_proof_ substrate. **The carrier split was never the strategy; it was the defect.**
(The performance change re-introduces a `ByteArray` accumulator _only_ as a proved-equal
implementation, in two layers with **distinct proof status** — see
[Performance](#performance-two-proof-layers) — keeping `Bytes n` as the specification
every law is stated over.)

---

## Why these choices — the reasoning in lay terms

This section explains the _reasoning_, for a reader who does not write Lean (or
who is porting `codec` to another language). No claim here goes beyond the
statement above; this is the "why", so a non-Lean reader can judge the
trade-offs rather than just copy the names.

### The one big idea first

The paper's core insight is that one _description_ drives _two directions_ by
making every block a **partial isomorphism** — a box with two doors that are each
other's inverse. The paper _says_ the doors are inverse but never _checks_ it.
`codec` turns that promise into a **field**: you cannot build the box without
supplying the proof that the doors undo each other. That one move — from
"documented in prose" to "enforced by the type" — is `[S1]`, and almost every
other choice below is a consequence of making that move _honest_.

### `[D1]` bytes instead of characters — why it matters

The paper's smallest unit is `Char`. For a tiny calculator language that is fine,
but a _binary_ format — an image, a network packet — is not made of
characters; many of its bytes are not printable at all, and pretending everything
is a `Char` forces you to smuggle binary data through a text type that fights you
at every step. So `codec` moves the base unit down to a single byte and the base
string to a byte list; text becomes a downstream concern (`utf8` maps `String`
onto bytes) — on _top_ of bytes, not underneath. Nothing about the framework
changes; only the ground floor does.

The **spec substrate is the single length-indexed `Bytes n := Fin n → UInt8`**: it
is a reducible, length-indexed function, so every `Fin`/`funext` lemma applies and
every law is a finite induction, **and** it lowers to a scalar indexed load in the
emitted IR — no second carrier, no transfer lemma _for the laws_. So the
_specification_ has one byte-string type: **`Bytes n` is the proof substrate and
its own scalar-read run-model** (the length is a _type_ index, not a boxed `Nat`).
"The model you prove on" and "the model you read at speed" are the same thing. (The
packed `Array`/`ByteArray` carriers sit _above_ this substrate as proved-equal or
trust-seam implementations; the laws never leave `Bytes n`.) — see
[Representations](#representations-one-length-indexed-byte-string-the-spec-substrate).

### `[D2]` + `[D3]` the decoder returns a _list_, and `|` means "try both, keep

all" — why backtracking is non-negotiable

A parser answers "does this input match, and what value does it produce?". A
**committed-choice** `|` tries the left branch and, if it grabs something, stops
— quick, but it throws away the other branch's answers. A **backtracking-union**
`|` tries _both_ and returns _all_ the possible results. The paper's `|` is the
second kind: it is literally the _union_ of two result lists (§4.3), and the
parser returns _every_ way to read the input.

Backtracking is not merely the paper's choice — it is the _only_ choice that is
compatible with repetition. `many p` is "zero or more `p`s", naturally
`empty | (p then many p)`: "match nothing, or match one `p` and recurse". Under
committed choice the "match nothing" branch always succeeds immediately (it
consumes zero input), so the parser always stops there and returns `[]`, never
reading even one `p`. The empty string is a prefix of _every_ string, so no
reordering or "disjointness" bookkeeping can fix it. So `codec` keeps the paper's
semantics exactly, and the roundtrip laws hold **unconditionally** — because the
decoder and the denotation agree _by construction_. The cost is the paper's own
admitted cost (§4.4): naive backtracking is exponential in the worst case; making
it fast without changing what it means is a separate, later problem.

### `[D4]` lossless capture — why we cannot follow the paper's destructive constructor

The paper's `ignore` maps _any_ run of whitespace down to a single value and, on
printing, always emits _one_ (fixed) run back — `skipSpace` re-emits none,
`optSpace`/`sepSpace` re-emit a single blank, but none of them preserves the
original length. That is one-way loss: three spaces in, a fixed run out. The paper
accepts this and says the inverse law holds only "modulo equivalence classes".

`codec` cannot do that — not as a preference, but as a **consequence of the
isomorphism itself**. Every `codec` building block is a strict partial
isomorphism, and the inverse law is a _field_ you must supply to construct one. A
lossy combinator like `ignore` cannot satisfy that field: it sends every run of
whitespace (any length) to the same value, so `unapply` cannot recover which run came out of a given result. There is no round-trip at all — `decode "   "` and
`decode ""` both give the same value, so `encode` cannot tell them apart and
`encode (decode s) = s` fails for every non-canonical `s`. Because `codec` is
isomorphic _by the type of its combinators_, it simply **cannot include
`ignore`** — the constructor would not typecheck (no proof exists for it).

So instead of following the paper's destructive combinator, a run of optional
bytes is _captured_ and re-emitted verbatim — same length, same bytes — so parse
and print are a genuine byte-for-byte two-way street. Where the paper relaxes the
law to keep `ignore`, `codec` keeps the law _strict_ and therefore has no
`ignore`.

### `[D5]` no prefix-disjointness gate

Some deterministic parsers require `|`'s branches to be _prefix-disjoint_ — to
never both match strings where one is a prefix of the other — so "commit to the
first success" stays deterministic. `codec` needs no such gate, and could not have
one: it is incompatible with the paper's repetition, because the two branches of
`many p` are **never** prefix-disjoint (`[]` is a prefix of every non-empty
string). With `|` as backtracking union, the branches are tried independently and
concatenated, so there is nothing to keep disjoint.

### `[D6]` a description is a _value_ — why the paper's typeclass hides the thing

we need to prove about

In the paper, a description lives _inside the type system_: a typeclass, with "a
parser" or "a printer" chosen by context. You never hold a description in your
hand; it is implicit. `codec` makes `Codec` an explicit **tree** (seven
constructors), so a description is an ordinary value you can pattern-match on and
**structurally recurse over**. Every roundtrip proof works case-by-case over the
seven constructors — and that finite induction is _the_ thing that makes "proved
for every description" mean something. A typeclass gives you no finite list of
cases to exhaust.

### `[D7]` why there is no `iterate`

The paper builds `foldl` out of `iterate` — "apply this step until it fails"
(and, reversed, unapply it). The subtle problem: applying forward until it stops
and unapplying backward until it stops can land on **different** stopping points,
because "apply succeeds ↔ unapply succeeds" does not mean "apply fails ↔ unapply
fails". To ship `iterate` as an isomorphism you would have to _claim_ the two
fixpoints agree — false in general — or burden every caller with a fragile
precondition. `codec` omits `iterate` and defines `foldl`/`foldr` _directly_ by
well-founded recursion (each step strictly decreases a measure, which _is_ the
honest guarantee). `foldl` is all `chainl1` needs, so nothing is lost and no
unsound law is shipped.

### `[D8]` decidable checks instead of `Eq`/`Bool`

The paper's `pure`/`element`/`subset` ask "is this the value I should match?" via
Haskell's `Eq` or a `Bool`. In `codec` those become _decidable, proof-backed_
witnesses: a procedure that, for every value, either proves the match or proves
its denial — never "maybe". The job is the same; the difference is that the
encoder's "compare and branch" is a provable step rather than an unverifiable
`if`.

### `[S1]` the law is a field — why this is the whole point

Covered above: the paper muses that encoding the invariant "would be interesting
to see"; `codec` does it. The concrete benefit is that _soundness is impossible
to forget_ — you cannot accidentally construct a broken isomorphism, because the
constructor will not typecheck without the proof.

### `[S2]` + `[S3]` renaming, and an empty-of-leaves core

Naming (`token`→`byte`, `parse`/`print`→`decode`/`encode`) keeps the text-world
vocabulary from leaking onto bytes. The scope decision (`[S3]`) keeps core empty
of concrete formats, so nothing in it can silently assume text or one machine's
endianness; the first downstream leaf (`u8`, literally just `byte`) is the smoke
test that the framework is genuinely general.

### `[S4]` `foldl`/`foldr` are fresh, and need a termination witness

`foldr` is not `foldl` with the arrows flipped — the obvious `inverse ∘ foldl ∘ inverse` does not even typecheck, because the step's types swap order. So it is a
separate definition. Both folds take a measure plus a proof that each step
_strictly decreases_ it — the honest termination guarantee, a precondition the
caller supplies, unlike the _unconditional_ laws of the structural isos. A porter
knows exactly what their language's `foldl` must also require: a decreasing
measure, not just a recursive function.

### `[S5]` + `[S6]` repetition is _semantic_, and its least-fixpoint status is

proved

"Zero or more" is the one place a description would have to be _infinite_. A
**strict** language cannot hold an infinite description (the paper, being lazy,
can), so `codec` does not try: `many` is **not** a node at all. Its three uses are
spelled out directly — the _meaning_ (a relation that is the _least_ thing closed
under "empty, or one more element"), the _decoder_ (which requires each step to
consume a byte so it terminates), and the _encoder_ (which recurses on the value
list, so it needs no condition). `[S5]` proves "least fixpoint" rather than
asserting it; `[S6]` records the structural consequence of strictness — there is
no `sepBy`/`sepBy1`/`some`/`many1` **value**, only the relation/decoder/encoder
triple, and the `sepBy` triple has "one or more" (non-empty) semantics. A porter
should look for these three readings, not for a `many` object.

---

**Bottom line for a porter.** The paper gives the idea; `codec` makes it _honest_
by (1) enforcing the inverse law as a type, (2) resting on bytes, (3) keeping the
full backtracking semantics so the laws are unconditional, (4) being strictly
isomorphic — which _rules out_ the paper's destructive (`ignore`-shaped)
constructors rather than needing to drop them by hand, and (5) making the
description an ordinary value you can induct over. Reproduce those first; the
rest is bookkeeping you can re-derive.

## The abstraction, in brief

```lean
-- partial isomorphisms: two directions, one law, carried as a field
structure Iso (α β : Type) where
  apply   : α → Option β
  unapply : β → Option α
  law     : ∀ a b, apply a = some b ↔ unapply b = some a

-- a description is a value built from these combinators
--   $ : Iso α β → Codec α → Codec β      (apply an iso)
--   * : Codec α → Codec β → Codec (α × β) (sequential / product)
--   | : Codec α → Codec α → Codec α      (backtracking union)
--   empty / pure / byte / satisfy        (failure / fixed value / one byte / guarded byte)

-- the length-indexed byte string (the single spec substrate and its scalar read)
--   Bytes n := Fin n → UInt8 ; s ⟨i, ·⟩ is a structural indexed load

-- one description, two interpreters (the substrate is `Bytes n`)
--   decode : Codec α → {n : Nat} → Bytes n → List (α × Suffix n)  -- all (value, rest) pairs
--   encode : Codec α → α → Option ({n : Nat} × Bytes n)           -- partial, length + bytes

-- the laws that make it a codec
--   Rel d x s ↔ (x, Suffix.empty n) ∈ decode d s     (bidirectional)
--   encode d x = some ⟨n, s⟩ → (x, Suffix.empty n) ∈ decode d s (roundtrip, unconditional)
```

Every `Codec` is built by structural induction over the seven constructors
(`iso`/`seq`/`alt`/`empty`/`pure`/`byte`/`satisfy`); `iso` is the single
constructor that wraps an `Iso`, so the inverse guarantee is **structural**:
the law is a field, and the two theorems above hold **unconditionally** for every
description — no solver, no per-combinator gate, no prefix-disjointness condition.

## Scope

- **`codec`** (this package): the pure framework — `Iso`, `Codec`, `Rel`, the two
  interpreters (the single `Bytes n` substrate), and the laws. **No
  domain-specific leaf codecs** (not even `u8`).
- **`lean-binary`** (downstream): `u8`, `u16le`/`u16be`, … , `varint`,
  `lengthPrefix`, image/Protobuf demos, and the speed benchmark.
- **`lean-text`** (downstream): `utf8` plus `text`/`identifier`/`whitespace` —
  the paper's §6 text domain, re-based on bytes.

## Performance — two proof layers, and an honest ceiling

The speed story has three parts: a packed result carrier (Layer 1), a generic
bulk-byte trust seam (Layer 2), and a **hard ceiling on pure-Lean parsing** that
the first two do not remove.

The packed result carrier (see `Codec/Packed.lean`) gives the interpreter a
contiguous-buffer fast path, in **two layers with distinct proof status** that are
never conflated:

- **Layer 1 — proven, zero trusted C.** The packed decoder/encoder (`decodeArray` /
  `decodeFullArray` / `encodeArray` / `encodeByteArrayBytes`) and their refinement
  theorems (`decodeArray_eq`, `decodeFullArray_spec`, `encodeArray_eq`,
  `encodeByteArrayBytes_eq`), each `[propext, Quot.sound]`-only, zero
  `Classical.choice`, zero `sorry`. These are the **only** layer admitted to the
  `#print axioms` gate.
- **Layer 2 — a named trust seam.** `byteSlice` / `blitBytes` / `findByte` /
  `commitRemainder` (in `Codec/ByteSlice.lean`) are `memcpy`/`memchr`-style byte
  operations. Each is `@[extern "…"]` with an **elaborating Lean body** that pins
  the intended meaning and reduces in proofs — but the **running C** in
  `Codec/ByteSlice.c` is **trusted, not proven**.

  An important, frequently-misread point: `#print axioms <seam>` reporting
  "no axioms" is **by construction** and says **nothing about the C**. `@[extern]`
  swaps only the _emitted_ C; Lean's kernel sees only the pure body, so the axiom
  check cannot see the C symbol at all. The body being `[propext, Quot.sound]`-clean
  is a fact about the _spec_, not evidence that the C implements it. Layer 2 is
  therefore **excluded** from the `#print axioms` acceptance entirely, and its
  contract is a named prose promise — "the C matches the Lean body byte-for-byte" —
  that is re-checked empirically (byte-for-byte value checks in the bench), never
  proved. "No axiom" is **never** "no trust."

  Every seam nevertheless carries its **own** Lean law pinning that body —
  `byteSlice_spec`, `blitBytes_spec`, `findByte_spec`, `commitRemainder_spec` — so
  the C's contract names a theorem rather than "read the definition". Any consumer
  or bench cites the law instead of re-deriving the body. The laws are not uniformly
  axiom-free: `findByte_spec` reports `[propext]` (its `Array.findIdx?` scan goes
  through `DecidableEq UInt8`), and the other three report none. That difference is
  recorded at each law, not treated as drift — `[propext]` is inside the gate.

  The seams are **generic** bulk byte movement, not semantic parsers: `byteSlice`
  (suffix `memcpy`), `blitBytes` (buffer-to-buffer `memcpy`), `findByte` (`memchr`),
  and `commitRemainder` (a `USize`-indexed `byteSlice` wrapper). There is **no C
  that parses digits, numbers, fields, or format structure** — all codecs are pure
  Lean; the C surface stops at "copy/scan these raw bytes." (This is a hard design
  rule, not an implementation detail.)

The proven `decodeFullArray` (Layer 1) deliberately still builds its suffix via
the `List.toArray.drop` transport (an axiom-clean body, not a trusted
`@[extern]`), so Layer 2 remains distinct from and never conflated with Layer 1.
A "named trust seam" boundary that is only _believed_ to match `Array.extract`'s
out-of-range clamping — not yet reconciled clause-by-clause at the spec level — is
an open contract to tighten, not a proof gap to hide: see the engineering ledger
for the reconciliation task.

### The honest ceiling (what two layers do _not_ buy)

Measured this session, the **pure-Lean** interpreter — even the packed Layer-1
carrier — bottoms out around **20–40× slower than hand-written C**, and this is a
_compiler-backend_ limit, not a code-shape limit. `Nat`/`UInt8`/`UInt64` arithmetic
all lower to boxed, heap-allocating operations (`lean_nat_mul`, `lean_uint8_to_nat`,
`instAddUInt64`), and `USize` is an unboxed `size_t` **only as an `@[extern]`
argument**, never once it is stored in a returned product/`Option`. There is no
pure-Lean escape: rewriting a parser to thread a `USize` cursor made it _slower_.
The concrete canary — an RFC 3339 date-time (`parse`/`print` over a `ByteArray`) —
parses at a few hundred ns/op where the equivalent `clang -O2` C parser is ~10 ns/op.

The consequence, recorded as a standing decision: **pure-Lean codecs are the spec
and accepted at ~20–40× C speed**; the only C-speed regions are the generic
`memcpy`/`memchr` seams above; anything whose hot loop is arithmetic (say, numeric
parsing) is a downstream FFI concern, not a core codec. The packed carrier removes
the _result_ allocation (nested `concat` closures per element) — a real,
proved-equal win — but it does **not** move the per-element scalar arithmetic off
the boxed heap, so it does not close the gap to C.

Measured (current `bench`, `[measured]`, never hand-typed; all figures are the
bench's own, and note the toolchain does not stabilize wall-clock well — see the
engineering ledger on benchmark noise): the Layer-2 `byteSlice`/`blitBytes`/
`findByte` seams run at the `memcpy`/`memchr` floor (tens of GiB/s moving bulk
bytes), while the pure-Lean bulk `fastEncodeRepeat`/`encodeRepeat` and the RFC 3339
`parse`/`print` sit in the tens-of-MiB/s / hundreds-of-ns range — around the
boxed-scalar floor, as above.

## Getting started

The build toolchain (Lean 4 + the `openspec` CLI) comes from the Nix flake:

```bash
nix develop      # enter the dev shell
lake build       # compile + verify
```

See `CHANGELOG.md` for what has changed, and `LICENSE.md` for the terms (AGPL-3.0
or a commercial license from the author).
