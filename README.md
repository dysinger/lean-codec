# codec

A verified, bidirectional codec library: **one description, two directions.**

`codec` takes Tillmann Rendel and Klaus Ostermann's _"Invertible Syntax
Descriptions: Unifying Parsing and Pretty Printing"_ (Haskell'10, September 30 2010,
Baltimore, Maryland, USA; ACM) and carries it further —
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

Where the paper _states_ that inverse law in prose — and §5 names the cost
explicitly, "it is not safe because **it is not checked that the two directions are
really inverse to each other**", with §7.5 leaving the follow-up open: "It would be
interesting to see **how the invariants of `Iso` values could be encoded in a
dependently typed language**" — `codec` makes it a **field of the type**: you cannot construct an isomorphism
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
[Performance](#performance-two-proof-layers-and-where-the-speed-goes).

**[D3] `|` is the paper's _backtracking union_, not committed choice.**
`decode (d₁ | d₂) s = decode d₁ s ++ decode d₂ s`, matching `Rel (d₁ | d₂) = Rel d₁ ∨ Rel d₂` by construction. (The paper itself treats the two directions asymmetrically — and it _says so_ in §3.3, where the `Alternative` class is introduced, not only in §4 where the instances are given: its _parser_ `|` is backtracking union (`++`, §4.1) while its _printer_ `|` is left-biased `mplus` (try left, else right; §4.2). `codec` keeps the **relation** backtracking — that is the single source of truth — and lets `encode` inherit the printer's left-bias naturally, so `Rel` and `decode` agree by construction and nothing rounds through a committed choice.)

**[D4] Lossless capture — a destructive constructor such as the paper's
`ignore` is _impossible_ under strict isomorphism.** The paper (§6.3) defines
`ignore :: α → Iso α ()` and, in its own words, notes it is "again **not a strict
partial isomorphism**": it maps _any_ run of blanks down to a single unit value
and, on printing, emits a **fixed, single** representation back — so an
arbitrary-length whitespace run is not preserved, and the inverse invariant
holds only "modulo equivalence classes" (§3.1) rather than literally. (`skipSpace`
and `optSpace` in §6.3 are the two **direct** instantiations of `ignore`; `sepSpace =
text " " ∗ skipSpace` merely _composes_ `skipSpace` behind a required blank, so it is
not a third instantiation.) The three differ in what they re-emit, and the
difference is the whole loss: **`skipSpace` prints nothing**, **`optSpace` prints
exactly one space** no matter how many (including zero) were parsed, and
**`sepSpace` requires at least one blank on input and prints one space**. Because every `codec` combinator is a **strict** partial
isomorphism — `Iso.law` is a field, `apply a = some b ↔ unapply b = some a` — we
**cannot follow the paper's destructive constructor**: a lossy `ignore` cannot
inhabit `Iso`, because its `apply` is **not injective**. `ignore x = Iso (fun _ =>
Just ()) (fun () => Just x)` sends _every_ `a` to `()`, so the field would demand
`apply a = some () ↔ unapply () = some a` — i.e. `True ↔ a = x` — for every `a` at
once, which is false for any `a ≠ x`. (The paper says the same thing in its own
words: "`ignore` is again not a strict partial isomorphism, because **all values of
`α` are mapped to ()**".) Note what is _not_ the reason: the failure is not that
"two distinct inputs map to one output, so `unapply` cannot choose" — `unapply` is
free to pick either one; it fails because the law is an `↔` quantified over
_every_ `a`, and a constant `apply` cannot satisfy it for two different `a`. So instead of relaxing the law to admit `ignore`, a run of
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

**[D5] `|` needs no prefix-disjointness condition — a _corollary of `[D3]`_, not an
independent departure.** The foil is concrete and the paper names it: Parsec "provides
a `|` combinator, but its semantics implements predictive parsing with a look ahead of
1, whereas our implementation supports unlimited backtracking" (§4.4), so "with
Parsec, `p | q` may fail, even if `q` would succeed". Designs like that require `|`'s
branches to be _prefix-disjoint_ so at most one can match. `codec` requires none, and
could not use such a condition even if offered it: because `|` is `[D3]`'s
backtracking union, the branches are tried independently and concatenated, and no
prefix condition can work for repetition anyway (`[]` is a proper prefix of every
non-empty string, so `nil | cons` is never prefix-disjoint).

**[D6] `Codec` is a description _value_, not the §3.4 typeclass.** The paper
embeds syntax descriptions polymorphically (a `Syntax` typeclass, with `$`/`∗`/
`|`/`pure`/`token` as methods). `codec` instead makes `Codec` an inductive AST
(iso`/`seq`/`alt`/`empty`/`pure`/`byte`/`satisfy` as constructors), so a description is an
ordinary value you can hold and **structurally recurse over** — which is what
makes "proved for every description" a real, finite induction rather than a
promise.

**[D7] `iterate` (paper §5.3, the backward-run step of the §5.2 foldl machine) is
deliberately omitted.** Its forward- and backward-iteration fixpoints need not
coincide: "unapply until it stops" and "apply until it stops" can land on different
states, because `apply`-succeeds-iff-`unapply`-succeeds does not give
`apply`-fails-iff-`unapply`-fails. So no inverse law exists for `iterate` without a
precondition, and `codec` omits it rather than ship a subtly-unsound one. What is
supplied instead is `Iso.foldl`/`Iso.foldr` directly, and the honest obligation they
carry is a **`measure : α → Nat` plus a proof that each step strictly decreases it**
(`MeasureDecreases`) — a termination witness, not a "chain-isolated in both
directions" condition (that phrase has no counterpart in the paper and is not
anything `codec` requires; it was invented in an earlier draft).

**And there is no `chainl1` value to need it.** The paper's `chainl1 = foldl f $ arg
∗ many (op ∗ arg)` is a description; `codec`, being strict, has no such value
(`[S6]`). What exists is the triple `relChainl1` / `decodeChainl1` / `encodeChainl1`,
and composing it needs **three** things: `Iso.foldl`, the repetition triple, and a
`ConsumesByte` witness for the decoder. Saying "`foldl` is the combinator `chainl1`
actually needs" understated it by two components.

**[D8] The _value-level_ checks carry a _decidable_ witness, not the paper's
`Eq α`/`(α → Bool)`.** Scoped precisely, because the claim is easy to overstate:
`Iso.element` and `Iso.subset` take `[DecidableEq α]` and `[DecidablePred p]`, and
`Codec.pure` takes `[DecidableEq α]` — the same _job_ (a check the printer performs),
but decidable and proof-backed rather than a free-form `Eq`.

**`Codec.satisfy` deliberately keeps a bare `(UInt8 → Bool)`.** It is not an
oversight: decorating it with `DecidablePred` would add no provable fact, because
`UInt8`'s decidable equality is already total and the predicate's meaning lives in
the caller's function either way — so the class would be ceremony, not evidence.
`satisfy` is the leaf a downstream author actually writes, so this entry must not
imply it was converted when it was not.

`encode` being _partial_ is **not** a departure — it is the paper's `Maybe`
printer kept as-is. The rejecting sites are split across the two levels: the `Codec`
constructors `empty` and `pure x` yield `none` (nothing to print / value mismatch),
and the `Iso` `subset p` yields `none` when the value is outside `p`. (They are not
all `Codec`s — `subset` is an `Iso`, composed into a `Codec` via `iso`.) We
deliberately do **not** totalize it.

### Strengthenings (we complete the paper, without changing its meaning)

**[D2] The nondeterministic list decoder — _refiled here from "Departures"_ (the
anchor id is kept for continuity; several downstream files cite it).** The paper's
decoder returns a _list_ of `(value, remaining)` pairs:

```haskell
newtype Parser α = Parser (String → [(α, String)])
```

(§4.1), and its denotation is the graph `data Rel α = Rel [(α, String)]` (§4.3).
`codec` keeps the list: `decode` returns every `(value, remainder)` pair, and `|` is
list concatenation. **This is a strengthening, not a departure**, and the earlier
placement under "Departures" was a defect: the paper's `parse` _filters_ its result
to whole-string matches —

```haskell
parse (Parser p) s = [x | (x, "") ← p s]
```

— so the paper's `parse` is not even the full relation; its `Rel` is. `codec`'s
`decode` returns the unfiltered pair list, i.e. a **superset** of what `parse`
yields and exactly the paper's `Rel`. Nothing observable changes; `codec` simply
exposes the relation rather than only its fully-consuming slice, and states the
relationship as the law `Rel d x s ↔ (x, Suffix.empty n) ∈ decode d s`.

**[S1] `Iso.law` is a _field_, and for every structural `Iso` it holds
_unconditionally_.** The paper §3.1 states the inverse invariant in prose,
unchecked, and §5 gives the motivating problem in its own words: an `Iso` written
directly with the constructor "is not safe because **it is not checked that the two
directions are really inverse to each other**". §7.5 then asks the follow-up — "It
would be interesting to see **how the invariants of `Iso` values could be encoded in
a dependently typed language**". `codec` answers both: `law` is a required field, so
a broken `Iso` does not typecheck.

**Two strengths, stated separately, because they are not the same strength.**
(i) For the **structural** isos (`unit`, `commute`, `associate`, `element`,
`subset`, `inverse`, `×`, `◦`) the law holds **unconditionally** — no hypothesis,
because `[D4]` removes the lossy `ignore` that would have needed one. (ii)
`Iso.foldl`/`foldr` also carry a `field`, but their `apply` is restricted to
**terminal seeds** (`Iso.foldl` refuses a seed that still unapplies), so they hold
_on that domain_, with a `MeasureDecreases` witness the caller supplies — which is
exactly what `[S4]` says. `[S1]` was previously written so that it appeared to
promise the folds were unconditional too; they are not, and the two anchors now agree
rather than contradicting.

**[S2] Format-agnostic naming.** `Syntax`/`parse`/`print`/`token` are the paper's
text vocabulary; on bytes they mislead, so they become `Codec`/`decode`/`encode`/
`byte`. **Only two of those four are a rename:** `Syntax → Codec` and `print →
encode` change the name and nothing else. `token → byte` changes the _carrier_
(`Char` → `UInt8`, `[D1]`), and `parse → decode` changes the _result shape_
(whole-string matches → every `(value, remainder)` pair, `[D2]`) — so those two are
not cosmetic and should not be ported as if they were.

**[S3] Zero domain-specific leaf codecs.** Core ships only the primitive leaves
`byte` and `satisfy` (plus the non-leaf `pure`, which is a value-equality
check, not a format);
every concrete format (`u8`/`utf8`/`varint`/…) lives downstream (`lean-binary`,
`lean-text`). Nothing in core can silently bake in a text- or machine-specific
assumption.

**[S4] `foldl`/`foldr` are _fresh_ well-founded derivations, not `inverse ∘
foldl ∘ inverse`.** The right-fold dual is a distinct definition, and "type-incoherent"
is checkable rather than rhetorical: the paper's `foldl` is
`Iso (α, [β]) α` built from a step `Iso (α, β) α`; the dual needs `Iso ([α], β) β`
from a step `Iso (α, β) β`, and `inverse : Iso (α, β) α → Iso α (α, β)` produces
neither the right argument order nor the right nesting — the `[β]`/`[α]` positions do
not line up, so no composition of `inverse`/`foldl` has the type. Both folds take
their own decreasing-measure witness (`measure : α → Nat` plus `MeasureDecreases`),
a _precondition_, not an unconditional law like the structural isos (`[S1]`).

**[S5] `relRepeat`'s least-fixpoint status is _proved_, not asserted.** The
repetition denotation is the least relation closed under the `nil`/`cons` rules;
an induction principle makes "least fixpoint" a theorem rather than a claim.

**[S6] Unbounded `many` is _semantic_, not a `Codec` value — and the primary
reason is `[D6]`, not laziness.** In the paper `many` is a value because it is a
polymorphic **function of the `Syntax` class** (§3.4: `many :: Syntax δ ⇒ δ α → δ
[α]`), i.e. it lives on `[D6]`'s typeclass embedding rather than in a datatype.
`codec` has no typeclass to hang it on — `Codec` is an inductive value — and there
are then **two** independent obstacles to making it a `Codec` node:

1. **A definitional cycle, for the _witness-carrying_ node.** `many` as a `Codec`
   constructor needs a `Productive` predicate over `Codec`, which needs `Rel`, which
   needs `Codec`: the order `Codec → Productive → Rel → Codec` cannot be broken, and
   the mutual-inductive escape fails the universe check.
   **Scope of that claim, stated precisely** (an earlier revision said only
   "verified", which overstated it): what is established is that a `many` node
   carrying its productivity witness as a _field_ is not definable in this ordering.
   A `many` node _without_ the witness — `Rel (many p) := relRepeat (Rel p)`, with
   `relRepeat` moved above `Rel` — would typecheck, since `relRepeat` is polymorphic
   in its relation and `Productive`/`Rel` are ordinary `def`s over an
   already-declared `Codec`. What such a node cannot have is a **total decoder**:
   `decode` would need the witness at the use site, which is exactly what the
   constructor field was for. So the cycle argument is why there is no _usable_ node,
   not why no node at all can be written.
2. **Strictness, secondarily.** Lean is strict, so a finite AST node cannot contain
   an unbounded repetition at all — the paper, being lazy, can hold one. This is
   what makes the omission _necessary_ rather than merely convenient, but it is not
   the primary reason the paper's `many` cannot be ported directly; the typeclass
   embedding (`[D6]`) is.

So repetition lives as **three separate artifacts** — a denotation (`relRepeat`), a
decoder (`decodeRepeat`), and an encoder — rather than a single `many` value.

`codec` _additionally_ derives `relSepBy`/`decodeSepBy`/`encodeSepBy` and
`relChainr1`/`decodeChainr1`/`encodeChainr1` in the same §6.1 style; the paper
defines none of these, so they are `codec`'s own faithful additions, not a
reproduction. **`sepBy` here is one-or-more** (`relSepBy` is `False` on the empty
list — it is `sepBy1`), as is `chainl1`; zero-or-more is `optional` of the
one-or-more form. None of these exist as bare `Codec`-building symbols. This is the
same semantic content for `many`/`chainl1`, but it is a _representation_ difference
(typeclass embedding vs. inductive value), not merely a cosmetic naming change.

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
[Performance](#performance-two-proof-layers-and-where-the-speed-goes).)

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
admitted cost (§4.4): naive backtracking is exponential in the worst case **and** it
"suffer[s] from … a space leak due to unlimited backtracking, which limits its
applicability to large inputs". The space half does not arise here in the same form:
`codec`'s `decode` returns a `Suffix n` carrying a length witness rather than a fresh
string, so retaining a backtracking alternative retains an index and a shared `Bytes
n`, not a copied suffix — the leak's _growth_ is in the result list, and the
exponential bound is what limits applicability either way.

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
honest guarantee). `chainl1` needs three things — `Iso.foldl`, the repetition
triple, and a `ConsumesByte` witness for the decoder — and `codec` supplies all
three, so nothing is lost and no unsound law is shipped. (An earlier revision of
this paragraph said "`foldl` is all `chainl1` needs"; `[D7]`'s own text above
corrects that, and the two now agree.)

### `[D8]` decidable checks instead of `Eq`/`Bool`

The paper's `pure`/`element`/`subset` ask "is this the value I should match?" via
Haskell's `Eq` or a `Bool`. In `codec` those become _decidable, proof-backed_
witnesses: a procedure that, for every value, either proves the match or proves
its denial — never "maybe". The job is the same; the difference is that the
encoder's "compare and branch" is a provable step rather than an unverifiable
`if`.

### `[S1]` the law is a field — why this is the whole point

Covered above: the paper states the gap plainly (an `Iso` "is not safe because it
is not checked that the two directions are really inverse to each other") and leaves
the dependent encoding open in §7.5; `codec` does it — with the caveat `[S1]`
now states, that the _structural_ isos are unconditional while `foldl`/`foldr` hold
on their terminal-seed domain with a measure witness. The concrete benefit is that _soundness is impossible
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

-- one description, two interpreters (the substrate is `Bytes n`);
-- `d` is EXPLICIT, `n` is inferred from `s`
--   decode (d : Codec α) {n : Nat} (s : Bytes n) : List (α × Suffix n) -- all (value, rest) pairs
--   encode (d : Codec α) (x : α) : Option (Sigma fun n => Bytes n)     -- partial, length + bytes

-- the laws that make it a codec (`n` is bound by `s : Bytes n`, never free)
--   Rel d x s ↔ (x, Suffix.empty n) ∈ decode d s     (bidirectional)
--   encode d x = some ⟨n, s⟩ → (x, Suffix.empty n) ∈ decode d s (roundtrip, unconditional)
```

Every `Codec` is built by structural induction over the seven constructors
(`iso`/`seq`/`alt`/`empty`/`pure`/`byte`/`satisfy`); `iso` is the single
constructor that wraps an `Iso`, so the inverse guarantee is **structural**:
the law is a field, and the two theorems above hold **unconditionally** for every
description — no solver, no per-combinator gate, no prefix-disjointness condition.

### Three generic primitives, added because a real codec could not be written without them

`[S3]` keeps core free of concrete formats — base2/4/8/10/16/32/64 live in
`lean-basen`, text in `lean-text`. **That rule is unchanged and this package ships
no format.** What it now also ships are three _format-agnostic_ primitives, because
every downstream leaf codec was otherwise blocked:

| was missing                         | what it blocked downstream                                                                   | now                                                                                                |
| ----------------------------------- | -------------------------------------------------------------------------------------------- | -------------------------------------------------------------------------------------------------- |
| a total-bijection `Iso` constructor | writing a leaf's `law` by hand, in `UInt8`/`UInt16`/`UInt32` coercion lemmas                 | `Iso.ofTotal f g hgf hfg` — law discharged from two round-trip equations                           |
| `ConsumesByte` for `seq`/`iso`      | every composed codec proved productivity by hand (`lean-basen` does exactly this, per block) | `seqConsumesByte`, `isoConsumesByte`                                                               |
| a single-value decode entry point   | a leaf author could only decode a _repetition_; `decodeOne` is committed-choice and unwired  | `decodeWholeOne` / `decodeWholeOneBytes`, with `decodeWholeOne_eq` tying them to the specification |

None of these names a format, an endianness, or a width — they are the shape every
leaf needs, which is why they belong in core and the leaves do not.

**Their in-tree status, stated precisely so it is not over-read.** All three are
proved (`[propext, Quot.sound]`-only, `#print axioms` run per lemma), and **none has
an in-tree caller**: there is no concrete codec here to call them, by design. Their
consumers are the downstream repos. `[S3]` means this package cannot demonstrate
them by example — that is the rule working as intended, not a gap to be closed here.

## Scope## Scope

- **`codec`** (this package): the pure framework — `Iso`, `Codec`, `Rel`, the two
  interpreters (the single `Bytes n` substrate), and the laws. **No
  domain-specific leaf codecs** (not even `u8`).
- **`lean-binary`** (downstream): `u8`, `u16le`/`u16be`, … , `varint`,
  `lengthPrefix`, image/Protobuf demos, and the speed benchmark.
- **`lean-text`** (downstream): `utf8` plus `text`/`identifier`/`whitespace` —
  the paper's §6 text domain, re-based on bytes.

## Performance — two proof layers, and where the speed goes

The speed story has three parts: a packed result carrier (Layer 1), a generic
bulk-byte trust seam (Layer 2), and the measured cost of the pure-Lean per-element
loop itself — which is where the remaining headroom is, and which the first two do
not touch (see "Where the speed actually goes" below).

The packed result carrier (see `Codec/Packed.lean`) gives the interpreter a
contiguous-buffer fast path, in **two layers with distinct proof status** that are
never conflated:

- **Layer 1 — proven, zero trusted C.** The packed decoder/encoder (`decodeArray` /
  `decodeFullArrayRoot` / `encodeArray` / `encodeByteArrayBytes`) and their
  refinement theorems (`decodeArray_eq`, `decodeFullArrayRoot_eq`,
  `encodeArray_eq`, `encodeByteArrayBytes_eq`), each `[propext, Quot.sound]`-only,
  zero `Classical.choice`, zero `sorry`. These are the **only** layer admitted to
  the `#print axioms` gate. (`decodeFullArray` is also proved — but proved equal
  to `head?` of `decode`, which makes it the wrong decoder to use; see below.)
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

**Do not use `decodeFullArray` for full consumption.** It commits to the head of
its candidate list (`| (_, c) :: _ => some …`) rather than searching, so on an
input where the first candidate consumes fewer bytes than needed it reports
success having consumed less than the whole buffer. Its theorem
`decodeFullArray_spec` is true — it honestly proves the function equal to the
`head?` of `decode` — so this is a _decoder_ defect, not a proof defect. The
backtracking full-consumption decoder is `decodeFullArrayRoot` (proved equal to
`decodeFull` by `decodeFullArrayRoot_eq`) — and for a whole buffer you should not
call it by hand. **`decodeWhole`** is the wired surface:

```lean
-- the fast, whole-buffer full-consumption decoder — the surface to run
decodeWhole      : Codec α → ConsumesByte d → Array UInt8 → Option (List α)
decodeWholeBytes : Codec α → ConsumesByte d → Bytes n      → Option (List α)
```

`decodeWhole` delegates straight to the packed `Array UInt8` + `Nat`-cursor search;
`decodeWholeBytes` takes the _specification_ carrier and packs it through the one
`bytesToArray` transport, so a caller holding `Bytes n` has a fast path too instead
of choosing between the slow `decodeFull` and hand-rolling the packing. Both are
tied to the specification by a law — `decodeWhole_eq : decodeWhole d h a = decodeFull
d h a.size (arrayToBytes a)` and `decodeWholeBytes_eq` — so every theorem about
`decodeFull` reads off for the wired surface with no second set of proofs. The
bench checks both the value and the law at run time, and measures the wired surface
against `decodeFullArrayRoot` in the same run: they are the same number, which is
what "wired" means.

`decodeFull` itself stays exactly what it was: **the specification**, written for its
proofs and not for speed. It is not a default anyone should reach for.

**The encode side has the same wired surface, and needed it more.** `encodeRepeat`
builds a nested `concat` closure per element, and `fastEncodeRepeat` — which was meant
to be the fast path — still calls `encode p x` per element and re-reads the resulting
`Bytes` closure byte-by-byte through `pushBytes`. So it re-stages the accumulator but
keeps the per-element intermediate, and measured it is only ~1.2× better than the slow
route (`fastEncodeRepeat` 20 MiB/s vs `encodeRepeat` 17 at 4 KiB). The wired surface
accumulates through `encodeArray`'s shape instead, with no `Bytes` intermediate:

```lean
encodeWhole      : Codec α → α → Option (Array UInt8)          -- one value, packed
encodeWholeRepeat: Codec α → List α → Option (Array UInt8)     -- a value list
encodeWholeBytes : Codec α → α → Option (Σ n, Bytes n)         -- spec carrier out
```

Each is tied to the specification (`encodeWhole_eq`, `encodeWholeRepeat_eq`,
`encodeWholeBytes_toList`), and the bench checks the law **and** the round trip —
encode with `encodeWhole`, decode with `decodeWhole`, get the input back. Measured at
`n` = 4 KiB: **32 MiB/s, against 17 for `encodeRepeat` and 20 for the old
"fast" `fastEncodeRepeat`** — a 1.9× improvement over the encoder that was already
supposed to be the fast one.

### Where the speed actually goes (measured, with its causes named)

This section replaces an earlier one that claimed a "~20–40× slower than
hand-written C" ceiling and attributed it to the compiler boxing scalar
arithmetic. **That claim had no bench lane behind it and is withdrawn.** The
numbers below come from `bench`'s own `benchDecodeShapes` lane (task 6.4), which
measures four proved-equivalent decode shapes against a same-run `memcpy` and
prints both figures.

**First, a correction of yardstick.** `memcpy` is the wrong reference for a
per-element codec, and quoting a "× off C" ratio against it is a category error:
`memcpy` moves a byte for ~0.045 ns (a bulk copy, hardware-accelerated), while a
parser does per-element _work_ — read, decide, advance, accumulate. The honest
reference for a parser is a hand-written C parser over the same bytes, and this
repo does not yet ship one. So the figures below are given **as ns/step and as a
multiple of the measured pure-Lean floor**, not as a ratio to `memcpy`.

Measured with `bench`'s `benchDecodeShapes` lane, `n` = 4 KiB, 15 samples of 3 calls
each, at load average ~2.3–2.6 on 10 cores.

### Warm versus cold: the table had been conflating two different questions

Every `benchRatio` lane interleaves a same-size `memcpy` with the measured call, so
both sides see the same cache state. That is correct for a _ratio to `memcpy`_ — and
it also **evicts the 4 KiB input between calls**, so the figure it prints is
_cold-input_ cost. That is a legitimate number. It is **not** "the achievable
pure-Lean per-element floor", which is a claim about _compute_.

The bench prints both. `benchBurst` runs 200 back-to-back calls inside one timing
window and reports **min / median / max over all 5 rounds**, not the best one, so the
warm-up decay is visible instead of being hidden behind a single endpoint. Its
working set is **one buffer**: the call index is passed to the measured function, so
the loop still varies its input (and cannot hoist) while `n` bytes — not `8n` — stay
resident. The old 8-buffer rotation is still printed as `(burst@8buf)` for the record.

Measured in one session, two consecutive `bench 4096 4096` runs, `n` = 4096, load
average ~4.4 on 10 cores. Every burst row carries its own range across the two runs,
because the decay between rounds is real and quoting one endpoint hides it:

| lane                       | run 1 (min / median / max, ns) | run 2 (min / median / max, ns) | burst@8buf, run 2 (min / median / max) |
| -------------------------- | ------------------------------ | ------------------------------ | -------------------------------------- |
| `arrayRead` (per call)     | 65 / 67 / 71                   | 64 / 65 / 73                   | 63 / 64 / 67                           |
| `idealCursor` (4096 st)    | 10508 / 10605 / 10692          | 10672 / 10883 / 11053          | 10760 / 10953 / 10989                  |
| `decodeFullArray` (512 st) | 13931 / 14011 / 14076          | 14198 / 14469 / 14960          | 14441 / 14579 / 14787                  |

Per step, the two rows a "gap to the floor" is a ratio of:

| lane                             | burst median (run 1 / run 2) | per step                  |
| -------------------------------- | ---------------------------- | ------------------------- |
| `idealCursor` (pure-Lean loop)   | 10605 / 10883 ns             | **~2.6 / ~2.7 ns/step**   |
| `decodeFullArray` (whole decode) | 14011 / 14469 ns for 512 st  | **~27.4 / ~28.3 ns/step** |

So the honest picture is **two numbers, and neither is "the" answer**: a _floor_ is a
compute claim and comes from the burst; a _throughput_ figure comes from the
interleaved lane. Which one you want depends on whether your input is hot — for a
codec run in a loop over an already-resident buffer, the burst is the relevant one.

**The headline gap is ~10.5×, and it is stated as a range.** Taking the per-step
medians above: `27.4 / 2.6 ≈ 10.5` in run 1 and `28.3 / 2.7 ≈ 10.5` in run 2 — the
two runs agree to a tenth because both numbers moved together (they are measured in
the same process under the same load). Across this session's runs under varying load
the floor moved between ~2.6 and ~3.0 ns/step with the decode row moving with it, so
the gap is **~10–11×**. An earlier revision of this section claimed "~11×" from a
floor of "**2.4 ns/step**"; that 2.4 was the _minimum of 5 decaying rounds_ at an
`8n` = 32 KiB working set, i.e. the most favourable endpoint of the wrong variant.
The measured burst **median** at an L1-resident working set is **~2.6–3.0 ns/step**,
and the gap is **~10–11×**. The correction is small; the reason for it is the point,
and it is the same defect one layer down from the one the warm/cold split fixed.

| shape                                                 | lane                           | cold ns/step | warm ns/step (burst median) | note                                       |
| ----------------------------------------------------- | ------------------------------ | ------------ | --------------------------- | ------------------------------------------ |
| `memcpy` (`copySlice`), for scale                     | `benchCalibration`             | ~0.03        | —                           | ~125 ns / 4 KiB                            |
| `Array` indexed read alone                            | `arrayRead`                    | 11–12        | ~65 ns/call                 | a single read, not a loop                  |
| **ideal `Id.run` cursor loop** (`arr[k]` + `Nat`)     | `idealCursor` (+`(burst)`)     | 15           | **~2.6–2.7**                | **the achievable pure-Lean compute floor** |
| `decodeArray` single step (`List (α × Nat)` result)   | `decodeArray step`             | 12           | —                           | the per-step `List`                        |
| `packedCands` alone (now an `attach.map`)             | `packedCands (per step)`       | 430–650      | —                           | cold-input dominated; see below            |
| `decodeFullArrayRoot` (packed `Array` + `Nat` cursor) | `decodeFullArray` (+`(burst)`) | 49           | **~27.4–28.3**              | the whole decode, one candidate searched   |
| `decodeFullFastRoot` (`Bytes`/`Suffix` cursor)        | `decodeFullFast`               | 77           | —                           | the `Suffix`/`bdrop` path                  |
| `decodeFull` (the `Bytes n` specification itself)     | `decodeFull spec`              | ~31,200      | —                           | super-linear: re-walks the suffix per step |

All cold cells are from the same two-run session and move with load; they are
order-of-magnitude, not point measurements. The two burst rows are the ones a gap may
be taken from, and only as a range.

**The `packedCands` row, and a figure that has now been withdrawn twice.** The old
entry here claimed **3 ns/call on a hot, constant array**. **That claim is deleted,
not qualified.** It came from a sink of `(…).length` — a constant `1` for a codec with
one candidate — so the optimiser dropped nearly the whole call; a function that
indexes an array cannot cost 3 ns in a tree where the bare index measures ~12. It
was never a `packedCands` number.

The replacement is the lane in `benchDecodeShapes`, which is a **burst** over 8
buffers that differ _at the cursor_ (buffers differing only at byte 0 yield the same
candidate and an invariant sink — the gate now rejects that), with the candidate
values folded into the sink:

| lane              | burst (min / median / max, ns per call) |
| ----------------- | --------------------------------------- |
| `packedCands k=1` | 85 / 86 / 87                            |
| `packedCands k=2` | 105 / 106 / 107                         |

Two calibration notes, both of which cost a wrong figure this session:

- **`lean --run` is the interpreter, not the compiled cost.** A `lean --run` probe of
  this exact call reads ~850–1050 ns/call. Quoting that against the compiled 86 is a
  10× error in the other direction. Only rows printed by the `lake build bench`
  executable may be quoted.
- The interleaved-lane figure (**430–541 ns/call**, two runs, above) is _cold_: it
  re-touches a 4 KiB array per call. It is a memory figure wearing a compute label,
  which is exactly the confusion this section exists to keep apart.

**What the numbers say, stated at the strength the evidence supports.** In a warm
loop the packed decoder is **~27–28 ns/step against a ~2.6–2.7 ns/step pure-Lean
floor** — about **10.5×** — and the whole of that gap is per-step work (a `List`
cell, the search, the accumulator), not memory bandwidth. On cold input the same
decoder is ~49 ns/step, because it is then paying to stream the buffer. Both are
honest; they answer different questions, and a document that quoted one as the other
is what this section used to do.

**One thing the table above does _not_ cover — now measured.** `Codec.byte` has
**exactly one candidate per cursor position**, so `decodeFullArraySearch` never
iterates on that workload: the ~10–11× is the degenerate `k = 1` case of a
backtracking search. The `k > 1` lane prices the difference. Its codec is
`satisfy (fun _ => true) | satisfy (fun _ => true)` — **two candidates at every
position**, each consuming one byte and each able to complete the buffer — and the
lane **asserts its premise** (`packedCands` length is 1 at `k = 1` and 2 at `k = 2`)
before timing, so a run that silently degenerates fails instead of reporting a
number.

Measured in one session, two consecutive `bench 4096 4096` runs at load ~2.9 on 10
cores, burst medians, 512 steps per burst:

| lane                         | run 1 (min / median / max) | run 2 (min / median / max) | ns/step         |
| ---------------------------- | -------------------------- | -------------------------- | --------------- |
| `idealCursor`                | 10136 / 10253 / 10446      | 10573 / 10709 / 10828      | 2.50 / 2.61     |
| `decodeFullArray` (`k = 1`)  | 14467 / 14615 / 14695      | 13965 / 14087 / 14346      | **28.5 / 27.5** |
| `decodeFullArray k=2`        | 27695 / 28105 / 28210      | 25767 / 26173 / 26546      | **54.9 / 51.1** |
| `packedCands k=1` (per call) | 74 / 75 / 77               | 73 / 75 / 76               | 75 / 75         |
| `packedCands k=2` (per call) | 94 / 94 / 95               | 92 / 95 / 96               | **94 / 95**     |

**What that says — the search is linear in `k`, and its cost is not all in
`packedCands`.**

- The second candidate costs **~25 ns/step** (52.4 − 27.4): roughly one whole extra
  decode step, so the backtracking search runs at **~1.9×** the `k = 1` decode. The
  ~10–11× headline is therefore a **lower bound** for a real backtracking codec; at
  `k = 2` the gap to the floor is **~21×**.
- `packedCands` moves **86 → 106 ns/call** for the extra candidate: **~20 ns** of the
  ~25 ns per-candidate cost. So **~5 ns/step is _not_ `packedCands`** — it is the
  `decodeArray` re-list plus the singleton `PackedCand` allocation in
  `decodeFullArraySearch`. That residue is what a rewrite would have to attack, and
  it is a measured number rather than a guess.
- `packedCands` measures **86 ns/call** at `k = 1` and **106** at `k = 2` in the
  compiled burst lane. The older "3 ns/call hot" figure is **withdrawn outright** —
  it was a folded-away sink, not a measurement (see the note above).

**Nothing was optimised as a result.** The task was to price the term _before_
rewriting it, and the numbers say the rewrite is worth ~4–7 ns/step of a ~55 ns/step
decode — real, but neither the dominant term nor a change to make on a guess.

### The hand-written C reference — the yardstick that was missing

Every figure above is relative to this repository's own pure-Lean cursor loop.
That answers "how much per-step work does the codec do above the cheapest Lean
loop", which is a real question — but not the one a reader asks, which is **how far
is this from a hand-written C parser over the same bytes**. `AGENTS.md` has said for
several revisions that a `memcpy` ratio is a category error here (it moves a byte;
a parser does per-element work) and that "the honest reference is a hand-written C
parser, which this repo does not yet measure". It now does.

`Codec/CRef.c` (+ `benchCReference`) is that reference. It is **not** Layer 2 and
**not** a trust seam: no `@[extern]` in `Codec/`, nothing proven depends on it, it is
excluded from the `#print axioms` gate by construction, and it is linked only into
the `bench` executable. It exists to be measured against, never used.

Three properties keep it honest rather than a straw man:

- **Same job.** `decodeWhole Codec.byte` decodes a whole buffer as many
  `Codec.byte`: one value per byte. The C side allocates an `n`-element value array,
  fills it from the input, and returns it. An output-free `checksum` loop would skip
  the allocation the Lean side pays for and flatter C by exactly the term under
  discussion.
- **Value-checked at run time** against `decodeWhole` on four inputs before any
  number prints, so a C reference that computes something _else_ faster fails the
  lane instead of silently changing what "the same bytes" means.
- **Same measurement machinery** as every Lean row: `benchBurst`, median of rounds,
  one L1-resident buffer, a different `n/8`-byte window decoded per call so neither
  closure can be folded away.

Measured in one session, two consecutive runs, load ~1.4 on 10 cores, burst medians,
`n/8` = 512 steps per burst:

| lane                           | run 1 (min / median / max, ns) | run 2 (min / median / max, ns) | ns/step         |
| ------------------------------ | ------------------------------ | ------------------------------ | --------------- |
| `idealCursor` (Lean loop)      | 10380 / 10532 / 10669          | 9982 / 10059 / 10643           | 2.57 / 2.46     |
| **C reference** (hand-written) | 3501 / 3598 / 3783             | 3482 / 3507 / 3575             | **7.03 / 6.85** |
| `decodeWhole` (Lean)           | 14487 / 14623 / 15477          | 13755 / 13811 / 14197          | **28.6 / 27.0** |
| **Lean ÷ C**                   | **4.1×**                       | **3.9×**                       | **~4×**         |

**What that settles, including one thing it upsets.**

1. **The gap to hand-written C is ~4×, not 10–21×.** The 10–21× figures are _against
   this repo's own floor_, and quoting them as "off C" was the category error
   `AGENTS.md` warned about, committed by omission — there was no C column, so the
   Lean-relative number was the only one available and it read as an absolute.
2. **The Lean floor is itself ~2.7× _faster_ than the C reference** (2.5 vs 6.9
   ns/step). That is not a paradox and not a win: the floor sums bytes and allocates
   nothing, while C allocates an `n`-element value array and boxes a value per byte
   to hand back the same list shape the Lean decoder returns. It is a useful
   reminder that most of the C reference's time is _materialisation_, not parsing —
   which is also where a large part of the Lean decode's time goes.
3. **"Within a small single-digit multiple of hand-written C" is now met — at ~4×.**
   An earlier revision of this section said that bar was **not** met. That statement
   was true when written (no C reference existed) and is now false, so it is replaced
   rather than kept. The bar was never a _target_ the owner set; it is a description
   of the measurement, and the measurement changed.

The Layer-2 seams remain the only C-speed regions: `byteSlice`/`blitBytes`/
`findByte` run at the `memcpy`/`memchr` floor (tens of GiB/s moving bulk bytes),
as the bench reports.

**How to reproduce / what is enforced.** `benchDecodeShapes` prints both numbers
and the ratio with the five measurement rules the engineering ledger records
(one fresh timed call per sample, a data-dependent sink so the optimiser cannot
delete the work, median rather than mean, the `memcpy` reference interleaved in
the same samples, and the load average noted next to the result). It is a
**reporting** lane, not a failing one: the owner has set no threshold, and a bar
invented by the tooling would be the same defect as the figure it replaced.

## Getting started

The build toolchain (Lean 4 + the `openspec` CLI) comes from the Nix flake:

```bash
nix develop      # enter the dev shell
lake build       # compile + verify
```

See `CHANGELOG.md` for what has changed, and `LICENSE.md` for the terms (AGPL-3.0
or a commercial license from the author).
