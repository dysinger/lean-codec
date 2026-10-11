# codec

A verified, bidirectional codec library: **one description, two directions.**

`codec` takes Rendel & Ostermann's *"Invertible Syntax Descriptions: Unifying
Parsing and Pretty Printing"* (Haskell Symposium 2010) and carries it further —
**more dependently typed, more provable, and binary.** The paper gives the idea:
one description, two directions, related by invertibility. `codec` is the same
idea, finished.

## The idea, in one breath

Every building block of a syntax description is a **partial isomorphism** — a
box with two doors, `apply` and `unapply`, that are each other's inverse. If you
know how to go *into* the box, you automatically know how to come back out,
because the two doors are the same fact stated twice. So one description drives
**two directions** at once:

- **decode** — bytes in, value out (the parser);
- **encode** — value in, bytes out (the pretty-printer);

and the two directions are *provably* inverse, not just documented as such.

Where the paper *states* that inverse law in prose (and notes, almost as an
aside in §7.5, that it "would be interesting to see" it encoded dependently),
`codec` makes it a **field of the type**: you cannot construct an isomorphism
without its proof, and the roundtrip — `encode d x = some s → (x, []) ∈
decode d s` — is a **closed theorem**, holding **unconditionally** for every
description. Invertibility is enforced by the type system, not by a comment.

`codec` also re-bases the idea from text (`String`/`Char`) onto **bytes**
(`UInt8`), so it covers fixed-width integers, endianness, image files, and LEB128
varints — with text rebuilt downstream, *on top of* bytes.

The proofs live in the code (`Codec/*.lean`, each declaration documented in
place) and the engineering state in `openspec/`; this document is the
**architecture statement** — the complete record of where `codec` stands
relative to the paper, and why.

______________________________________________________________________

## From the paper to a binary codec

This is the canonical, complete record of every place `codec` departs from the
paper (a *departure* — an observable-semantics change) or completes it (a
*strengthening* — no observable-semantics change). Each entry cites the paper's
§/quote and the Lean symbol that implements it, so a porter can read this one
list and know exactly what to reproduce. Anchors `[D1]`–`[D8]` and `[S1]`–`[S6]`
are stable cross-reference targets, shared with the code and the design docs.

### Departures (observable-semantics changes)

**[D1] `String`/`Char` → bytes — bytes become the base unit.**
The paper's concrete syntax is textual: `Rel :: [(α, String)]` (§4.1 the decoder
is `String → [(α, String)]`) and `token :: δ Char` (§4.3). `codec` targets
binary, so the base unit is `UInt8`, the base string is a byte sequence, and
`byte : Codec UInt8` is the `token` analogue. Text/Unicode is rebuilt downstream
(`lean-text`) on top of bytes, not in core. The proof substrate is a plain byte
list; a packed `ByteArray`-backed form is a later, *separate* transport concern,
not the thing we prove about.

**[D2] The nondeterministic list decoder.** The paper's decoder returns a *list*
of `(value, remaining)` pairs — a relation (§4.1 `Parser (String → [(α, String)])`,
§4.3 "decoding … the graph"). `codec` keeps it that way: `decode` returns all
`(value, remainder)` pairs, and `|` is list concatenation.

**[D3] `|` is the paper's *backtracking union*, not committed choice.**
`decode (d₁ | d₂) s = decode d₁ s ++ decode d₂ s`, matching `Rel (d₁ | d₂) =
Rel d₁ ∨ Rel d₂` by construction.

**[D4] Lossless capture — "allowed" bytes are *kept*, not discarded (no
`ignore`).** The paper (§3.1, §6.3) deliberately *discards* optional bytes
(`ignore`/`skipSpace` map arbitrary whitespace to a single blank and back), and
therefore abandons a strict isomorphism in favor of "modulo equivalence classes".
We reject that weakening: a run of bytes a codec allows is *captured* as a value
and re-emitted verbatim (realized by repetition over a `subset p byte` step, not a
new primitive). There is therefore **no `ignore` combinator in core**, and the
strict inverse law holds unconditionally.

**[D5] `|` needs no prefix-disjointness condition.** Some deterministic-parser
designs require `|`'s branches to be *prefix-disjoint* so at most one can match a
given input. `codec` requires none — and admits none: with `|` as backtracking
union, the branches are tried independently and concatenated, and no prefix
condition could work for repetition anyway (`[]` is a proper prefix of every
non-empty string, so `nil | cons` is never prefix-disjoint).

**[D6] `Codec` is a description *value*, not the §3.4 typeclass.** The paper
embeds syntax descriptions polymorphically (a `Syntax` typeclass, with `$`/`∗`/
`|`/`pure`/`token` as methods). `codec` instead makes `Codec` an inductive AST
(`iso`/`seq`/`alt`/`empty`/`pure`/`byte` as constructors), so a description is an
ordinary value you can hold and **structurally recurse over** — which is what
makes "proved for every description" a real, finite induction rather than a
promise.

**[D7] `iterate` (paper §5.2/§5.3) is deliberately omitted.** Its forward- and
backward-iteration fixpoints need not coincide, so no inverse law exists without
a per-element "chain-isolated in both directions" precondition. We provide
`foldl`/`foldr` directly (well-founded recursion) and omit `iterate` rather than
ship a subtly-unsound law. `foldl` is the combinator `chainl1` actually needs.

**[D8] `pure`/`element`/`subset` carry a *decidable* witness, not the paper's
`Eq α`/`(α → Bool)`.** The paper's `Eq`/`Bool` checks become `[DecidableEq α]`/
`[DecidablePred p]` — the same *job* (a check the printer performs), but
*decidable and proof-backed* rather than a free-form `Eq` or an unverifiable `Bool`.

`encode` being *partial* is **not** a departure — it is the paper's `Maybe`
printer kept as-is: `empty`/`pure x`/`subset p` reject out-of-domain values, and
we deliberately do **not** totalize it.

### Strengthenings (we complete the paper, without changing its meaning)

**[S1] `Iso.law` is a *field*, and it holds *unconditionally*.** The paper §3.1
states the inverse invariant in prose, unchecked; §7.5 muses about encoding it
dependently. `codec` does it: the law is a required field, and because `[D4]`
removes the lossy `ignore`, the strict law holds for **every** core `Iso` — the
structural ones with no precondition, and `foldl`/`foldr` with a well-foundedness
witness the caller supplies.

**[S2] Format-agnostic naming.** `Syntax`/`parse`/`print`/`token` are the paper's
text vocabulary; on bytes they mislead, so they become `Codec`/`decode`/`encode`/
`byte`. A rename only.

**[S3] Zero domain-specific leaf codecs.** Core ships only `byte` and `pure`;
every concrete format (`u8`/`varint`/`utf8`/…) lives downstream (`lean-binary`,
`lean-text`). Nothing in core can silently bake in a text- or machine-specific
assumption.

**[S4] `foldl`/`foldr` are *fresh* well-founded derivations, not `inverse ∘ foldl ∘
inverse`.** The right-fold dual is a distinct definition (the obvious
`inverse ∘ foldl ∘ inverse` is type-incoherent for the step type). Both take a
decreasing-measure witness — a *precondition*, not an unconditional law like the
structural isos.

**[S5] `relRepeat`'s least-fixpoint status is *proved*, not asserted.** The
repetition denotation is the least relation closed under the `nil`/`cons` rules;
an induction principle makes "least fixpoint" a theorem rather than a claim.

**[S6] Unbounded `many` is *semantic*, not a `Codec` value.** An infinite
description cannot be a finite AST node (a prior attempt was irreducibly opaque),
so repetition lives as three separate artifacts — a denotation, a decoder, and an
encoder — rather than a single `many` value. The paper's named repetition
combinators (`sepBy`, `chainl1`/`chainr1`) are re-derived over those three; they
do **not** exist as bare `Codec`-building symbols.

Everything else is **kept**, and kept strongly: `Rel` is preserved as the
*specification* (decoding is the paper's full relation, nothing narrowed on top),
and partial encoding is preserved.

______________________________________________________________________

## Why these choices — the reasoning in lay terms

This section explains the *reasoning*, for a reader who does not write Lean (or
who is porting `codec` to another language). No claim here goes beyond the
statement above; this is the "why", so a non-Lean reader can judge the
trade-offs rather than just copy the names.

### The one big idea first

The paper's core insight is that one *description* drives *two directions* by
making every block a **partial isomorphism** — a box with two doors that are each
other's inverse. The paper *says* the doors are inverse but never *checks* it.
`codec` turns that promise into a **field**: you cannot build the box without
supplying the proof that the doors undo each other. That one move — from
"documented in prose" to "enforced by the type" — is `[S1]`, and almost every
other choice below is a consequence of making that move *honest*.

### `[D1]` bytes instead of characters — why it matters

The paper's smallest unit is `Char`. For a tiny calculator language that is fine,
but a *binary* format — an image, a network packet, a varint — is not made of
characters; many of its bytes are not printable at all, and pretending everything
is a `Char` forces you to smuggle binary data through a text type that fights you
at every step. So `codec` moves the base unit down to a single byte and the base
string to a byte list; text becomes a downstream concern (`utf8` maps `String`
onto bytes) — on *top* of bytes, not underneath. Nothing about the framework
changes; only the ground floor does. (A `ByteArray` — raw memory — is the *fast*
representation, but it is opaque to the proof assistant, which cannot see inside
it to reduce equations. So the *proof* model is a plain list, and the *run* model
is a later, separate packed form. "The model you prove on" and "the model you run
at speed" are deliberately two things.)

### `[D2]` + `[D3]` the decoder returns a *list*, and `|` means "try both, keep
all" — why backtracking is non-negotiable

A parser answers "does this input match, and what value does it produce?". A
**committed-choice** `|` tries the left branch and, if it grabs something, stops
— quick, but it throws away the other branch's answers. A **backtracking-union**
`|` tries *both* and returns *all* the possible results. The paper's `|` is the
second kind: it is literally the *union* of two result lists (§4.3), and the
parser returns *every* way to read the input.

Backtracking is not merely the paper's choice — it is the *only* choice that is
compatible with repetition. `many p` is "zero or more `p`s", naturally
`empty | (p then many p)`: "match nothing, or match one `p` and recurse". Under
committed choice the "match nothing" branch always succeeds immediately (it
consumes zero input), so the parser always stops there and returns `[]`, never
reading even one `p`. The empty string is a prefix of *every* string, so no
reordering or "disjointness" bookkeeping can fix it. So `codec` keeps the paper's
semantics exactly, and the roundtrip laws hold **unconditionally** — because the
decoder and the denotation agree *by construction*. The cost is the paper's own
admitted cost (§4.4): naive backtracking is exponential in the worst case; making
it fast without changing what it means is a separate, later problem.

### `[D4]` lossless capture — why we refuse to throw bytes away

The paper's `ignore` maps *any* run of whitespace down to a single value and, on
printing, always emits *one* space. That is one-way loss: three spaces in, one
space out. The paper accepts this and says the inverse law holds only "modulo
equivalence classes". `codec` wants the law to be **literally true**, which a
lossy combinator makes impossible. So `codec` simply **has no `ignore`**: a run of
optional bytes is *captured* and re-emitted verbatim — same length, same bytes —
so parse and print are a genuine byte-for-byte two-way street. Where the paper
relaxes the law to keep `ignore`, `codec` relaxes nothing and drops `ignore`
instead.

### `[D5]` no prefix-disjointness gate

Some deterministic parsers require `|`'s branches to be *prefix-disjoint* — to
never both match strings where one is a prefix of the other — so "commit to the
first success" stays deterministic. `codec` needs no such gate, and could not have
one: it is incompatible with the paper's repetition, because the two branches of
`many p` are **never** prefix-disjoint (`[]` is a prefix of every non-empty
string). With `|` as backtracking union, the branches are tried independently and
concatenated, so there is nothing to keep disjoint.

### `[D6]` a description is a *value* — why the paper's typeclass hides the thing
we need to prove about

In the paper, a description lives *inside the type system*: a typeclass, with "a
parser" or "a printer" chosen by context. You never hold a description in your
hand; it is implicit. `codec` makes `Codec` an explicit **tree** (six
constructors), so a description is an ordinary value you can pattern-match on and
**structurally recurse over**. Every roundtrip proof works case-by-case over the
six constructors — and that finite induction is *the* thing that makes "proved
for every description" mean something. A typeclass gives you no finite list of
cases to exhaust.

### `[D7]` why there is no `iterate`

The paper builds `foldl` out of `iterate` — "apply this step until it fails"
(and, reversed, unapply it). The subtle problem: applying forward until it stops
and unapplying backward until it stops can land on **different** stopping points,
because "apply succeeds ↔ unapply succeeds" does not mean "apply fails ↔ unapply
fails". To ship `iterate` as an isomorphism you would have to *claim* the two
fixpoints agree — false in general — or burden every caller with a fragile
precondition. `codec` omits `iterate` and defines `foldl`/`foldr` *directly* by
well-founded recursion (each step strictly decreases a measure, which *is* the
honest guarantee). `foldl` is all `chainl1` needs, so nothing is lost and no
unsound law is shipped.

### `[D8]` decidable checks instead of `Eq`/`Bool`

The paper's `pure`/`element`/`subset` ask "is this the value I should match?" via
Haskell's `Eq` or a `Bool`. In `codec` those become *decidable, proof-backed*
witnesses: a procedure that, for every value, either proves the match or proves
its denial — never "maybe". The job is the same; the difference is that the
encoder's "compare and branch" is a provable step rather than an unverifiable
`if`.

### `[S1]` the law is a field — why this is the whole point

Covered above: the paper muses that encoding the invariant "would be interesting
to see"; `codec` does it. The concrete benefit is that *soundness is impossible
to forget* — you cannot accidentally construct a broken isomorphism, because the
constructor will not typecheck without the proof.

### `[S2]` + `[S3]` renaming, and an empty-of-leaves core

Naming (`token`→`byte`, `parse`/`print`→`decode`/`encode`) keeps the text-world
vocabulary from leaking onto bytes. The scope decision (`[S3]`) keeps core empty
of concrete formats, so nothing in it can silently assume text or one machine's
endianness; the first downstream leaf (`u8`, literally just `byte`) is the smoke
test that the framework is genuinely general.

### `[S4]` `foldl`/`foldr` are fresh, and need a termination witness

`foldr` is not `foldl` with the arrows flipped — the obvious `inverse ∘ foldl ∘
inverse` does not even typecheck, because the step's types swap order. So it is a
separate definition. Both folds take a measure plus a proof that each step
*strictly decreases* it — the honest termination guarantee, a precondition the
caller supplies, unlike the *unconditional* laws of the structural isos. A porter
knows exactly what their language's `foldl` must also require: a decreasing
measure, not just a recursive function.

### `[S5]` + `[S6]` repetition is *semantic*, and its least-fixpoint status is
proved

"Zero or more" is the one place a description would have to be *infinite*. A
strict language cannot hold an infinite description, so `codec` does not try:
`many` is **not** a node at all. Its three uses are spelled out directly — the
*meaning* (a relation that is the *least* thing closed under "empty, or one more
element"), the *decoder* (which requires each step to consume a byte so it
terminates), and the *encoder* (which recurses on the value list, so it needs no
condition). `[S5]` proves "least fixpoint" rather than asserting it; `[S6]` notes
the naming consequence — there is no `sepBy`/`sepBy1`/`some`/`many1` symbol, and
the `sepBy` triple has "one or more" (non-empty) semantics. A porter should look
for these three readings, not for a `many` object.

---

**Bottom line for a porter.** The paper gives the idea; `codec` makes it *honest*
by (1) enforcing the inverse law as a type, (2) resting on bytes, (3) keeping the
full backtracking semantics so the laws are unconditional, (4) refusing lossy
combinators so nothing is silently dropped, and (5) making the description an
ordinary value you can induct over. Reproduce those five points first; the rest
is bookkeeping you can re-derive.

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
--   empty / pure / byte                   (failure / fixed value / one byte)

-- one description, two interpreters (both over byte sequences)
--   decode : Codec α → List UInt8 → List (α × List UInt8)   -- all (value, rest) pairs
--   encode : Codec α → α → Option (List UInt8)              -- partial

-- the laws that make it a codec
--   Rel d x s ↔ (x, []) ∈ decode d s          (bidirectional)
--   encode d x = some s → (x, []) ∈ decode d s (roundtrip, unconditional)
```

Every `Codec` is a composition of `Iso`s; the inverse guarantee is **structural**:
the law is a field, and the two theorems above hold **unconditionally** for every
description — no solver, no per-combinator gate, no prefix-disjointness condition.

## Scope

- **`codec`** (this package): the pure framework — `Iso`, `Codec`, `Rel`, the two
  interpreters, and the laws. **No domain-specific leaf codecs** (not even `u8`).
- **`lean-binary`** (downstream): `u8`, `u16le`/`u16be`, … , `varint`,
  `lengthPrefix`, image/Protobuf demos, and the speed benchmark.
- **`lean-text`** (downstream): `utf8` plus `text`/`identifier`/`whitespace` —
  the paper's §6 text domain, re-based on bytes.

## Getting started

The build toolchain (Lean 4 + the `openspec` CLI) comes from the Nix flake:

```bash
nix develop      # enter the dev shell
lake build       # compile + verify
```

See `CHANGELOG.md` for what has changed, and `LICENSE.md` for the terms (AGPL-3.0
or a commercial license from the author).
