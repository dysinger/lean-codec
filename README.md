# codec

A verified, bidirectional codec library for Lean 4 (repo directory: `lean-codec`).

**Intent.** Take Rendel & Ostermann's *"Invertible Syntax Descriptions:
Unifying Parsing and Pretty Printing"* (Haskell Symposium 2010) and make it
**more dependently typed, more provable — and binary.** The paper gives the
idea: one description, two directions, related by invertibility. `codec` is
the same idea, carried further in Lean, to completion:

- **Provable, not asserted.** The paper *states* the `Iso` invariant and
  notes in passing (§7.5) that it "would be interesting to see" it encoded
  dependently. `codec` answers: the inverse law is a **field**, so an `Iso`
  without its proof cannot exist, and the roundtrip is a **closed theorem**.
  Invertibility is enforced by the type system, not documented in prose.
- **Dependently typed where the paper is loose.** The paper's `Iso` invariant
  is "modulo equivalence classes" in places — because it *loses* optional bytes.
  `codec` removes the loss (`[D4]`), so the strict inverse law holds
  **unconditionally**; the "relaxation" is not carried, it is *eliminated*, and
  the precise law is a type-checked field.
- **Binary, and more.** The paper is text-only (`String`/`Char`) and never
  considers binary. `codec`'s core is a byte sequence, so it covers fixed-width
  integers, endianness, image files, and LEB128 varints — and text/Unicode is
  rebuilt downstream as a codec composed on top of bytes.

One description, two directions. The encode→decode direction is the
**unconditional** `roundtrip` law: `encode d x = some s → (x, []) ∈ decode d s`
(`decode` returns a *list* of `(value, remainder)` pairs, so the precise statement
is membership, not a bare `=`). The decode→encode converse — `(x, []) ∈ decode d s
→ encode d x = some s` — holds byte-for-byte **only for `Functional` descriptions**
(see `Codec.Sound.encode_of_decode`), since backtracking `|` may map one value to
several byte strings. Not tested, not asserted: closed theorems for every
well-formed description.

- **Pure framework.** `codec` ships `Iso`, `Codec`, `Rel`, the two
  interpreters, and the laws — **zero domain-specific leaf codecs** (not even
  `u8`; the only descriptions are the primitives `byte` and `pure`).
- **Byte concrete syntax.** Everything concrete is a downstream package built by
  composition: `lean-binary` (binary leaves) and `lean-text` (text/Unicode).
- **Proof-carrying by construction.** There is no "verified vs unverified"
  tier; every codec is verified by its type.

See `openspec/changes/invertible-binary-core/proposal.md` for the full design, and
`openspec/changes/invertible-binary-core/tasks.md` for the task ledger.

______________________________________________________________________

## From the paper to a dependent, binary codec

The paper is the **foundation**, not a spec to transcribe. This section is the
**canonical record** of every place `codec` differs from the paper (a
*departure*, an observable-semantics change) or completes it (a
*strengthening*, no observable-semantics change). Each entry cites the paper's
§/quote and the Lean symbols that implement it, so a later porter can read this
one list and know exactly what to reproduce. Anchors `[D1]`–`[D8]` and
`[S1]`–`[S6]` are stable cross-reference targets.

### Departures (observable-semantics changes)

**[D1] `String`/`Char` → `List UInt8`/`UInt8` — bytes become the base unit.**
The paper's concrete syntax is textual: `Rel :: [(α, String)]` (§4.1 the
decoder is `String → [(α, String)]`) and `token :: δ Char` / `token = Rel [(t, [t]) |
t ← characters]` (§4.3). Our core targets binary (fixed-width integers, endianness,
image files, LEB128 framing); the base unit is `UInt8`, the base string is
`List UInt8`, and `byte : Codec UInt8` is the `token` analogue. Text/Unicode is
rebuilt downstream in `lean-text` on top of bytes, not in core. The provable core
is the `Bytes` model (an `abbrev` for `List UInt8`); `Buffer` (a `ByteArray`-backed
newtype in `Codec.Buffer`) is the later executable transport surface (§7),
*not* the proof substrate, because `ByteArray`'s FFI ops do not reduce under
`simp` (the proofs are over `List` reduction, e.g. `s = s₁ ++ s₂`).

**[D2] The nondeterministic list decoder is *kept*, not narrowed.** The paper's
decoder already returns a *list* of `(value, remaining)` pairs — a relation
(§4.1 `Parser (String → [(α, String)])`, §4.3 "decoding … the graph"). An earlier
version of `codec` narrowed this to a deterministic single-result decoder for speed
(§4.4's open problem), but that forced `|` into *committed* choice, which is
**incompatible with the paper's `|` and `many`** (an empty branch always wins;
`nil`/`cons` are never prefix-disjoint). We **restored** the paper's semantics:
`decode : Codec α → List UInt8 → List (α × List UInt8)`, `|` as list concatenation.
The laws are now *unconditional*; efficiency is future work (it does not change
the semantics). See `[D5]` and `[S1]`.

**[D3] `|` is the paper's *backtracking union*, not committed choice.**
`decode (d₁ | d₂) s = decode d₁ s ++ decode d₂ s`, matching `Rel (d₁ | d₂) = Rel d₁
∨ Rel d₂` by construction. (An earlier committed-choice deviation and its
prefix-disjointness gate were reversed — see `[D5]`.)

**[D4] Lossless capture — "allowed" bytes are *kept*, not discarded (no
`ignore`).** The paper (§3.1, §6.3) deliberately *discards* optional bytes
(`ignore`/`skipSpace` map arbitrary whitespace to `unit` and back to a single
blank), and therefore abandons a strict isomorphism in favor of "modulo
equivalence classes". We reject that weakening: a run of bytes a codec allows is
captured as a value and re-emitted verbatim, realized by repetition over a
`subset p byte` step (`relRepeat (Rel (subset p byte))` denotation,
`decodeRepeat`/`encodeRepeat` interpreters) — *not* a new primitive. There is
therefore **no `ignore` combinator in core**. The encode→decode roundtrip is
**byte-for-byte unconditional**; the decode→encode half is byte-for-byte only for
`Functional` descriptions (see the headline note above and `Codec.Sound`).

**[D5] `|` needs no prefix-disjointness condition.** This is the *absence* of the
pre-reversal departure. With `|` as backtracking union (`[D2]`/`[D3]`), no prefix
condition is required — and none *can* work for repetition (`[]` is a proper prefix
of every non-empty string, so `nil | cons` is never prefix-disjoint). The former
`NonNull`/`PrefixDisjoint`/`Disjoint` machinery is deleted.

**[D6] `Codec` is an inductive description AST, not the §3.4 typeclass.** The
paper embeds syntax descriptions polymorphically (§3.4 `Syntax`/`δ` in a typeclass,
with `$`/`∗`/`|`/`pure`/`token` as methods). `codec` instead makes `Codec : Type →
Type 1` an **inductive** AST (free-alternative / free-applicative): `iso`/`seq`/`alt`/
`empty`/`pure`/`byte` are constructors. This is what lets `Rel`/`decode`/`encode` be
ordinary functions over *one* description value (the typeclass reading would make the
description implicit and block structural induction on it). Recorded in
`Codec/Codec.lean` and `tasks.md:1.4`.

**[D7] `iterate` (paper §5.2/§5.3) is deliberately omitted.** The paper defines
`iterate :: Iso α α → Iso α α` (line 866 of the literate paper) and builds `foldl`
from it. We provide `foldl`/`foldr` directly (well-founded recursion) and omit
`iterate`: its forward- and backward-iteration fixpoints need not coincide, so no
field law exists without a per-element "chain-isolated in both directions"
precondition (see the rationale in `Codec/Iso.lean`). Shipping `iterate` would
mean shipping a subtly-unsound law; omitting it is the honest choice. `foldl` is
the combinator `chainl1` actually needs.

**[D8] `pure`/`element`/`subset` carry a *decidable* witness, not the paper's
`Eq α`/`(α → Bool)`.** The paper requires `pure :: Eq α ⇒ α → δ α` (§3.4, "needed so
that a printer can check") and `element :: Eq α ⇒ α → Iso () α` (§5.1). In Lean the
analogue is `[DecidableEq α]` (for `pure`/`element`) and `[DecidablePred p]`
(for `subset`, where the paper uses an `α → Bool` guard). Same *semantic* role (a
check the encoder/decoder performs), but decidable-valued rather than
`Bool`/classical `Eq`. Forced by `Iso.law` being `Prop`-valued; a port to a language
with a different equality story must reproduce this decidable check.

`encode` staying partial (`Option`) is **not** a departure — it is a *kept*
property: `empty`/`pure x`/`subset p` reject out-of-domain values exactly as the
paper's `Maybe` printer does (§4.2). We deliberately do **not** totalize `encode`.

### Strengthenings (not semantic changes — we complete the paper)

**[S1] `Iso.law` is a *field*, and it holds *unconditionally*.** The paper §3.1
states the inverse invariant in prose, unchecked; §7.5 notes in passing it "would
be interesting to see" it encoded dependently. We answer: `law : ∀ a b, apply a =
some b ↔ unapply b = some a` is a **field** of `Iso`, so an `Iso` without its proof
cannot be constructed. Because `[D4]` removes the lossy `ignore` primitive, the
strict law holds for **every** core `Iso` — the structural isos (`nil`/`cons`/`unit`/
`commute`/`associate`/`element`/`subset`/`optionSome`) with *no* precondition, and
`foldl`/`foldr` with a well-foundedness witness (`measure : α → Nat` +
`MeasureDecreases`) the caller supplies (see `[S4]`).

**[S2] Format-agnostic naming.** `Syntax`/`parse`/`print`/`token` are the paper's
text vocabulary (§1 "sequences of characters", §3.4 `token :: δ Char`). On bytes
they mislead, so we use `Codec`/`decode`/`encode`/`byte`. A rename only.

**[S3] Zero domain-specific leaf codecs.** A *scope* decision: the only primitive
descriptions in core are `byte` and `pure`; nothing mentions `u8`/`varint`/`utf8`.
All concrete formats live downstream (`lean-binary`, `lean-text`).

**[S4] `foldl`/`foldr` are *fresh* well-founded derivations, not `inverse ∘ foldl ∘
inverse`.** The right-fold dual is a distinct definition over `Iso (β × α) α` (the
obvious `inverse ∘ foldl ∘ inverse` is **type-incoherent** for the step type). Both
take a `measure : α → Nat` and a `MeasureDecreases`/`MeasureDecreasesR` witness — a
*precondition*, not an unconditional law like the structural isos. Recorded in
`Codec/Iso.lean`; per their computable `WellFounded.fix` over `Nat.lt`, these are
**not** `noncomputable` (the entire `chainl1`/`chainr1` family is `#eval`-able).

**[S5] `relRepeat`'s least-fixpoint status is *proved*, not asserted.** The
repetition denotation `relRepeat R` is the least relation closed under the
`nil`/`cons` rules; `relRepeat_induction` (in `Codec/Codec.lean`) is the induction
principle that makes "least fixpoint" a theorem (axioms `[propext]` only).

**[S6] Unbounded `many` is *semantic*, not a `Codec` value.** An infinite AST cannot
be a finite description in this strict language (a former `partial def many` was
proof-opaque, making `Rel (many p) ↔ relRepeat (Rel p)` unprovable). Repetition
lives as three separate artifacts — the denotation `relRepeat (Rel p)`, the
productive decoder `decodeRepeat p h` (well-founded on `s.length`), and the total
encoder `encodeRepeat p` — plus the `many`-shaped list combinators re-derived over
those three. The names `sepBy`/`sepBy1`/`some`/`many1` **do not exist as symbols**:
what the paper's `sepBy`/`sepBy1` name is realized as the `relSepBy`/`decodeSepBy`/
`encodeSepBy` triple (which has **sepBy1 semantics** — non-empty; the empty list is
not a valid value and `encodeSepBy [] = none`). Zero-or-more separation is
`optional (sepBy p sep)`. See "The `many` totality note" below.

Everything else is **kept**, and kept strongly: `Rel` is preserved as the
*specification* (decoding is the paper's full relation; no narrowing layered on
top of it), and partial encoding is preserved.

______________________________________________________________________

## Departure #5, resolved: the committed-choice detour and its reversal

The committed-choice `|` (and the prefix-disjointness machinery it required —
`NonNull`, `PrefixDisjoint`, `Disjoint`, and the prefix trichotomy) was a
consequence of attempting a deterministic single-result decoder for speed. We
discovered, over several sessions, that committed `|` is *incompatible* with the
paper's `|` and `many`:

  * `decode (nil $ pure ()) s` always succeeds consuming 0 bytes, so a
    committed `many p = nil | cons $ p * many p` always returns `[]` and never
    reaches `cons`.
  * even reordered, `nil` and `cons` are never prefix-disjoint, because `[]`
    is a proper prefix of every non-empty string — so no prefix condition can
    gate repetition, regardless of `NonNull p`.

Both facts were proved in the process (`ProperPrefix [] s ↔ s ≠ []`), showing
the *approach* was unsound, not merely unfinished. The fix was to **restore the
paper's semantics** (`[D2]`/`[D3]`): `decode : Codec α → List UInt8 →
List (α × List UInt8)` with `|` as list concatenation. Then
`Rel (d₁ | d₂) = Rel d₁ ∨ Rel d₂` and `decode` agree by construction, the laws
became unconditional, and the entire prefix-disjointness section was deleted.

Efficiency remains the paper's §4.4 open problem (exponential/space-leak under
unlimited backtracking) and is future work — a separate spike to re-implement
the *same* semantics more efficiently, not a change to the semantics. The
type-level core (`Iso`, `Rel`, `foldl`, the laws) is unaffected and reused.

______________________________________________________________________

## Why these choices? — the reasoning in lay terms

This section explains the *reasoning* behind `[D1]`–`[D8]` and `[S1]`–`[S6]`,
for a reader who does not write Lean (or who is porting `codec` to another
language). No claim here goes beyond the canonical table above; this is the
"why", written so a non-Lean reader can judge the trade-offs rather than just
copy the names.

### The one big idea first

The paper's core insight is that one *description* can drive **two directions**:
turn a value into text (`encode`, the pretty-printer) and turn text back into a
value (`decode`, the parser). It does this by making every building block a
**partial isomorphism** — a box with two doors, `apply` and `unapply`, that are
each other's inverse. If you know how to go *into* the box, you automatically
know how to come back out, because the two doors are the same fact stated
twice.

The paper *says* the doors are inverses but never *checks* it — it's a promise
written in a comment. `codec` turns that promise into a **field** (a required
slot in the box's type): you literally cannot construct an `Iso` without
supplying the proof that `apply` and `unapply` undo each other. That single
move — from "documented in prose" to "enforced by the type" — is `[S1]`, and
almost every other choice below is a consequence of making that move *honest*.

### `[D1]` bytes instead of characters — why it matters

The paper's smallest unit is `Char`; its concrete syntax is `String`. For its
text-only examples (a tiny calculator language) that is fine. But a *binary*
format — an image file, a network packet, a LEB128 varint — is not made of
characters; many of its bytes are not printable text at all, and pretending
everything is a `Char` forces you to smuggle binary data through a text type
that will fight you at every step (encoding, endianness, bytes that aren't
valid characters). So `codec` moves the *base unit* down one level, to a single
byte (`UInt8`), and the *base string* to `List UInt8`. Text then becomes a
downstream concern (`lean-text` maps `String` onto bytes via `utf8`) — on *top*
of bytes, not underneath them. Nothing about the framework changes; only the
ground floor does.

**Why `Bytes` (i.e. `List UInt8`) and not `ByteArray`?** A `ByteArray` is the *fast*
representation (raw memory), but its operations are opaque to Lean's `simp`: the
proof assistant cannot see inside them, so equations like `s = s₁ ++ s₂` (which
the entire proof lives on) would not reduce and every proof would get stuck. A
`Bytes` (= `List UInt8`) is a plain linked list that `simp` *can* unfold step by step — it
is a *proof-friendly* model. So we prove everything on `Bytes`, and later
(*not* in core) swap in a `Buffer` (a `ByteArray`-backed transport, `Codec.Buffer`) whose
`Bytes ↔ Buffer` relationship is itself proved once. This is the difference between "the model
you prove on" and "the model you run at speed" — `[D1]`'s second sentence is
deliberately that separation.

### `[D2]` + `[D3]` the decoder returns a *list* of results, and `|` means "try
both, keep all" — why backtracking is non-negotiable

A parser's job is to answer "does this input match, and what value does it
produce?". There are two ways to answer:

1. **Committed choice** (what a first attempt did): try the left branch of `|`;
   if it grabs some input, *commit* to it and never look back. This is how many
   hand-written parsers work, and it is fast.
2. **Backtracking union** (what the paper specifies, `[D2]`/`[D3]`): try *both*
   branches and return *all* the possible (value, leftover-input) pairs.

The paper's own denotational semantics is the second kind: `|` is literally the
*union* of the two result lists (§4.3), and the parser returns `[(α, String)]` —
a list, i.e. *every* way to read the input. Committed choice was a tempting
optimization, but it turns out to be **mathematically incompatible** with the
paper's `many` (repetition). Here is the concrete failure: `many p` is "zero or
more `p`s", and its natural description is `empty | (p then many p)` — "either
match nothing, or match one `p` and recurse". Under committed choice, the
"match nothing" branch *always* succeeds immediately (it consumes zero input),
so the parser always stops at the left branch and returns the empty list, never
even *trying* to read one `p`. The empty list is a prefix of *every* string, so
no amount of reordering or "disjointness" bookkeeping can fix it — you cannot
say "only use the empty branch when the other branch can't possibly start"
because the other branch can start with *anything*. (Both these facts were
proved, not just observed.)

So `codec` keeps the paper's semantics *exactly* — the decoder is a list of all
`(value, remaining)` pairs, and `|` concatenates the two lists. The payoff is
huge: because `Rel (d₁ | d₂) = Rel d₁ ∨ Rel d₂` and `decode (d₁ | d₂) =
decode d₁ ++ decode d₂` agree *by construction* (no cleverness needed), all the
roundtrip laws hold **unconditionally** — no "this only works if your grammar is
unambiguous" caveat. The cost is the paper's own admitted cost (§4.4): the
naive decoder is exponential in the worst case. We accept that cost in core and
treat "make it fast without changing what it means" as a *separate*, later, and
explicitly-deferred problem — `[D5]` notes the prefix-disjointness machinery
that committed choice needed is simply gone.

### `[D4]` lossless capture — why we refuse to throw bytes away

The paper has a combinator `ignore` (used for whitespace: `skipSpace`/`optSpace`)
that maps *any* run of spaces, of *any* length, down to a single fixed value —
and when printing, always outputs *one* space. That is a one-way loss: parse
"   " (three spaces) and print it back and you get " " (one space). The paper
accepts this and says the inverse law holds only "modulo equivalence classes" —
i.e. "these are equal up to some ignored difference".

The problem: `codec` wants the inverse law to be *literally* true (`[S1]`), as a
checked theorem, not modulo anything. A lossy combinator makes that impossible
— you cannot prove "unparse ∘ parse = identity" if parse collapses three spaces
to one. So `codec` simply **does not have `ignore`**: a run of optional bytes is
*captured* as a value (`relRepeat (Rel (subset p byte))` — "a list of every
space you actually saw") and re-emitted *verbatim*, same length, same bytes.
Parse and print are then a genuine two-way street, byte for byte.

**The benefit is honesty to the type system.** If the inverse law is a field,
it must be *true*; if it is true, nothing can be silently discarded; if nothing
is discarded, no "modulo" hedge is needed. You give up `ignore`'s convenience
(collapsing runs to a canonical form) and in exchange you get a library where
"roundtrip" is a *theorem* rather than a guideline. Where the paper relaxes the
law to keep `ignore`, `codec` relaxes nothing and drops `ignore` instead. One
caveat, stated plainly: the roundtrip is trivially guaranteed in the
**encode→decode** direction for every description; the **decode→encode**
direction ("every parse re-encodes to the same bytes") needs the description to
be *functional* — to map each value to at most one byte string — because the
backtracking `|` can legitimately give one value two spellings.

### `[D6]` `Codec` is a *value* (an AST), not a typeclass — why the paper's
encoding hides the thing we need to prove about

In the paper, syntax descriptions live *inside the type system*: `Syntax` is a
Haskell typeclass, and `δ` is a type parameter that is secretly "a parser" or
"a printer" depending on context. You never hold a description *in your hand*;
it is implicit, baked into the type. That is elegant for Haskell, but it means
you cannot write a function whose *argument* is a description and then do
structural reasoning about it — there is no single object to look at.

`codec` makes `Codec α` an explicit **inductive data type** (a tree built from
six constructors: `iso`, `seq`, `alt`, `empty`, `pure`, `byte`). A description
is now an ordinary *value* you can pass around, pattern-match on, and —
critically — **structurally recurse over** to prove things by induction. Every
roundtrip proof in `Codec.Sound` works by "if it is built from `iso`, then …;
if from `seq`, then …", case by case. That induction is *the* thing that makes
"proved for every description" mean something: with a typeclass there is no
finite list of cases to exhaust. This is the free-alternative / free-applicative
encoding the canonical table mentions, and it is the linchpin of `[S1]`
actually being provable across the whole library.

### `[D7]` why there is no `iterate`

The paper builds `foldl` out of a primitive called `iterate` — "apply this step
over and over until it fails" (and, reversed, unapply it). The subtle problem:
applying a step forward until it stops and unapplying backward until it stops
can land on *different* stopping points, because "apply succeeds ↔ unapply
succeeds" does not mean "apply fails ↔ unapply fails". The forward fixpoint and
the backward fixpoint need not agree. To ship `iterate` as an `Iso` you would
have to *claim* they do — which is false in general — or burden every caller
with a fragile "this chain is well-behaved in both directions" precondition.

`codec` takes the third option: **omit `iterate` entirely** and define `foldl`/
`foldr` *directly* by well-founded recursion (with a measure that strictly
decreases each step, which *is* the honest guarantee). `foldl` is the only thing
`chainl1` actually needs, so nothing is lost — and no subtly-unsound law is
shipped. This is the same taste as `[D4]`: when a paper's nicety would require
a false or unprovable claim, drop the nicety and keep the proof.

### `[D8]` `DecidableEq`/`DecidablePred` instead of Haskell's `Eq`/`Bool`

The paper's `pure` needs `Eq α` so the printer can ask "is this the value I'm
supposed to match?"; its `element` does the same, and `subset p` takes a `p : α →
Bool`. In Haskell those are free-form: `Eq` can be sham equality, and `Bool` is
just a boolean with no proof behind it. Lean's proofs live in `Prop`, and to
*branch on* a `Prop` (to compute "match or not") you need a `Decidable` witness
— a procedure that, for every `x`, *proves* `x = y` or *proves* `x ≠ y`, never
"maybe". So `codec` asks for `[DecidableEq α]` and `[DecidablePred p]`: the same
*job* the paper's `Eq`/`Bool` do, but with a proof attached — `DecidableEq` is
`Eq α` *plus* a decider, so it is strictly more information than the paper asks
for, not less. The benefit is that this extra witness is exactly what lets the
encoder's "compare and branch" step be a *theorem-provable* step rather than an
unverifiable `if`. A port to a language without a `Prop`-based proof system can reproduce this
with whatever its honest-equality-decider is; the point to carry over is "the
equality check must be *decidable and proof-backed*, not just a bool."

### `[S1]` the law is a field — why this is the whole point

Covered in "The one big idea" above: the paper notes (§7.5) that encoding the
inverse invariant dependently "would be interesting to see"; `codec` does it.
The concrete benefit is that *soundness is impossible to forget* — you cannot
accidentally construct a broken `Iso`, because the constructor will not typecheck
without the proof. "Proved by construction" is not marketing; it is a statement
about what the compiler accepts.

### `[S2]` + `[S3]` renaming, and keeping the core empty of leaf codecs

`[S2]` is cosmetic but load-bearing for clarity: `token` means "a character" in
a text world but means nothing on bytes, so it becomes `byte`; `parse`/`print`
become `decode`/`encode`. `[S3]` is a *scope* decision: the core ships only the
building blocks (`byte`, `pure`) and no `u8`/`varint`/`utf8` — every concrete
format lives downstream (`lean-binary`, `lean-text`). The benefit is that nothing
in core can silently bake in a text- or machine-specific assumption; the first
downstream leaf (`u8`, which is literally just `byte`) is simultaneously the
smoke test that the framework is *actually* general enough to build on.

### `[S4]` `foldl`/`foldr` are fresh, and need a termination witness

The right fold `foldr` is not just `foldl` with the arrows reversed — the obvious
"`inverse ∘ foldl ∘ inverse`" trick does not even typecheck, because the step
function's types swap order (`α × β` becomes `β × α`). So `foldr` is a separate
well-founded definition. Both folds take a `measure : α → Nat` plus a proof that
every unfold step *strictly decreases* that measure — this is the
*termination* guarantee (the recursion cannot loop forever), and it is a
**precondition the caller supplies**, unlike the *unconditional* laws of the
structural isos (`nil`/`cons`/`commute`/`associate`/…). The benefit of being
honest that the folds are conditional on a witness (rather than pretending they
are total like the rest) is that a porter knows exactly what their language's
`foldl` must also require: a decreasing measure, not just a recursive function.
(Lesson in passing: these folds were once marked `noncomputable` out of caution;
`WellFounded.fix` over a `Nat` measure is actually perfectly computable, so the
whole chain-combinator family is runnable.)

### `[S5]` + `[S6]` unbounded repetition is *semantic*, and its least-fixpoint
status is proved

Repetition ("zero or more") is the one place a description would have to be
*infinite* — an endless tree. A strict data type cannot contain an infinite
description, so `codec` does not try: `many` is **not** a `Codec` node at all.
Instead its three uses are spelled out directly: the *meaning*
(`relRepeat (Rel p)` — a recursive relation that is the **least** thing closed
under "empty, or one more element"), the *decoder* (`decodeRepeat`, which
requires the step to consume at least one byte so it is guaranteed to terminate),
and the *encoder* (`encodeRepeat`, which recurses on the *value* list so it
needs no condition at all). `[S5]` adds the induction principle
(`relRepeat_induction`) that proves "least fixpoint" rather than asserting it.
`[S6]` spells out the naming consequence: there is **no** `sepBy`/`sepBy1`/
`some`/`many1` symbol — what the paper calls `sepBy` is the
`relSepBy`/`decodeSepBy`/`encodeSepBy` triple, and it has `sepBy1` (non-empty)
semantics because an empty separated list is not a meaningful value. A porter
should not go looking for a `many` object; they should recreate these three
readings.

---

**Bottom line for a porter.** The paper gives the idea; `codec` makes it *honest*
by (1) enforcing the inverse law as a type, (2) resting on bytes, (3) keeping
the full backtracking semantics so the laws are unconditional, (4) refusing lossy
combinators so nothing is silently dropped, and (5) making the description an
ordinary value you can induct over. Everything else — naming, scoping, the
`many` split, the fold termination witnesses — follows from those five. When you
port, reproduce the *five* points first; the rest is bookkeeping you can re-derive.

## The abstraction, in brief

```lean
-- Layer 0: partial isomorphisms (the paper §3.1/§5.1), law as a field
structure Iso (α β : Type) where
  apply   : α → Option β
  unapply : β → Option α
  law     : ∀ a b, apply a = some b ↔ unapply b = some a

-- Layer 1: the description interface (the paper §3.4's `Syntax`, renamed `Codec`)
  -- $ : Iso α β → Codec α → Codec β       (IsoFunctor)
  -- * : Codec α → Codec β → Codec (α × β) (ProductFunctor / sequential)
  -- | / empty : Codec α → Codec α → Codec α / Codec α   (Alternative / choice)
  -- pure / byte : α → Codec α / Codec UInt8            (the paper's `pure`/`token`)

-- Layer 2: denotational semantics (the paper §4.3), over the provable List model
def Rel (d : Codec α) (x : α) (s : List UInt8) : Prop := ...

-- the two interpreters (format-agnostic naming):
--   decode : Codec α → List UInt8 → List (α × List UInt8)   -- all (value, rest) pairs
--   encode : Codec α → α → Option (List UInt8)              -- partial

-- the two theorems that make "one description = one relation" precise:
--   bidirectional:  Rel d x s ↔ (x, []) ∈ decode d s
--   roundtrip:      encode d x = some s → (x, []) ∈ decode d s
```

Every `Codec` is a composition of `Iso`s via `$`/`*`/`|`/`pure`/`byte`; the
inverse guarantee is **structural**: the `Iso` law is a field, and the two
`Rel` theorems above hold **unconditionally** (for every description, including
`alt`/`many`) — no solver, no per-combinator lemma, no prefix-disjointness gate.
The provable core is `Bytes` (= `List UInt8`); `Buffer` (a `ByteArray`-backed
newtype, whose FFI-backed ops do not reduce under `simp`) is the later executable
transport surface in `Codec.Buffer`, transported on top.

______________________________________________________________________

## Scope

- **`codec`** (this package): the pure framework. `Iso`, `Codec`, `Rel`,
  `decode`/`encode`, and the laws.
- **`lean-binary`** (downstream): `u8`, `u16le`/`u16be`, `u32le`/`u32be`,
  `u64le`/`u64be`, `bytes n`, `count n`, `varint`, `lengthPrefix`, image-header
  and Protobuf demos, and the speed benchmark.
- **`lean-text`** (downstream): `utf8 : Iso String (List UInt8)` plus `text`/
  `identifier`/`whitespace` — the paper's §6 text domain, re-based on bytes.

The core contains **no domain-specific leaf codecs** (its descriptions are `byte`
and `pure`); the first downstream leaf (`u8`, a one-line `byte`) is the
acceptance test that the framework is genuinely expressive.

______________________________________________________________________

## Status

The core is implemented and proven (see the task ledger
`openspec/changes/invertible-binary-core/tasks.md`): `Iso`, `Codec`, `Rel`,
`decode`/`encode` (nondeterministic/backtracking `|`), `foldl`/`foldr`, and the
**unconditional** bidirectional/roundtrip laws. `iterate` is deliberately omitted
(its forward/backward fixpoints need not coincide, so no field law — see
`Codec/Iso.lean`). Bounded repetition (`count`/`manyUpTo`) is total and
`#eval`-able. The `chainl1`/`chainr1` combinators (and their `foldl`/`foldr`
witnesses) are **computable** — the `WellFounded.fix` over a `Nat` measure needs no
`noncomputable` — so the whole derived-combinator layer is extractable. Unbounded repetition is **not** a finite `Codec` value; its
semantics lives in three already-separate places (see below): `relRepeat` (the
total least-fixpoint denotation), `decodeRepeat` (the productive decoder),
`encodeRepeat` (the total encoder). The `many`-shaped *list* combinators
(`sepBy`, `chainl1`/`chainr1`) are re-derived over these three, with their own
`_spec`/`_rel` laws. The efficient `Buffer` transport (`Codec.Buffer`) is done;
the extraction + benchmark remain future
work.

### The `many` totality note

`many` (paper §3.4) is an *infinite* description, so a strict-`List` value cannot
represent it as a finite `Codec` (a former `partial def many` was irreducibly
opaque at the `Rel` level — a `partial def` yields no equational lemma — making
`Rel (many p) ↔ relRepeat (Rel p)` unprovable). `many` therefore does **not**
exist as a `Codec`; its three readings are:

  * **denotation** — `relRepeat (Rel p)` (in `Codec.Codec`), the total
    least fixpoint;
  * **decoder** — `decodeRepeat p h` (in `Codec.Decode`), well-founded on
    `s.length`, total exactly for *productive* `p` (`productive_iff_consumesByte`,
    each step consumes ≥1 byte), only diverging for a genuinely-infinite
    empty-matching `p` like `pure ()` (`relRepeat_unbounded_of_empty`);
  * **encoder** — `encodeRepeat p` (in `Codec.Encode`), structural on the value
    list, total for every `p` (no productivity witness needed).

The list combinators built *on* `many` — realized as the `relSepBy`/`decodeSepBy`/
`encodeSepBy` triple (the paper's `sepBy`, with **`sepBy1`/non-empty** semantics)
and the `relChain*`/`decodeChain*`/`encodeChain*` triples (the paper's
`chainl1`/`chainr1`) — are likewise re-derived as relations, decoders, and
encoders (over `relRepeat`/`decodeRepeat`/`encodeRepeat`, keeping `Iso.foldl`/
`Iso.foldr` unchanged), each with an unconditional `_spec` (bidirectional) and
`_rel` (encoder-soundness) law; productivity appears only as the decoder's `hsep`
argument. There is **no bare `sepBy`/`sepBy1`/`some`/`many1` symbol**: the empty
list is not a valid `relSepBy` value (`encodeSepBy [] = none`), so the paper's
zero-or-more `sepBy` is `optional (relSepBy …)`. See `[S6]`.

```lean
-- total, #eval-able: productive (each byte consumes 1 byte)
#eval (byteRepeat [1,2,3]).map (fun (xs, r) => (xs, r))
  -- [([], [1,2,3]), ([1], [2,3]), ([1,2], [3]), ([1,2,3], [])]
```

______________________________________________________________________

## Working on the project

The build toolchain — the Lean 4 toolchain (`lean`, `lake`) plus the
spec-driven-development CLI (`openspec`) — is provided by the Nix flake's
`devShells.default` (see `flake.nix`), not installed globally. Enter it first:

```bash
nix develop          # from the repo root (or any subdirectory)
```

Inside the shell, the usual commands are available:

```bash
lake build           # compile + verify (the proof gate: zero `sorry`, zero warnings)
lake build --help
openspec status --change "<name>" --json   # OpenSpec change workflow
```

The shell also runs the flake checks (`nix flake check`), which validate Lean (the
same `lake build` with no `sorry`), the OpenSpec planning artifacts
(`openspec validate --all`), and formatting (`treefmt`).
