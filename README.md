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
without its proof, and the roundtrip — `encode d x = some ⟨n, s⟩ → (x, Suffix.empty n) ∈ decode d s` — is a **closed theorem**, holding **unconditionally** for every
description. Invertibility is enforced by the type system, not by a comment.

**That second line used to read `(x, []) ∈ decode d s`** (`codec-audit-round-six`
R7-31). `[]` is not the library's empty remainder — the type is `List (α × Suffix n)`
and the empty remainder is `Suffix.empty n` — so the shorthand was rendered in
backticks as if it were the library's own statement. `bidir` (line for line,
`Rel d x s ↔ (x, Suffix.empty n) ∈ decode d s`) is the exact form, and this section
now uses it in the same spelling as `[D2]`'s two other citations rather than a fourth
one that existed nowhere.

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
The paper's concrete syntax is textual. The decoder is
`newtype Parser α = Parser (String → [(α, String)])` (§4.1) and the primitive token
is `token` over `Char`; the value graph is `data Rel α = Rel [(α, String)]` (§4.3) —
quoted in full, because an earlier revision rendered the two declarations as the
fragments `Parser (String → [(α, String)])` and `Rel :: [(α, String)]`, neither of
which is what the paper says (the first drops the `newtype` head and the `α` binder,
the second writes `Rel` as if it were a constructor rather than a `data` type).
`[D2]` below quotes them correctly; the two anchors now agree. `codec` targets binary, so the base
unit is `UInt8`, the base string is a byte sequence, and `byte : Codec UInt8` is
the `token` analogue. Text/Unicode is rebuilt downstream (`lean-text`) on top of
bytes, not in core. **One byte-string type, one job** (see
[Representations](#representations--one-length-indexed-byte-string-the-spec-substrate)): the _spec_
substrate is the single length-indexed `Bytes n := Fin n → UInt8`, which is
structurally reducible for proofs **and** expected (as an IR matter, not a theorem) to
lower to a scalar indexed load — there
is no separate `List` spec and no `ByteArray` run-model slab _for the specification
carrier_ (`decode`/`encode`/`Rel` and the laws). The packed (`Array UInt8`) and
byte-slice (`ByteArray`) carriers in `Codec/Packed.lean`/`Codec/ByteSlice.lean` are
proved-equal or trust-seam _implementations on top of_ that single spec — see
[Performance](#performance--two-proof-layers-and-where-the-speed-goes).

**[D2] The nondeterministic list decoder — filed under Departures, where it belongs.**
The anchor id `[D2]` is kept for continuity (downstream files cite it), but the
classification is _departure_, not strengthening. This anchor has now been mis-filed
**twice**, in opposite directions, and the reason is worth recording because it is
the check a reader should apply:

- "Departures" was wrong because a `Departures` heading means an observable
  semantics change, and `[D2]` was described as merely exposing the paper's `Rel`;
- "Strengthenings" is wrong for the **same** reason in the other direction. This
  section's own definition (above) is that a strengthening is "a _strengthening_ —
  no observable-semantics change". `codec`'s `decode` returns the unfiltered pair
  list, the paper's `parse` returns only whole-string matches: those are different
  observable results from the same input, so the change is observable and it is a
  **departure**. Calling it a strengthening because the new result is a superset
  confuses "more informative" with "no observable change"; a superset _is_ a
  different observation.

**And the premise needed correcting too.** The paper has **two decoder-side
values**, not one: `parse :: Parser α → String → [α]` (the `[α]`-interpreter,
filtered at `""`) and `data Rel α = Rel [(α, String)]` (the graph). So `codec` did
not _extend_ a `Rel`; it **replaced an `[α]`-interpreter with the graph**. ("Two"
counts the _decoder_ side only — the paper's third interpreter is `print`, which is
`[S2]`'s subject; an earlier revision said "two values, not one" without the scope,
which reads as a count of the whole paper.) The link to `parse` is a theorem
— `decode_spec` specialised at `r = Suffix.empty n` gives `Rel d x s ↔ (x, Suffix.empty n) ∈
decode d s` (`bidir`), with the `n - n = 0` transport discharged by `Rel_cast` — not a
definitional identity. (An earlier revision said "filtered at", which describes an
operation `bidir` does not perform: it specialises the remainder and then transports a
cast, and nothing in the proof filters a list — `codec-audit-round-nine` review N-5.)

The paper's decoder returns a _list_ of `(value, remaining)` pairs:

```haskell
newtype Parser α = Parser (String → [(α, String)])
```

(§4.1), and its denotation is the graph `data Rel α = Rel [(α, String)]` (§4.3).
`codec` keeps the list: `decode` returns every `(value, remainder)` pair, and `|` is
list concatenation. **An earlier revision filed this as a _strengthening_ and that
was wrong** — for the reason this anchor's opening gives: a superset is a different
observation, so it is a **departure**, and the "departure" heading it sits under is
correct. (The mis-filing happened in both directions before this was settled; do not
re-open it.) The paper's `parse` _filters_ its result to whole-string matches —

```haskell
parse (Parser p) s = [x | (x, "") ← p s]
```

— so the paper's `parse` is not even the full relation; its `Rel` is. `codec`'s
`decode` returns the unfiltered pair list — a **superset, as a set of pairs**, of
what `parse` yields, and it is the paper's `Rel` **denotation** (`bidir` is the `↔`,
not an equality) — that is, as a set of
`(value, string)` pairs, not as a multiset of derivations, so two parses reaching the
same pair are one element of the relation (see the Multiplicity note under `[D3]`).
The **relation** is unchanged; the
**observation** is not — `[α]` and `[(α, String)]` are different results for the same
input — which is why this is a departure and not a strengthening. It states the
relationship to `parse` as a theorem rather than a definitional identity:
`Rel d x s ↔ (x, Suffix.empty n) ∈ decode d s`.

**[D3] `|` is the paper's _backtracking union_, not committed choice.**
`decode (d₁ | d₂) s = decode d₁ s ++ decode d₂ s`, matching `Rel (d₁ | d₂) = Rel d₁ ∨ Rel d₂` by construction. (The paper itself treats the two directions asymmetrically — and it _says so_ in §3.3, where the `Alternative` class is introduced, not only in §4 where the instances are given: its _parser_ `|` is backtracking union (`++`, §4.1) while its _printer_ `|` is left-biased `mplus` (try left, else right; §4.2). `codec` keeps the **relation** backtracking — that is the single source of truth — and lets `encode` inherit the printer's left-bias naturally, so `Rel` and `decode` agree by construction and nothing rounds through a committed choice.)

**Scope of that claim: `Rel`, `decode`, `encode` — not everything in the crate.**
Core _also_ ships a committed-choice decoder, `Codec.decodeOne`
(`Codec/DecodeOne.lean`), whose `alt` is `orElse` (first non-`none` branch) and
whose `seq` commits to the **first** `d₁` result. It is sound (`decodeOne_mem`:
every result is a genuine `decodeArray` result) but **not complete** — it can
return `none` where `decodeArray` has results — and its completeness is recorded as
**open**, not claimed. So "`|` is backtracking union" is a statement about the
relation and the list decoder; a second, explicitly gated surface exists and a
porter who wants only the paper's semantics should ignore it.

**Multiplicity: "agree by construction" means the same _graph_, not the same _data_.**
`decode (d | d) s = decode d s ++ decode d s`, a **list concatenation**, so
`decode (d | d) s` returns every result **twice**, while `Rel (d | d) = Rel d ∨
Rel d` is the idempotent `∨` and carries each pair once. A porter who models `|` as
set union will match on `Rel` and diverge from `decode` on multiplicity — and, if
they dedupe, break `encode`'s left-bias correspondence. The two "agree" at the level
of which values relate to which strings; they do not agree as multisets.

**[D4] Length-preserving capture — a destructive constructor such as the paper's
`ignore` is _impossible_ under strict isomorphism, and the length-changing job it
existed for is not reproduced.**

**Read the second half of that title first, because it is the operative limit.** Both
mechanisms core ships for capture are **length-preserving when instantiated at `Bytes n`**
— and core ships the _layer_, not an instance: `Normal`'s normalizer is **parametric**,
`norm : S → S` (`Codec/Normal.lean:126`), so an instantiation at `Bytes n` cannot change
the byte count, and `relTakeWhile` relates a run of length `n` to a value of _all_ `n`
bytes.

(Two corrections live in this parenthesis, and the second was introduced by the first. An
earlier revision said "the `Normal` layer's normalizer is `norm : Bytes n → Bytes n`",
naming a concrete function that exists nowhere — `codec-audit-round-nine` review P1-PA3). The
fix then claimed "there is no `Normalizer` value constructed anywhere", citing
`grep -rn Normalizer Codec/`. **That grep's path excluded the file that falsifies it**:
`Bench.lean:61` is `theorem foldNz : Normalizer UInt8 foldNorm := ⟨foldNorm_idem⟩` — a
constructed `Normalizer`, idempotence proved, on the bench's two-symbol alphabet (review
F-1). Precisely: core ships the **layer** and no `Bytes n` instantiation of it
(`grep -rn Normalizer Codec/` indeed finds only the structure and the binders of
`fill`/`decodeNormal`), while the bench **does** construct one at `UInt8` to value-check
the layer. The parametric form is the stronger claim either way — it rules out shrinking
at _every_ instantiation rather than one — and the lesson is this session's recurring one:
**a claim scoped by a path is only as good as the path, and `Codec/` is not the repo.**)

**`takeWhile`'s denotation, because its type is the fact a porter needs and the name
hides it** (`codec-audit-round-nine` §7.3): the captured value is a **`List UInt8`** —
`relTakeWhile (p : UInt8 → Bool) : List UInt8 → (n : Nat) → Bytes n → Prop`, `n`
**explicit** — not the paper's `[()]`, a list of units. The paper's `ignore`-shaped
capture throws the bytes away, which is what makes it lossy; here every captured byte is
retained. That type difference _is_ `[D4]`'s whole content, and a porter reproducing
"`takeWhile`" by copying the paper's `[()]` will get a lossy capture and then wonder why
the law does not close. **What is _not_ claimed**: there is no theorem asserting that the
run-to-`List UInt8` relation is a bijection and no `Iso` built from `takeWhile`
(`grep -n 'Iso.*takeWhile' Codec/Combinators.lean` finds none) — an earlier revision said
"is a bijection on the run and can be the inside of an `Iso`", which is true in substance
but was stated as though proved (review P4-N4).

The paper's `ignore` exists for a _length-changing_
job — collapse an **arbitrary-length** blank run to a fixed representation, i.e. a
`Bytes m → Bytes n` map with `m ≠ n` — and **core does not reproduce it**. A carrier
for that is a `Bytes m → Bytes n` `Iso` (or a `List`-shaped normalizer) with its own
`Productive`/`ConsumesByte`/shrink-witness obligations, and it is **not built here**;
see the length-preserving caveat below, which is the same fact stated at the point of
use rather than as a parenthesis 40 lines later.

The paper (§6.3) defines
`ignore :: α → Iso α ()` and, in its own words, notes it is "again **not a strict
partial isomorphism**": it maps _any_ run of blanks down to a single unit value
and, on printing, emits a **fixed, single** representation back — so an
arbitrary-length whitespace run is not preserved. §3.1 lets this pass by reading the
invariant "modulo equivalence classes" — quoted, and marked as the paper's own
concession rather than a law this project could state and check.

**Read the quotation precisely: that sentence is about `ignore` alone.** The paper
turns it into a _family_ by instantiating it three ways — `skipSpace`, `optSpace`,
`sepSpace` — and the "not a strict partial isomorphism" verdict is inherited from
`ignore`, not separately argued for each. In particular `skipSpace` re-emits the
**empty** list (it _parses_ any run of blanks, _prints_ nothing), which is exactly
the lossy direction; `optSpace` prints exactly one space; `sepSpace` requires one
input blank and prints one. Citing the paper's sentence as if it covered
`skipSpace`/`optSpace` as independently-argued cases overstates it, and an earlier
revision of this anchor did exactly that. (`skipSpace`
and `optSpace` in §6.3 are the two **direct** instantiations of `ignore`; `sepSpace =
text " " ∗ skipSpace` merely _composes_ `skipSpace` behind a required blank, so it is
not a third instantiation.) The three differ in what they re-emit, and the
difference is the whole loss: **`skipSpace` prints nothing**, **`optSpace` prints
exactly one space** no matter how many (including zero) were parsed, and
**`sepSpace` requires at least one blank on input and prints one space**. Because every `codec` combinator is a **strict** partial
isomorphism — `Iso.law` is a field, `apply a = some b ↔ unapply b = some a` — we
**cannot follow the paper's destructive constructor**: a lossy `ignore` cannot
inhabit `Iso`, because its `apply` is **constant** — it sends _every_ `a` to `()`,
and the law is an `↔` quantified over **every** `a`. Concretely, `ignore x = Iso (fun
_ => Just ()) (fun () => Just x)` would demand
`apply a = some () ↔ unapply () = some a`, i.e. `True ↔ a = x`, for every `a` at
once — false for any `a ≠ x`. (The paper says the same thing in its own
words: "`ignore` is again not a strict partial isomorphism, because **all values of
`α` are mapped to ()**".) **The obstruction is constancy, not non-injectivity, and an
earlier revision said the opposite in consecutive sentences** (`codec-audit-round-five`
R6-17): its anchor sentence read "because its `apply` is **not injective**", and three
sentences later the same paragraph correctly said "Note what is _not_ the reason: the
failure is not that two distinct inputs map to one output, so `unapply` cannot
choose". The first sentence was the error. Non-injectivity is a _consequence_ of
constancy and is not by itself fatal: a partial iso whose `apply` merged two inputs
could still satisfy the field if `unapply` picked the one the law demands, so what
breaks is the `↔` over all `a`, not the merging. So instead of relaxing the law to admit `ignore`, a run of
allowed bytes is _captured_ as a value and re-emitted verbatim — realized by
repetition over a **`Codec.satisfy p`** step, not a new primitive. The step is the
`Codec` **constructor** (`Codec/Codec.lean`): `satisfy : (UInt8 → Bool) → Codec UInt8`.
What `Codec/Combinators.lean` holds is its _use_, as the element of
`relTakeWhile`/`decodeTakeWhile`/`encodeTakeWhile` (`codec-audit-round-eight` S-1 — an
earlier revision's parenthetical sent a reader to `Codec/Combinators.lean` for a
declaration that is not there). (An earlier revision wrote "a `subset p byte` step"; no
code composes `subset` with `byte` — the step is `satisfy p`.) There is therefore
**no `ignore` combinator in core**, and the strict inverse law holds
unconditionally.

**The diagnosis, sharpened (normal forms).** `ignore` cannot inhabit `Iso α S`
_because it is not an `Iso`_ — it is the lossy _half_ of a codec whose honest
object is a bijection with the **quotient of the concrete syntax by the
information-free variation**. This is `Codec/Normal.lean`'s own account of the
record: its module header says the earlier `[D4]` "conclusion is right, but its
diagnosis was incomplete" — capture-verbatim is one _instantiation_ of the quotient
layer (the identity normalizer), not the explanation of why `ignore` fails. The
quotient-as-object formulation is the explanation; capture-verbatim is the
degenerate case that happens to need no `norm`.

**Capture-verbatim is length-preserving _for a `Bytes n` instance_, and that bounds what
it can do there.** The layer itself is generic — `Normal (S : Type) (norm : S → S)`, so
`norm : S → S` for any `S` — and it is the `Bytes n` specialisation (`norm : Bytes n →
Bytes n`) that cannot shorten its input. A `List`-carrier instance is **not**
length-preserving, and is in fact the carrier a length-changing normalizer would use
(`codec-audit-round-eight` S-4: the earlier wording stated the general premise at
`Bytes n`, which reads as the layer _forbidding_ a `List` normalizer when it
instantiates one directly). For a `Bytes n` instance, then: Case folding
(half the point of `[D4]` for a Base16 decoder) fits; **collapsing a whitespace run
does not** — that is `Bytes m → Bytes n` with `m ≠ n` and needs a different carrier.
So the one thing the paper's `ignore` existed _for_ — discarding an arbitrary-length
blank run — is the one thing this layer cannot reproduce, and the layer says so at
the point of use rather than in a later parenthesis. A codec using it also owes the
per-instance fact that its encoder emits a normal form, without which the
normalising decoder can fail on its own encoder's output. A format often accepts
several spellings of one value — hexadecimal case is the example above, where the two
spellings differ only in information that carries no value — so the quotient is `S/~`
where `s ~ t ↔ norm s = norm t` for a total idempotent `norm`.

**An earlier revision cited this as "(RFC 4648 §8: a Base16 decoder MUST accept both
`6F` and `6f`)" and that was wrong on the standard's own text** (`codec-audit-round-eight`
M-1). §8 says the opposite: _"Base 16 encoding does not require case insensitivity;
however, Base 16 decoders MAY accept lowercase letters."_ Accepting both cases is a
**permission**, not an obligation, so a decoder that rejects `6f` is conformant. The
citation also mattered in the direction it was wrong: it invites a reader to generalise
"case is free" to other formats, and for Base64 it is false — its alphabet uses all 64
symbols, so `a`–`z` are 26 distinct values and uppercasing would turn valid input into a
different value. The quotient argument does not need the RFC at all; it needs only that
some spelling variation carries no information, which this paragraph now says. `codec` puts that quotient in the **object** rather
than relaxing the law in the **morphism**, which is the one thing `[S1]` forbids:
`Codec/Normal.lean` supplies `Normal S norm` (the fixed points of `norm`, a type)
and `Normalizer S norm` (carrying `norm`'s idempotence), so
`Iso α (Normal S norm)` is an **ordinary `Iso`** with its `law` still a field. The
lossy direction is `decodeNormal`, the normalizer composed _outside_ the `Iso`: it
accepts input the `Iso` rejects, has no inverse, and is explicitly not a codec
value. Capture-verbatim is then simply the **identity normalizer** — the degenerate
case of the layer, not a prohibition on having one. Two consequences worth stating:
the layer is **length-preserving** (`norm : S → S`, so a `Bytes n` instantiation cannot
change the byte count — case folding fits and collapsing a whitespace run does not, since
that needs a different carrier; the earlier form of this sentence wrote
`norm : Bytes n → Bytes n`, a concrete function the tree does not contain — review P1-PA3
saw the same defect in `[D4]` and this was its surviving second site), and a
codec using it owes the per-instance fact that its encoder emits a normal form,
without which the normalising decoder can fail on its own encoder's output.

**[D5] `|` needs no prefix-disjointness condition — a _corollary of `[D3]`_, not an
independent departure.** The foil is concrete and the paper names it: Parsec "provides
a `|` combinator, but its semantics implements predictive parsing with a look ahead of
1, whereas our implementation supports unlimited backtracking" (§4.4) … "with
Parsec, `p | q` may fail, even if `q` would succeed". _(The `…` marks an elision, and
the material strictly between the two fragments is **three words** — "This means
that", §4.4 — after which the paper's own sentence continues directly into the second
quoted fragment. An earlier revision rendered the note as a quote-with-its-own-ellipsis
("This means that … whereas the syntax description …"), i.e. it spliced the elision
marker itself across the text it was describing; the span is quoted exactly here and no
more (`codec-audit-round-five` R6-16). The point of the note is the marker, not the
three words: without it the two fragments read as adjacent text, which they are not.)_
Designs like that require `|`'s
branches to be _prefix-disjoint_ so at most one can match. `codec` requires none —
and the checkable reason is that **`Codec.alt` carries no premise at all**: `[D3]`'s
backtracking union tries the branches independently and concatenates their results,
so there is no hypothesis a prefix condition could add to. A prefix condition could
therefore only _narrow_ a law that already holds for free. (It would also be
unavailable in general: `[]` is a proper prefix of every non-empty string, so
`nil | cons` is never prefix-disjoint.) An earlier revision justified this with an
unfalsifiable "could not use such a condition even if offered it", which cannot be
checked against anything; the premise-free statement can.

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
`apply`-fails-iff-`unapply`-fails. So `iterate` cannot satisfy `Iso.law`
**unconditionally** — it does not follow from the step iso's law, and no proof of it
exists here — and `codec` omits it rather than ship a subtly-unsound one. (An earlier
revision said "no inverse law exists", which is stronger than what is proved: what is
proved and recorded is that the two fixpoints need not agree, so the law is not
available _without_ a precondition. `codec-audit-round-six` R7-20.) What is
supplied instead is `Iso.foldl`/`Iso.foldr` directly, and the honest obligation they
carry is a **`measure : α → Nat` plus a proof that each step strictly decreases it**
— a termination witness. **Stated at the right type, because an earlier revision
collapsed two different things** (`codec-audit-round-five` R6-24):
`MeasureDecreases` is not "a measure with a proof field"; it is a structure
**parameterised by the measure and the iso**, `MeasureDecreases (measure : α → Nat)
(i : Iso (α × β) α)`, whose **only field is the proof** `dec : ∀ a a' b, i.unapply a
= some (a', b) → measure a' < measure a`. So the measure is an _argument_ to the
witness type, not a field of it — which is what makes one structure serve every fold.
(That same anchor's later list gets this right: "a `measure : α → Nat` plus a proof"
is two arguments, `MeasureDecreases measure f`, not one bundled value.) It is a
termination witness, not a "chain-isolated in both
directions" condition (that phrase has no counterpart in the paper and is not
anything `codec` requires; it was invented in an earlier draft).

**And there is no `chainl1` value to need it.** The paper's `chainl1 = foldl f $ arg
∗ many (op ∗ arg)` is a description; `codec`, being strict, has no such value
(`[S6]`). What exists is the triple `relChainl1` / `decodeChainl1` / `encodeChainl1`,
and composing it needs **five** things: `Iso.foldl`, **a `MeasureDecreases` witness
for that fold** (a separate argument — `Iso.foldl` does not carry it), **a
_terminal_ seed**, the repetition triple, and a `ConsumesByte` witness for the
decoder. Saying "`foldl` is the combinator `chainl1` actually needs" understated it
by three components, and an earlier revision that said "three" still missed
`MeasureDecreases`; a revision that said "four" missed the seed.

**The terminal-seed obligation is not decoration.** `Iso.foldl`'s `apply` returns
`none` on a seed that still unapplies (`Codec/Iso.lean`): the fold is defined over
the states `unapply` reaches, so a seed with a live step has no image and the
composition silently has no result. `[S4]` already states this restriction; `[D7]`
omitted it, so the two anchors disagreed on what the fold obliges a caller to supply.
They now agree.

**[D8] The _value-level_ checks carry a _decidable_ witness, not the paper's
`Eq α`/`(α → Bool)`.** Scoped precisely, because the claim is easy to overstate:
`Iso.element` and `Iso.subset` take `[DecidableEq α]` and `[DecidablePred p]`, and
`Codec.pure` takes `[DecidableEq α]` — the same _job_ (a check the printer performs),
but decidable and proof-backed rather than a free-form `Eq`.

**`Codec.satisfy` deliberately keeps a bare `(UInt8 → Bool)`, and it is not a
paper combinator at all.** Two things an earlier revision got wrong here:

- **Scope.** `satisfy` has no counterpart in the paper: the paper's byte-level leaf
  is `token`, which `[S2]` renames to `byte`, and `satisfy p` is an _extra_ `Codec`
  constructor (`Codec/Codec.lean`) — the byte-token-with-guard. It sits under this
  anchor only because the departure it most resembles is the `Decidable`-vs-`Bool`
  choice; do not read it as a ported primitive.
- **Why the others _were_ converted and this one was not.** The earlier reason ("a
  `DecidablePred` would add no provable fact, because `UInt8`'s decidable equality is
  already total") explains nothing about **the decision to convert `subset`**. The
  actual reason is scope of the obligation: `Iso.element`/`subset`/`Codec.pure`
  _decide_ their check (produce a `Bool`-valued **result**), so a `Decidable` instance
  is the obligation a caller must discharge and the library can profitably demand it.
  `satisfy p` never decides anything — it _filters_ with a predicate the caller
  already wrote, and its consumers (`takeWhile` and the run values built on it) only
  ever need that `Bool`. Wrapping it in `DecidablePred p` would therefore add a
  hypothesis to every consumer without changing a single result, i.e. ceremony. So
  `subset` was converted because it decides; `satisfy` was not because it filters.
  This entry must not imply it was converted when it was not.

`encode` being _partial_ is **not** a departure — it is the paper's `Maybe`
printer kept as-is. The rejecting sites are split across the two levels: the `Codec`
constructors `empty` and `pure x` yield `none` (nothing to print / value mismatch),
and the `Iso` `subset p` yields `none` when the value is outside `p`. (They are not
all `Codec`s — `subset` is an `Iso`, composed into a `Codec` via `iso`.) We
deliberately do **not** totalize it.

### Strengthenings (we complete the paper, without changing its meaning)

**[S1] `Iso.law` is a _field_, and for every structural `Iso` it holds
_unconditionally_.** The paper §3.1 states the inverse invariant in prose,
unchecked, and §5 gives the motivating problem in its own words: an `Iso` written
directly with the constructor "is not safe because **it is not checked that the two
directions are really inverse to each other**". §7.5 then asks the follow-up — "It
would be interesting to see **how the invariants of `Iso` values could be encoded in
a dependently typed language**". `codec` answers both: `law` is a required field, so
a broken `Iso` does not typecheck.

**Composition is `≫`, not the paper's `◦` — and the two read in opposite order.**
`Codec/Iso.lean` defines `infixr:80 " ≫ " => Iso.trans` as _Kleisli_ composition:
`f ≫ g` applies `f` first, then `g`. The paper's `◦` is ordinary function
composition, `g ◦ f` = apply `f` then `g`. So a porter reading `f ≫ g` as `f`
after `g` will invert every composed iso — and the error is silent, because both
have the right type in the common case. This is a renaming the anchor must state,
not an implementation detail.

**The full unconditional-iso list**, because an earlier revision named a subset:
`id`, `ofTotal`, `trans` (`≫`), `inverse`, `prod` (`×`), `associate`, `commute`,
`unit`, `element`, `subset`, `nil`, `cons`, `optionSome`. `ofTotal` is the one that
matters most for a porter: it turns two round-trip equations into the `law`, so a
total bijection needs no hand-written inverse proof.

**"Unconditional" describes the _law_, not the footprint, and the list is not
footprint-uniform** (`codec-audit-round-eight` S-5): `Iso.inverse` measures
**axiom-free**, while the other twelve are `[propext]`-only. That is the kind of
difference the trust-contract section states is "recorded at each law, not treated as
drift", so quoting one footprint for the whole list would be the drift. Per-name
measurement, from `#print axioms` — grep `recorded at each law` for the sentence.

`Iso.foldl` and `Iso.foldr` are **deliberately excluded** from that list, and the
list is called "full" only of the _unconditional_ structural isos. **How the count
is obtained matters, and an earlier revision got both the number and the method
wrong** (`codec-audit-round-five` R6-04): it said "grepping `^def` in
`Codec/Iso.lean` finds exactly two other `Iso`-valued definitions", which is wrong
twice over — `grep '^def'` misses a multi-line signature, and the tree has **four**
more, not two. A walk of the compiled environment (the same method `Axioms.lean`'s
definition-coverage check uses) finds **19** public `Iso`-valued definitions:
`id`, `ofTotal`, `trans`, `inverse`, `prod`, `associate`, `commute`, `unit`,
`element`, `subset`, `nil`, `cons`, `optionSome` (the 13 structural unconditional
isos above), plus `foldl`, `foldr`, `counterIso`, `counterIsoR`, plus the two
counterexample witnesses `uniqSeqIso` and `uniqSeqUnitIso` — **13 + 4 + 2 = 19**.

**The total was right and the decomposition was wrong** (`codec-audit-round-six`
R7-03). This sentence used to give `13 + 4`, which sums to 17, because it named the
fold pair and the two counter isos but not the two witness isos in `Codec/Sound.lean`.
A total that is correct while its parts do not add up is the shape that survives a
correction: the number looks right and only the sum is wrong. The 19 is re-derived
for this fix by an environment walk, and that walk returns the two witnesses **by
name** — so this is the list the method produces, not a repaired sum.

Those six are not all in the same position, which is why "exactly two others" was
misleading rather than merely off by two:

- `Iso.foldl`/`Iso.foldr` hold their law only on the **terminal-seed domain** —
  strength (ii) below, with a `MeasureDecreases` witness the caller supplies;
- `Iso.counterIso`/`Iso.counterIsoR` hold it **unconditionally** — they are the
  `MeasureDecreases` satisfiability witnesses (`counterMeasureDecreases`,
  `counterMeasureDecreasesR`), structure literals whose `law` is proved at the
  definition site like every entry in the list above. The earlier revision lumped
  these in with the folds by saying both "hold their law only on the terminal-seed
  domain", which is **false for `counterIso`/`counterIsoR`**.
- `Codec.uniqSeqIso`/`Codec.uniqSeqUnitIso` are the two leaves of the `Unambiguous`
  counterexample — unconditional structure literals like the rest, and not
  combinators a porting reader is looking for at all.

So the honest scope of the 13-value list is: it is the list of **structural**
unconditional isos a porter reproduces, and it is complete _of that category_ — it is
not an enumeration of every `Iso`-valued definition in the tree. The six omitted
values are a fold pair with a domain restriction, two counterexample witnesses and
two witness leaves; none is a combinator a porting reader is missing.

**Three of the thirteen have no in-tree caller at all, and that is expected rather
than a defect** (`codec-audit-round-five` R6-30). Measured by an environment walk over
referencing constants (ignoring the compiler's `.eq_1` unfoldings): `Iso.id`,
`Iso.ofTotal` and `Iso.associate` are referenced by **nothing** — they are the
category's identity and its two structural isos, shipped for a downstream author and
required by `[S3]` only as _combinators a porter must reproduce_. `Iso.element` and
`Iso.subset` used to be in the same position; they are not any more, because
`codec-audit-round-five` §2.3 gave them the **domain laws**
`Iso.element_unapply_eq_some_iff` / `Iso.subset_apply_eq_some_iff` — the answer to
`R6-07`.

**The heading used to say "Five" while this paragraph concluded three**
(`codec-audit-round-six` R7-19): "five" was the count _before_ the `element`/`subset`
domain laws existed, and only the heading was left behind when the body was corrected.
The number is **3**, it is the list above, and it is measured — not remembered.

**Two strengths, stated separately, because they are not the same strength.**
(i) For the **structural** isos in that list the law holds **unconditionally** — no
proof obligation, because `[D4]` removes the lossy `ignore` that would have needed
one. (No _instance_ hypothesis is exempt from this: `Iso.element` takes
`[DecidableEq α]` and `Iso.subset` takes `[DecidablePred p]`, so "unconditionally"
means "no isomorphism premise", not "no typeclass arguments at all" — an earlier
revision's bare "no hypothesis" read as the stronger claim.) (ii)
`Iso.foldl`/`foldr` also carry a `field`, but their `apply` is restricted to
**terminal seeds** (`Iso.foldl` refuses a seed that still unapplies), so they hold
_on that domain_, with a `MeasureDecreases` witness the caller supplies — which is
exactly what `[S4]` says. `[S1]` was previously written so that it appeared to
promise the folds were unconditional too; they are not, and the two anchors now agree
rather than contradicting.

**[S2] Format-agnostic naming.** `Syntax`/`parse`/`print`/`token` are the paper's
text vocabulary; on bytes they mislead, so they become `Codec`/`decode`/`encode`/
`byte`. **Only one of those four is a pure rename:** `Syntax → Codec`. The other
three are not cosmetic and should not be ported as if they were:

- `token → byte` changes the _carrier_ (`Char` → `UInt8`, `[D1]`);
- `parse → decode` changes the _result shape_ (whole-string matches → every
  `(value, remainder)` pair, `[D2]`);
- `print → encode` changes **what the argument is**: the paper's `print` is
  `print :: Printer α → α → Maybe String` — it takes an explicit _pretty-printer
  implementation_ value — while `encode` takes a `Codec` description —
  `encode : (d : Codec α) → α → Option (Σ n, Bytes n)`. An earlier revision called it
  "a method selected by the value's `Printer α` instance"; that is not the paper's
  form, and it is `[S2]`'s one real over-claim. The lead said only "changes the
  **argument**", which a reader takes as _whether_ an argument is passed — and both
  forms take one, so the lead contradicted the paragraph under it
  (`codec-audit-round-six` R7-18). The **conclusion survives** — this is the change
  with the largest porting cost — but the **reason** is that _what_ the argument is
  changed: the paper passes a `Printer α` **value**, `encode` passes a `Codec α`
  **description**.

  **Not "`[D6]`'s typeclass-to-value move", which an earlier revision cited here**
  (`codec-audit-round-seven` SHOULD-2). The paper's `print` is a plain top-level
  function over a `newtype` (§4.2), not an instance method — the only class in §3.4
  has `pure` and `token`. `[D6]` changed how the _description_ is represented; it did
  not move `print` out of a class, because `print` was never in one. The earlier
  sentence also called this "the one place `[S2]` and `[D6]` overlap", which that
  fact contradicts.

**[S3] Zero domain-specific leaf codecs.** Core ships every primitive leaf —
`byte`, `satisfy` — plus the non-leaf `pure` (a value-equality check, not a
format), **and one derived byte-run combinator, the `takeWhile` triple**.

That triple ships
as `relTakeWhile` / `decodeTakeWhile` / `encodeTakeWhile` (`Codec/Combinators.lean`),
with `decodeTakeWhile_spec`, `encodeTakeWhile_rel`, `encodeTakeWhile_ne_none` and
`encodeTakeWhile_of_decode` its laws. **Stated precisely, because an earlier revision
called this "the same shape every other combinator has" and that is false:**
`chainl1`/`chainr1` have **four** laws each (`decode…_spec`, `encode…_rel`,
`encode…_ne_none`, `encode…_of_decode`), and since `codec-audit-round-three` §1.5
(`openspec/changes/archive/2026-11-06-codec-audit-round-three/`) so do `takeWhile`
and `sepBy`.

**The rule covers C as well as Lean, and there is exactly one recorded exception.**
No per-format C, and no C that parses digits, numbers, fields or format structure
anywhere in the library. `Codec/`'s directory holds a single file that is not part of
the library — `Codec/CRef.c`, the bench's hand-written reference parser (moved into this
anchor from the 400-lines-later note by `codec-audit-round-nine` §7.10, so a reader of the
rule finds its exception in the rule). It _does_ parse bytes and says so in its own
header, and it is legitimate only because it is **bench-only**: no `@[extern]`, not in the
axiom gate, not reachable from any `Codec` module — it exists as the honest yardstick for
the performance claims. Do not add a second such file.

(That paragraph was first spliced in mid-sentence, so the following "It ships as
`relTakeWhile`…" read with `Codec/CRef.c` as its subject — a `.c` file shipping as three
Lean combinators. Caught by `codec-audit-round-nine`'s own review, M-1, which is the
round's restatement of a lesson already in this file: an insertion is a change to the
sentences _around_ it.)

The
fourth law takes a **`relFunctional`** hypothesis on the relation it transports —
`encode…_of_decode` needs it because the encoders are only right-inverses of the
decoders on functional descriptions. **How strong that obligation is, measured rather
than asserted** (`codec-audit-round-five` §D6 / R6-15; an earlier revision said it was
"conditional in **every** case" and that was too strong):

| combinator          | the `relFunctional` obligation                                                                                                                                                                     |
| ------------------- | -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `takeWhile`         | **derivable for any `p`** (`relTakeWhile_functional`); still _taken_                                                                                                                               |
| `sepBy`             | **two to derive, one to apply**: `relFunctional (Rel p)` and an `hstep` on `seqRight sep p` feed `relSepBy_functional`; `encodeSepBy_of_decode` itself takes only `relFunctional (relSepBy p sep)` |
| `chainl1`/`chainr1` | a genuine caller obligation                                                                                                                                                                        |

`takeWhile`'s step is `satisfy p`, whose bytes are determined by its _value_
(`t = single b` at length 1), so the obligation follows from the leaf's shape.

**"Derivable" is not "absent", and the row now says both** (`codec-audit-round-six`
R7-24). `encodeTakeWhile_of_decode` still takes `hd : relFunctional (relTakeWhile p)`
as a parameter; what `relTakeWhile_functional` proves is that a caller can always
supply it in one term, since that theorem quantifies over `p` and needs nothing else.
An earlier revision's "no hypothesis at all" described the lemma and read as a
description of the law, so a reader opening `encodeTakeWhile_of_decode` found a
hypothesis the table had said did not exist. Keeping the parameter explicit is
deliberate: it makes the `_of_decode` family uniform, because `sepBy`'s twin needs
the hypothesis for real.

**`sepBy`'s row is the mirror-image error, and it was introduced while fixing
`takeWhile`'s** (`codec-audit-round-seven` SHOULD-3). The row said the obligation is
"`relFunctional (Rel p)` **and** an `hstep`" — true of `relSepBy_functional`, the
_lemma that derives_ `relFunctional (relSepBy p sep)`, but not of
`encodeSepBy_of_decode`, which takes **one** premise: `hd : relFunctional (relSepBy p
sep)`. The row now says which is which. `sepBy`
is a `Rel p` head plus a `takeWhile`-shaped tail: the tail is derivable, the **head is
an arbitrary `Codec α`**, so its functionality is a hypothesis on `p`. `chainl1`/
`chainr1` existentially quantify a seed and operand list and then require the fold's
`apply` to land on `a`, so two different pairs can fold to the same `a` — that is an
open question, not an obligation this package discharges or claims to. So "four laws"
is still the same shape as `chainl1`'s, but the conditional is weaker than "in every
case" for two of the three. And `takeWhile` is a
_run-value triple_ like `relRepeat`, not one of the bounded-eight `Codec` values:
its bound is the **input length**, not part of the description (`[S6]`). (An earlier revision
cited the symbol `Codec.takeWhile`, **which does not exist** — `#check` reports an
unknown identifier; there is no single `Codec`-valued `takeWhile`, only the triple.)

**The fifteen a porting reader must reproduce**, because this anchor is the one a
porter reads to know what they must build — and **the earlier revision called this
"every `Codec`-valued definition in the tree", which is false**
(`codec-audit-round-five` R6-05): an environment walk finds **four** more public
`Codec` values that no row lists. See the second paragraph.

| value                                                                                | at                                       | bounded?                                   |
| ------------------------------------------------------------------------------------ | ---------------------------------------- | ------------------------------------------ |
| `byte`, `satisfy`                                                                    | `Codec/Codec.lean` (`[D6]` constructors) | leaf                                       |
| `pure`                                                                               | `Codec/Codec.lean`                       | relates only the empty string              |
| `empty`, `alt` (`\|`), `seq` (`∗`), `iso`                                            | `Codec/Codec.lean`                       | structural                                 |
| `count`, `manyUpTo`, `optional`, `maybe`, `choice`, `seqRight`, `seqLeft`, `between` | `Codec/Combinators.lean`                 | **bounded** — hence genuine `Codec` values |

**This is the `Codec` list a porter must reproduce** — seven `Codec` constructors plus
eight bounded `Codec`-valued definitions. (The `Iso` side is separate and is `[S1]`'s
thirteen combinators, below; an earlier revision said "the list a porter must reproduce",
which read as the whole surface.) It is **not** an enumeration of every `Codec`
value in the tree, and the earlier revision's "every `Codec`-valued definition is one
of these fifteen" was false (`codec-audit-round-five` R6-05): a walk of the compiled
environment (the method `Axioms.lean`'s definition check uses, not a `grep '^def'`)
adds **four** public `Codec` values that exist only as **counterexample witnesses**
for the hypothesis predicates — `uniqSeqBt`, `uniqSeqBo`, `uniqSeqD2`, `uniqSeqWhole`
(`Codec/`). They are part of the environment and are _not_ part of the reproduction
surface, which is exactly the distinction the completeness claim has to make.

`Normal`'s `fill` and `decodeNormal` are **not** `Codec` values — an earlier revision
kept them as a row here, and that row contained zero `Codec` values — they are the
quotient layer's own entry points and are documented in `[D4]` instead.

The bounded eight matter for two reasons. They are `Codec` values (so a porter must
have them), and `[S6]` **relies on `optional`** — an unbounded `many` cannot be a
`Codec` value, but `optional` and `manyUpTo k` can because their bound is part of
the description. Unbounded repetition is the `relRepeat`/`decodeRepeat`/
`encodeRepeat` triple exposed as a **run value** (`[S6]`), and `takeWhile` is the
same shape: a triple, not a `Codec` constructor, because its length is bounded only
by the input.

**The core module inventory**, because an earlier revision listed anchors by value but
omitted a whole public module. Every file below is public, ships gated laws, and is
part of what a porter must reproduce:

| module                   | what it is                                                                                                                                                                                            | sample gated laws                                          |
| ------------------------ | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ---------------------------------------------------------- |
| `Codec/Codec.lean`       | `Bytes n`, `Rel`, the `Codec` AST, `decode`/`encode`                                                                                                                                                  | `Codec.decode_spec`, `Codec.encode_rel`                    |
| `Codec/Iso.lean`         | `Iso`, the structural isos, `foldl`/`foldr`                                                                                                                                                           | `Iso.unfoldBy_sound`, `Iso.counterMeasureDecreases`        |
| `Codec/Sound.lean`       | the roundtrip/bidir laws, the hypothesis families                                                                                                                                                     | `Codec.roundtrip`, `Codec.huniq_not_derivable`             |
| `Codec/Combinators.lean` | the bounded `Codec` values and the `takeWhile` triple (no `sepBy`/`chainl1`/`chainr1` symbol exists — the module's own header says so and an earlier row claimed them, `codec-audit-round-nine` §7.8) | `Codec.decodeTakeWhile_spec`                               |
| `Codec/Encode.lean`      | the encoder's accumulator lemmas (the encoder's _soundness_ law is `Codec.encode_rel`, in `Sound.lean`)                                                                                               | `Codec.fastEncodeRepeat_eq`                                |
| `Codec/Decode.lean`      | `decodeFull` (the `Run` combinator)                                                                                                                                                                   | `Codec.decodeFull_spec`                                    |
| `Codec/Packed.lean`      | Layer 1: `decodeArray`, `decodeWhole`                                                                                                                                                                 | `Codec.decodeArray_eq`                                     |
| **`Codec/Normal.lean`**  | **`[D4]`'s quotient layer: `Normal`/`Normalizer`/`fill`/`decodeNormal`**                                                                                                                              | `Codec.decodeNormal_encode`, `Codec.decodeNormal_of_fixed` |
| `Codec/DecodeOne.lean`   | the committed-choice `decodeOne` (sound, completeness open — `[D3]`)                                                                                                                                  | `Codec.decodeOne_mem`, `Codec.decodeArray_unique`          |
| `Codec/ByteSlice.lean`   | Layer 2: the named C trust seams                                                                                                                                                                      | `Codec.findByte_spec`                                      |

**`Iso.law` is a _field_, not a law of this library**, and an earlier revision of the
table above listed it as one. It is the third field of `structure Iso` — the inverse
obligation a _caller_ supplies — and it appears in `Axioms.lean` only because Lean
compiles a field projection as a `thmInfo`-shaped constant, so the gate's
"walk `thmInfo`" enumeration sees it. Gating a projection of a hypothesis proves
nothing; it is the same category error as reading Layer-2's "no axioms" as "no trust".
What `[S1]` claims is that `law` is _required_, which is a fact about the structure's
shape, not a theorem about `Iso` values.

`Codec/Normal.lean` is the one an earlier revision omitted entirely: it is a public
module with its own gated laws, and `[D4]`'s whole quotient-as-object argument lives
there. A porter reading only `[D2]`/`[S3]`/`[S6]` would not have known the layer
exists.

**Two of those "laws" are not laws.** `Normal.fixed` and `Normalizer.idem` are
**structure projections** — a field of `Normal` and a field of `Normalizer` — and
they appear in `Axioms.lean` for exactly the reason `Iso.law` does above: Lean
compiles a field projection as a `thmInfo`-shaped constant, so the gate's walk sees
them. They are the _hypothesis_ a caller supplies, not theorems about it. An earlier
revision listed them beside `decodeNormal_encode`/`decodeNormal_of_fixed` as "gated
laws", which is the same category error it applies to `Iso.law` a paragraph later.

**And the list above is not closed by inspection.** A predicate that looked only at a
theorem's head constant and arity classified seven declarations as projections including
`Codec.roundtrip` — the library's central theorem — because Lean elaborates `hal.1` as
`And.left hal`, and `And.left`'s own body _is_ a projection. The gate now decides
structurally (`CodecAxioms.isBareProj`): a projection constant applied, at its first
explicit declared argument, to something that is itself a projection of a hypothesis. On
that test five further declarations are projections rather than laws and are allowlisted
as such: `Codec.CandAligned_fst`, `Codec.CandAligned_at`, `Codec.packedCands_mem`
(it _names_ a membership callers would otherwise spell out, but asserts nothing), and
`Iso.apply_eq_some_of_unapply` / `Iso.unapply_eq_some_of_apply`. `Codec.roundtrip`,
`Codec.findFrom_finds` and `Codec.CandAligned_tail` stay gated — `CandAligned_tail` is a
real proof about an invariant, not a selection.

It is `UInt8`-specialised and says so: its docstring names `varint` and UTF-8 as
the intended uses, i.e. it is the _shape_ those formats need, not any of them.
Every concrete format (`u8`/`utf8`/`varint`/…) still lives downstream
(`lean-basen`, `lean-text`): no named format is defined in core, and nothing in
core can silently bake in a text- or machine-specific assumption. `decodeRepeat` —
the already-proved `relRepeat`/`decodeRepeat`/`encodeRepeat` triple — is exposed as
a **run value**, never a `Codec` constructor (`[S6]`).

**[S4] `foldl`/`foldr` are distinct well-founded derivations, not `inverse ∘
foldl ∘ inverse`.** "Fresh" was an earlier revision's word and it over-claimed:
`Codec/Iso.lean` says the recursion is **factored once in the unfolding direction** —
`foldr` _reuses_ `unfoldBy`, the same well-founded driver `foldl` uses — while the two
`apply` directions are **separate** helpers (`foldApply`, `foldrApply`), so a porter
expecting `foldr`'s `apply` to be `foldl`'s with a swap will not find it
(`codec-audit-round-eight` S-2, which qualified the earlier unqualified wording). What is distinct, and what a
porter has to write, is two things: the **step type** below, and the **measure
witness** each fold supplies. "Type-incoherent" is checkable rather than rhetorical.
The types are, in the code:

```
foldl (i : Iso (α × β) α) (measure : α → Nat) (h : MeasureDecreases measure i)
    : Iso (α × List β) α                    -- step consumes β, accumulates α
foldr (i : Iso (β × α) α) (measure : α → Nat) (h : MeasureDecreasesR measure i)
    : Iso (α × List β) α                    -- step has β on the LEFT
```

**Written as the real `#check`, not an erasure of it.** An earlier revision showed
`foldr : Iso (β × α) α → Iso (α × List β) α` with a note that the measure and
witness were "omitted for clarity" — but `Iso.foldr i` is a `Π` over `measure` and
the witness, not an `Iso`, so the arrow was a false statement about the library
rather than a shorthand for one (`codec-audit-round-seven` SHOULD-1). The paper's
`foldl` is the first. The dual needs a step whose **argument order is swapped** —
`Iso (β × α) α` — and `inverse : Iso (α × β) α → Iso α (α × β)` produces neither
that argument order nor the right nesting, so no composition of `inverse`/`foldl`
has the type. An earlier revision of this section attributed `Iso ([α], β) β` to
the dual, which is not the code; the type claim is the one above.

Both folds take their own decreasing-measure witness (`measure : α → Nat` plus
`MeasureDecreases` / `MeasureDecreasesR`), a _precondition_, not an unconditional
law like the structural isos (`[S1]`).

**[S5] `relRepeat`'s least-fixpoint status is _proved_, not asserted.** The
repetition denotation is the least relation closed under the `nil`/`cons` rules;
an induction principle makes "least fixpoint" a theorem rather than a claim.

**The `nil` case is `n = 0`, and that is the paper's own closure, not a departure.**
`relRepeat R [] n s ↔ n = 0` (`relRepeat_nil`, literally `Iff.rfl`). The paper's
`many` closes its `nil` branch at `nil $ pure ()` (`PAPER.md:433-439`), and `pure x`
relates `x` to the **empty string only** (`PAPER.md:647`: `pure x = Rel [(x, "")]`) —
so the paper's closure is _the empty concrete string_, not "any string". On a
`Bytes n` substrate the empty string is the unique inhabitant of `Bytes 0`, so `n = 0`
**is** the same fact with the length in the type. Two things follow:

- it is what makes `relRepeat_induction` an induction on the **list** rather than on
  the string's length, which is the shape every proof in this family needs;
- `decodeRepeat_spec` is stated against this denotation, so a reader comparing it to
  the paper's `many` should read the two side by side — they agree.

**A previous revision of this section claimed the paper closed at `True` and that
`codec` "departs" to `n = 0`. That was wrong about the paper** (`codec-audit-round-nine`
review P2-PA1): there is no departure here, and a porter following the old warning would
have been told to solve a problem that does not exist. The misreading is easy to make
because `relRepeat`'s `nil` _rule_ in a least-fixpoint presentation is often written
`True`; the paper writes it as a `pure ()`, which is not.

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
list — it is `sepBy1`), as is `chainl1`, and there is **no** zero-or-more triple: an
earlier revision said "zero-or-more is `optional` of the one-or-more form", which is
false — `optional` maps `α ↦ Option α`, so it would give `Option (List α)`, not a list
of zero or more separated elements, and there is no `sepBy` `Codec` value to apply it
to in the first place. Zero-or-more is the empty case of the _relation_ (the empty
list), with no derived triple. None of these exist as bare `Codec`-building symbols.
This is the
same semantic content for `many`/`chainl1`, but it is a _representation_ difference
(typeclass embedding vs. inductive value), not merely a cosmetic naming change.

Everything not listed under a `[Dn]` is **kept**, and kept strongly: `Rel` is
preserved as the _specification_ (decoding is the paper's full relation, nothing
narrowed on top), and partial encoding is preserved. (The earlier wording — "everything
else is **kept**" — contradicted `[D7]`, which omits `iterate` entirely, and
`[S2]`/`[D1]`, which change `token`'s carrier; `codec-audit-round-nine` §7.2.)

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
[Performance](#performance--two-proof-layers-and-where-the-speed-goes).)

|                    | **`Bytes n`** (`= Fin n → UInt8`)                                                                                                            |
| ------------------ | -------------------------------------------------------------------------------------------------------------------------------------------- |
| **Job**            | the single _specification_ substrate (proof) and its scalar-read run-model                                                                   |
| **Shape**          | a length-indexed function; `s ⟨i, ·⟩` is a structural read, no `List` cons cell                                                              |
| **For the prover** | reducible under `simp`/`rfl`/`funext`; decidable equality is finitary (`funext` over `Fin n`)                                                |
| **At runtime**     | an **IR-level expectation**, not a theorem: `n` is a _type_ index, so a read _should_ lower to a scalar indexed load. Measured caveat below. |

**The decision.** Every law (`Rel`, `decode_spec`, `bidir`, `roundtrip`, …) is stated and
proved over the single `Bytes n`, because that one type is both what the proof assistant
can reduce _and_ what is expected to lower to a scalar indexed load. `decode d (s : Bytes n)` returns
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
[Performance](#performance--two-proof-layers-and-where-the-speed-goes) — keeping `Bytes n` as the specification
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
every law is a finite induction, and no second carrier is needed _for the laws_. So
the _specification_ has one byte-string type: **`Bytes n` is both the proof substrate
and its own scalar-read run-model**.

**Two lowering claims are in circulation here, and they are about different values —
keep them apart.** (i) For a `Bytes n` read, the claim that it lowers to a scalar
indexed load is an **IR expectation**, not a theorem: no law in this repository states
anything about emitted code, and IR inspection is the only evidence for it. (ii) The
repo also records that the _packed cursor_ is a `Nat` and
**does lower to a boxed bignum** — measured, not assumed. The lowering argument
primarily lives at the top of `Codec/Packed.lean` (the packed cursor and its `Nat`
indexing); `Codec/ByteSlice.lean` is where the `Nat` choice bites, since
`commitRemainder` is `USize`-indexed and so needs one conversion at the boundary. (An
earlier revision cited only `ByteSlice.lean`, which is not where the lowering lives.) These sit on opposite sides
of the boxed/unboxed line, and an earlier revision offered both as unlabelled
"lowering" claims, which reads as a contradiction unless you know which value each is
about. The honest summary: `Bytes n`'s index is _syntactically_ a type index (so a
compiler _can_ unbox it), the cursor is _not_ (and by measurement is not unboxed), and
neither is a proved property of this library. (The packed `Array`/`ByteArray` carriers
sit _above_ the substrate as proved-equal or trust-seam implementations; the laws never
leave `Bytes n`.) — see
[Representations](#representations--one-length-indexed-byte-string-the-spec-substrate).

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
n`, not a copied suffix. The exponential bound is what limits applicability either
way.

**Where the leak's growth actually is: unmeasured.** An earlier revision of this
paragraph continued "… — the leak's _growth_ is in the result list", stated inside a
passage introduced as the paper's own cost. The paper attributes the leak to no such
thing (it names only "unlimited backtracking"), and nothing in this repository has
measured it — no bench lane reports result-list allocation, and the memory figures
that _do_ exist are about `packedCands` and the array read (see
[Performance](#performance--two-proof-layers-and-where-the-speed-goes)), not about `decode`'s
`List (α × Suffix n)`. It is therefore recorded here as the project's **unmeasured
inference**, not as a measurement and not as the paper's claim. Stated as an
inference it is at least a plausible one — `decode` genuinely materializes a list —
but a plausible inference is what this section exists to stop presenting as fact.

### `[D4]` lossless capture — why we cannot follow the paper's destructive constructor

The paper's `ignore` maps _any_ run of whitespace down to a single value and, on
printing, emits back whatever `x` it was instantiated with — `skipSpace` (= `ignore
[]`) re-emits nothing, `optSpace`/`sepSpace` re-emit a single blank — but none of them
preserves the original length. (`ignore`'s own `g ()` is `Just x`, so "one fixed run"
is an _instantiation_, not `ignore` itself; `codec-audit-round-seven` NITPICK-1.) That is one-way loss: three spaces in, a fixed run out.

**What the paper actually says, quoted exactly, because a paraphrase used to sit
inside the quotation marks** (`codec-audit-round-six` R7-21). §3.1 says the authors
"will generally not be very strict with the invariant stated above", and "in
particular we will sometimes interpret this condition **modulo equivalence
classes**" — the paper is describing how _it_ reads the invariant, not stating that
the inverse law _holds modulo_ equivalence classes as a verified fact. The project's
reading is the second thing, and it is the project's: the loss is the equivalence
class, not a law that has been weakened in a checkable way.

`codec` cannot do that — not as a preference, but as a **consequence of the
isomorphism itself**. Every `codec` building block is a strict partial
isomorphism, and the inverse law is a _field_ you must supply to construct one:
`apply a = some b ↔ unapply b = some a`. A lossy combinator like `ignore` sends
_every_ run of whitespace (any length) to the same value, so its `apply` is a
constant. Substituting that into the field gives `True ↔ unapply () = some a` for
**every** `a` at once — satisfiable only for a single `a`, i.e. false as soon as `α`
has two distinct elements. That is why `ignore` cannot inhabit `Iso`: the law is an
`↔` quantified over _every_ `a`, and a constant `apply` cannot satisfy it twice.

Note what is **not** the reason, because an earlier revision of this section said it
and it is wrong: the failure is not that "two distinct inputs map to one output, so
`unapply` cannot choose". `unapply` is perfectly free to pick either one; a partial
isomorphism makes no claim that `unapply` is a function of the _input_ — it is a
function of the _output_. The obstruction is the `↔`'s universal quantifier, not any
ambiguity in `unapply`. (Separately, and consistently: `decode "   "` and `decode
""` would both yield the same value, so a re-emitted representation must be the one
canonical spelling — which is exactly what the `Normal S norm` quotient type of
`[D4]` above supplies, and why the lossy direction is `decodeNormal` composed
_outside_ the `Iso`.)

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
honest guarantee). `chainl1` needs **five** things — `Iso.foldl`, a
`MeasureDecreases` witness for that fold (a separate argument, not bundled into
`Iso.foldl`), a **terminal** seed (`Iso.foldl`'s `apply` returns `none` on a seed
that still unapplies), the repetition triple, and a `ConsumesByte` witness for the
decoder. `codec` supplies the two folds and both witness families —
`counterMeasureDecreases` for `foldl` and `counterMeasureDecreasesR` for `foldr`, so
neither law rests on an uninhabited premise — while the fold, the terminal seed and
the repetition are the caller's to supply for their own format. Nothing is lost and
no unsound law is shipped. (Earlier revisions of this paragraph said "`foldl` is all
`chainl1` needs", then "three", then "four"; all four statements now agree, at five.)

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

Naming (`token`→`byte`, `parse`→`decode`, `print`→`encode`) keeps the text-world
vocabulary from leaking onto bytes — and, as `[S2]` states, only `Syntax → Codec` is
a pure rename: the carrier, the result shape and the `print`/`encode` argument all
change with the name. The scope decision (`[S3]`) keeps core empty of concrete
formats, so nothing in it can silently assume text or one machine's endianness; the
first downstream leaf (`u8`, literally just `byte`) is the smoke test that the
framework is genuinely general.

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
no `many`/`many1` **value**, only the relation/decoder/encoder triple, and the
`sepBy` triple has "one or more" (non-empty) semantics. **Bounded** repetition is
different and _is_ available as a `Codec` value — `count` and `manyUpTo` carry their
bound (`Nat → Codec α → …`), while `optional` and `maybe` are finite because 0-or-1
is, not because they take a bound (`#check @Codec.optional` takes no `Nat`) — a bound is
part of the description, and 0-or-1 needs none. `optional` does take one implicit
argument, `[DecidableEq α]`, which is an obligation on a caller rather than a bound on
the description — `[D8]` says so, and an earlier revision of this sentence omitted it
(`codec-audit-round-nine` §7.9). A porter should look for these three readings, not for a
`many` object.

---

**Bottom line for a porter.** The paper gives the idea; `codec` makes it _honest_
by (1) enforcing the inverse law as a type, (2) resting on bytes, (3) keeping the
full backtracking semantics, which makes the **soundness/roundtrip** laws
unconditional (`roundtrip`, `bidir`, `decode_spec`), (4) being strictly isomorphic
— which rules out a lossy **`Iso`**, so the paper's `ignore` could not be an `Iso` here
at all (it is not that the constructor is banned: a lossy `Codec` value is perfectly
inhabitable, `Codec.pure x` being the obvious one — what strict isomorphism forbids is
presenting the lossy direction as one half of a bijection; `codec-audit-round-nine`
§7.5), and (5) making the description an ordinary value
you can induct over. Reproduce those first; the rest is bookkeeping you can
re-derive.

**One qualification on (3), because this is the paragraph a porter reads first.**
"Unconditional" holds for the _soundness_ family and **not** for the _uniqueness_
family: `encode_of_decode`, `encode_injective_of_unambiguous`, `decodeArray_unique`
and `decodeFull_spec` each take a per-description hypothesis (`Functional`,
`Unambiguous`, `RelAligned`, `huniq`) that **no composition inherits** — see the
paragraph on suppliers in "The abstraction, in brief". An earlier revision said the
laws are unconditional without that scope, which read as a promise the uniqueness
laws do not keep (`codec-audit-round-seven` SHOULD-5).

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

**But the hypotheses that gate the _uniqueness_ laws do not come for free, and a
composed codec does not inherit its leaves' uniqueness.** `encode_of_decode`,
`encode_injective_of_unambiguous`, `decodeArray_unique` and `decodeFull_spec` are each
conditional on a family — `Unambiguous`, `Functional`, `RelAligned`, `LengthDet`,
`LengthConst`, `huniq` — and **each family has a supplier at `Codec.byte`**
(`lengthDet_byte`, `relAligned_byte`, `lengthConst_byte`, `huniq_byte`, …). That
supplier establishes **satisfiability**, **not congruence**; and it is **not the only
supplier of every family** — `Unambiguous` has two composed suppliers,
`uniqSeqBo_unambiguous` and `uniqSeqD2_unambiguous`, besides `unambiguous_byte`
(`codec-audit-round-five` R6-18; an earlier revision said "only at `Codec.byte`" and
that was false for `Unambiguous`). What is true, and is the point, is: `Codec.uniqSeq_not_congruent` proves that
`Unambiguous d₁ → Unambiguous d₂ → Unambiguous (seq d₁ d₂)` is **false**, with a
counterexample where both halves are unambiguous and `seq` relates two distinct
values to one one-byte input. `uniqSeq_not_relAligned` refutes the same for
`RelAligned`. So every uniqueness-gated law in this tree is **leaf-only**: a
downstream format must discharge the family for _its own_ description, and a porter
who assumes composition will ship an unsound decoder.

The pair that _does_ close a composition is `Functional d ∧ RelAligned (Rel d)` —
that is what `decodeArray_unique` uses — and it is a hypothesis a caller supplies,
never one the leaves donate.

### Three generic primitives, added because a real codec could not be written without them

`[S3]` keeps core free of concrete formats — base2/4/8/10/16/32/64 live in
`lean-basen`, text in `lean-text`. **That rule is unchanged and this package ships
no format.** What it now also ships are three _format-agnostic_ primitives, because
every downstream leaf codec was otherwise blocked:

| was missing                         | what it blocked downstream                                                                   | now                                                                                                                                                                                                                                                                             |
| ----------------------------------- | -------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| a total-bijection `Iso` constructor | writing a leaf's `law` by hand, in `UInt8`/`UInt16`/`UInt32` coercion lemmas                 | `Iso.ofTotal f g hgf hfg` — law discharged from two round-trip equations                                                                                                                                                                                                        |
| `ConsumesByte` for `seq`/`iso`      | every composed codec proved productivity by hand (`lean-basen` does exactly this, per block) | `seqConsumesByte`, `isoConsumesByte`                                                                                                                                                                                                                                            |
| a single-value decode entry point   | a leaf author could only decode a _repetition_; `decodeOne` is committed-choice and unwired  | `decodeWholeOne` / `decodeWholeOneBytes`; `decodeWholeOne_eq` ties the **`Array`** entry point to the specification, and `decodeWholeOneBytes_eq` (`rfl`) bridges the `Bytes` one to it — the two **compose** to a `Bytes`-level statement, which is not itself a named theorem |

None of these names a format, an endianness, or a width — they are the shape every
leaf needs, which is why they belong in core and the leaves do not.

**Their in-tree status, stated precisely so it is not over-read — and the three
differ.** All three are proved (`[propext, Quot.sound]`-only, `#print axioms` run per
lemma), but an earlier revision said "**none has an in-tree caller**" and that is
**false for one of them**:

- **`isoConsumesByte` _is_ called in-tree** — **once**, in
  `Codec/Combinators.lean`'s `countSuccConsumesByte` (whose result then feeds
  `seqCountConsumesByte`). It is exercised by the library's own `count` proofs. (An
  earlier revision of this line named `seqCountConsumesByte` as the call site, which is
  the theorem the call's _result_ flows into; `codec-audit-round-nine` review P1-PA1.)

  **And that single call is invisible to every gate.** A provenance/mention count over
  the tree finds `Codec.isoConsumesByte` in exactly three kinds of place: its own
  declaration in `Codec/Sound.lean`, that one call site, and the gate's own
  `gatedNames`/`#print axioms` entries. The gate pins its **footprint**, not its
  **referrers**, so a refactor that deletes the call site leaves every count green —
  which is precisely the "check reports nothing" shape this round is named for. The
  claim is true of the source and unverifiable by proxy, so this note is the check:
  **re-read the call site by hand** rather than trusting a green build. (Measured in
  `codec-audit-round-nine` §7.6; no arm asserts it, and that is stated rather than
  papered over.)

- **`Iso.ofTotal` and `decodeWholeOne` are genuinely caller-free**: no concrete codec
  lives here to call them, by design, and their consumers are the downstream repos.
  **One correction on the entry point's provenance** (`codec-audit-round-nine`'s review,
  M-2): the sentence above says the entry point is "tied to the specification", and that
  is true of `decodeWholeOne` (`Array UInt8`), whose law `decodeWholeOne_eq` names
  `decodeFull` directly. It is _not_ a single theorem for the `Bytes`-level
  `decodeWholeOneBytes` — that one has only `decodeWholeOneBytes_eq` (`rfl`) to
  `decodeWholeOne`, so the `Bytes`-level link is a two-step composition nothing names.
  Stated because a reader checking the claim will look for the theorem and not find it;
  `grep -rn decodeWholeOne Codec/` shows exactly those two laws.

`[S3]` means this package cannot demonstrate the caller-free two _by example_ — that
is the rule working as intended, not a gap to be closed here.

## Scope

- **`codec`** (this package): the pure framework — `Iso`, `Codec`, `Rel`, the two
  interpreters (the single `Bytes n` substrate), and the laws. **No
  domain-specific leaf codecs** (not even `u8`).
- **`lean-basen`** (downstream): the numeral bases — `base2`/`base4`/`base8`/
  `base10`/`base16`/`base32`/`base64`, plus `varint` and `lengthPrefix` on top of
  them, with their conformance theorems. It is the worked example of this rule:
  `codec` ships the framework, `lean-basen` ships the formats. (An earlier revision
  of this line named `lean-binary`, which does not exist; the repo was renamed.)
- **`lean-text`** (downstream): `utf8` plus `text`/`identifier`/`whitespace` —
  the paper's §6 text domain, re-based on bytes.

## The gate that keeps the gates honest

Every claim in this document about "gated", "pinned" or "checked" is produced by
`Axioms.lean`, which runs on `lake build` and fails the build rather than warning.
**14 lines of output, each a measurement**, pasted verbatim from a green build
(long lines elided with `…`):

```
axiom gate: 345 public theorems covered (0 explicit exclusion(s))
axiom gate: 427 public theorems partitioned, 345 gated and 82 allowlisted
axiom gate: 140 public definitions covered, 115 mentioned and 25 allowlisted (mention proxy)
axiom gate: definitions dropped by the name classifier — 54 removed + 140 kept = 194 candidates, all removals reason-recorded; by pattern (6 of 12 remove exactly one; 0 uncounted): casesOn 8, recOn 8, elim 7, noConfusion 15, noConfusionType …
axiom gate: 12 def-name patterns enumerated, each matching a recorded non-surface declaration; their per-pattern counts are asserted by the def-classifier arm above (54 of 194 candidates removed)
axiom gate: header numbers verified (427 = 345 + 82; defs 140 = 115 + 25)
axiom gate: constant kinds — thm 771 (gated + allowlisted), def 348 (mention proxy), opaque 0 / axiom 0 (no arm, must be 0), induct/ctor/rec/quot 30 (machinery, not walked); globally 1355 `opaque` and 12 `axiom`, all of them Lean/stdlib — n …
axiom gate: stated footprints verified (771 theorem docstrings scanned, 153 mention a footprint spelling; 170 claim site(s) found = 157 checked + 13 skipped as 0 other-theorem + 0 no-owner + 13 `def`-docstring. Asserted: 157 checked, 153 me …
axiom gate: propProjections covers every bare projection (9 listed)
axiom gate: propProjections entries are all bare projections (9 listed of 12 bare projections in the namespaces; the rest are the `dec`-suffixed three, classified by suffix)
axiom gate: footprint labels — 9 emitted by the classifier, all 9 declared, all 9 classified, and all 9 classes exercised in BOTH directions by a semantics-written probe (so a right-key/wrong-class remap fails)
axiom gate: allowlisted theorems' footprints (82 entries: 39 axiom-free + 24 the permitted pair + 19 other permitted; 0 depend on `Classical.choice`; all four asserted)
axiom gate: recursion-principle promotion — `Codec.findFrom.induct` is gated, and `Codec.findFrom` is covered by 6 gated theorem(s) that are not its own principle (Codec.findByte_spec, Codec.findFrom_complete, Codec.findFrom_finds, Codec.fi …
axiom gate: authored exemption verified (1 entr(ies), all gated; the suffix rule alone would have dropped 0 of them — 0 means the exemption is currently dead code, which is the measured state and not a defect)
```

An earlier revision of this block said "Ten lines" and quoted ten — with **six of the ten
values stale** (`342→343`, `83→82`, `144→152`, `146→156`, `8→13`, and the two arms added
since). The excerpt had rotted while the gate stayed green, which is the exact failure mode
this block exists to warn about: a _quotation_ of an asserted gate is itself a number, and
nothing asserted it (`codec-audit-round-nine` review P1-NB6).

**Each line reports a denominator and its removals decomposed by cause, and both are
asserted.** A count that only gets printed rots silently — the history of this file
records that happening four times — so a number that cannot fail the build is treated as
weaker evidence than one that can, and the gate's prose says which is which.

Two lessons are worth more than the individual lines:

- **A check is only as good as what _enters_ it.** Ten audit rounds found no soundness
  defect — no `Classical.choice`, no `sorry`, every law `[propext, Quot.sound]`-only — and
  found the same _class_ of defect fourteen times: a filter on a check's input that nothing
  audits. `codec-gate-denominators` made that a precondition on adding an arm instead of
  something a reviewer must remember.
- **A vocabulary is a filter too.** The stated-footprint arm recognised
  `` `[propext, Quot.sound]`-only `` but not the same literal without `-only`, so claims
  spelled that way never became claim sites at all — 22 of 159 docstrings containing a
  backticked axiom list were invisible, including two this document previously cited as
  audited. The fix is a _third_ reported number: the denominator of the matcher itself,
  measured by an independently written broader predicate, reconciled against what the
  vocabulary recognised. A list can be audited against shrinkage and still be far too short.

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
  axiom-free: `byteSlice_spec`, `blitBytes_spec` and `commitRemainder_spec` report
  no axioms at all, while `findByte_spec` reports `[propext]` — it reduces through
  `Array.getElem?`, whose array-bound decision is propositional. That difference is
  recorded at each law, not treated as drift — `[propext]` is inside the gate.

  `findByte`'s body is a **constructive `Nat`-recursion** (`Codec.findFrom`), not
  `Array.findIdx?`. The earlier `findIdx?` body reached `Classical.choice` through
  `DecidableEq UInt8`, so `findByte_spec` reported
  `[propext, Classical.choice, Quot.sound]` while the prose claimed `[propext]`.
  That gap is closed: the scan is written out so the footprint is a property of the
  code, and five content laws (`findFrom_sound`, `_least`, `_min`, `_complete`,
  `_finds`, all `[propext, Quot.sound]`-only) state what `memchr` actually
  guarantees — the result is in `[off, size)`, holds `b`, and no earlier index does;
  `none` means no index `≥ off` holds `b`.

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
decodeWhole      : (d : Codec α) → d.ConsumesByte → Array UInt8 → Option (List α)
decodeWholeBytes : (d : Codec α) → d.ConsumesByte → Bytes n      → Option (List α)
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
"fast" `fastEncodeRepeat`** — **1.6× over the encoder that was already supposed to be
the fast one** (`32 / 20`), or **1.9× over `encodeRepeat`** (`32 / 17`). An earlier
revision said "a 1.9× improvement over the encoder that was already supposed to be the
fast one", which pairs the slow route's ratio with the fast route's name
(`codec-audit-round-seven` N-04).

### Where the speed actually goes (measured, with its causes named)

This section replaces an earlier one that claimed a "~20–40× slower than
hand-written C" ceiling and attributed it to the compiler boxing scalar
arithmetic. **That claim had no bench lane behind it and is withdrawn.** The
numbers below come from `bench`'s own `benchDecodeShapes` lane (task 6.4), which
measures four proved-equivalent decode shapes against a same-run `memcpy` and
prints both figures.

**First, a correction of yardstick.** `memcpy` is the wrong reference for a
per-element codec, and quoting a "× off C" ratio against it is a category error:
`memcpy` moves a byte for ~0.03 ns — ~125 ns per 4 KiB (a bulk copy,
hardware-accelerated), the figure the scale row below pins; an earlier revision wrote
`~0.045` here, **50 % off** the same section's own `~0.03` (`codec-audit-round-eight`
S-3, two committed numbers that refuted each other; the percentage was stated as 48 % and
is `(0.045 − 0.03)/0.03 = 50.0 %` — `codec-audit-round-nine` review P1-NB8, which also noted
that 48 % reproduces only by mixing a rounded `125 ns` with an exact `0.045 × 4096`) —
while a
parser does per-element _work_ — read, decide, advance, accumulate. The honest
reference for a parser is a hand-written C parser over the same bytes. **This repo
now ships one** (`Codec/CRef.c` + `benchCReference`; see "The hand-written C
reference" below) — an earlier revision of this paragraph said "this repo does not
yet ship one", which was true then and is not now, and contradicts the section at
the end of this document. So the figures below are given **as ns/step and as a
multiple of the measured pure-Lean floor**.

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

Measured in one session (**run vintage: 2026-11-07, `lake build bench` + `bench 4096 4096`**), two consecutive runs, `n` = 4096, load
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
the same process under the same load). An earlier revision of this section claimed
"~11×" from a floor of "**2.4 ns/step**"; that 2.4 was the _minimum of 5 decaying
rounds_ at an `8n` = 32 KiB working set, i.e. the most favourable endpoint of the
wrong variant.

**The floor is quoted here as `2.46–2.61 ns/step`, which is the range the committed
tables actually contain** (`codec-audit-round-nine` §2.5). An earlier revision of this
paragraph said `~2.6–3.0`, and **neither endpoint is a cell of any table in this
document**: the two burst tables give `2.50 / 2.61` and `2.57 / 2.46`, so the interval
that contains every committed value is `2.46–2.61`. The `3.0` upper bound came from the
same withdrawal as the `2.4` — it is the range of a _varying-load_ session's floor, not
of the two runs these tables record, and quote-a-range-not-a-point is not a licence to
quote a range that excludes the points. With `2.46–2.61` the gap to the decode row spans
**~10.5–11.5×** (`27.4/2.61 = 10.498` to `28.3/2.46 = 11.504`, both recomputed —
`codec-audit-round-nine` review P1-NB1, which caught a first attempt at this very sentence
that wrote `11.6`, a bound no same-run pair produces). The decode row moves with the
floor, so per-run quotients stay near `10.5`; the floor's own span is what widens the
range. **The padded-range defect is worth naming explicitly**: it appeared here three
times in one round (`~2.6–3.0`, `~20–22×`, and then `10.5–11.6`), each time by writing
one run's value and stretching the interval until it covered the other's.

| shape                                                    | lane                           | steps/burst | cold ns/step                 | warm ns/step (burst median) | note                                       |
| -------------------------------------------------------- | ------------------------------ | ----------- | ---------------------------- | --------------------------- | ------------------------------------------ |
| `memcpy` (`ByteArray.copySlice`, `@[extern]`), for scale | `benchCalibration`             | —           | ~0.03                        | —                           | ~125 ns / 4 KiB                            |
| `Array` indexed read alone                               | `arrayRead`                    | 4096        | see note                     | **65–67 ns/call**           | a single read, not a loop                  |
| **ideal `Id.run` cursor loop** (`arr[k]` + `Nat`)        | `idealCursor` (+`(burst)`)     | 4096        | 15                           | **2.46–2.61**               | **the achievable pure-Lean compute floor** |
| `decodeArray` single step (`List (α × Nat)` result)      | `decodeArray step`             | —           | see note                     | —                           | the per-step `List`                        |
| `packedCands` alone (now an `attach.map`)                | `packedCands (per step)`       | —           | 430–650                      | —                           | cold-input dominated; see below            |
| `decodeFullArrayRoot` (packed `Array` + `Nat` cursor)    | `decodeFullArray` (+`(burst)`) | 512         | see note                     | **~27.4–28.3**              | the whole decode, one candidate searched   |
| `decodeFullFastRoot` (`Bytes`/`Suffix` cursor)           | `decodeFullFast`               | —           | see note                     | —                           | the `Suffix`/`bdrop` path                  |
| `decodeFull` (the `Bytes n` specification itself)        | `benchDecodeFull`              | —           | no per-step figure committed | —                           | super-linear: re-walks the suffix per step |

**The `steps/burst` column was added here** (`codec-audit-round-nine` §2.4) so this
table says what the other two already said: the burst rows are `n` calls inside one
buffer, and whether that is `4096` or `512` decides what "per step" means. `4096` is
the whole `n`-byte buffer; `512` is `n/8`, because those rows decode an **`n/8`-byte
window** per call (the decode lanes stagger a window so the input differs per call).
A `—` means the lane is not a burst. **`arrayRead`'s `4096` does not make its cold
cell derivable**: it is one read per call, so the steps/burst count is not a divisor —
see the note below. Its warm cell is the **median range `65–67`**, not `~64–67`: the two
run medians are `67` and `65`, and an earlier revision's `64` was a _minimum_ of one run
mixed into a median range, which is neither the median range nor the full range
(`63–73`) — `codec-audit-round-nine` review P1-NB10. The `idealCursor` warm cell is `2.46–2.61` here, matching the
correction above (§2.5); an earlier revision of this row said `~2.5–2.7`, the same
kind of padded range.

All cold cells except the last are from the same two-run session and move with load;
they are order-of-magnitude, not point measurements.

**The `decodeFullFastRoot` cold cell is now `see note`, not `77 ns/step`**
(`codec-audit-round-nine` §3). The lane that would have to produce it,
`benchDecodeFullFast`, prints `"decodeFullFast root [n]: value + bridge OK
(unbenchmarked, see 6.1b)"` — it value- and bridge-checks the decoder **and prints no
timing at all**, which its docstring states twice: every in-process attempt produced an
impossible number (first `0 ns/op`, then `41 ns/op`, i.e. clock granularity and an
artefact respectively), so the lane was reduced to a check rather than left printing a
figure nobody should quote. The `77` was therefore never a cell of this session's run:
it traces to `openspec/changes/archive/2026-11-01-codec-review-remediation/tasks.md`
line 2407, an A/B **control** column (`| decodeFullFastRoot (control) | 76–77 | 74–75 |`)
measured at `n = 65536` in **`ns/byte`**, on **2026-11-01** — a different date, a
different `n`, and a different unit borrowed into an `ns/step` column. This is the same
defect as the `49` one row above, and it is the **citation** form of the subtraction
`AGENTS.md` forbids: the error is quoting another run's control rather than subtracting
two cells, which is why no arithmetic check would have caught it. The reproducible
figure for this path is the out-of-band `~1,250–1,500 ns/byte` recorded in the lane's
own docstring; it must **not** be placed in an `ns/step` column, because it is a
per-_byte_ quantity from a different harness — reinstating the category error in the
other direction.

**The `decodeFullArrayRoot` cold cell is now `see note`, not `49 ns/step`**
(`codec-audit-round-eight` §4). There is no run behind the 49: every committed
per-step value for this function in this document lies in **27.21–29.22** (all twelve
non-median cells too — the warm column, the per-step table above, and the two-run burst
rows; the **medians** are `27.37–28.54`), the caption on this
very table says all its cold cells come from one session, and 49 is **1.72×** the
largest of them — a factor no other row in the table shows. A number that is
underivable from the rest of its own table is indistinguishable from a number that
was never measured, so it is dropped rather than qualified — the same treatment
`arrayRead` and `decodeArray step` already had. **The fix is not a re-measurement**:
the lane that prints the figure is `benchRatio "decodeFullArray"` (`Bench.lean`), and
quote _its_ output with _its_ run vintage if you need a cold number. What it measures
is the _interleaved_ lane, which is a throughput question, not a compute floor.

**Four rows now carry no `ns/step` figure** — two deliberately
(`codec-audit-round-seven` N-02, N-03), and two because their figures were unsourced
(`codec-audit-round-eight` §4's `decodeFullArrayRoot` cold cell and `codec-audit-round-nine`
§3's `decodeFullFastRoot` cold cell, both above). The first
two are one-level quantities the table used to divide by `n` anyway:

- **`arrayRead`** performs **one** `getD` per call, and `benchRatio` prints `ns/op`.
  Reporting "11–12 ns/step" means dividing one read by `n` = 4096, i.e. implying a
  single array read costs ~45,000–49,000 ns against the **65–67 ns** the burst lane
  measures for the identical one-read call — a 700× inversion. The honest figure is the
  burst one, and it is in the next column.
- **`decodeArray step`** was quoted at cold **12** while `idealCursor` — the bare,
  allocation-free cursor loop that a `decodeArray` step must _contain_ — is **15**.
  A component priced below the loop it contains is the arithmetic impossibility
  `Bench.lean` names for `packedCands`; the two figures cannot both be right, and
  neither is re-measured here, so neither is quoted.

Both rows are still in the table because the lanes exist and the _warm_ figure for the
first is sound; what was removed is only the per-step division that made them wrong.
(The fourth of the four is the `decodeFullFastRoot` **cold** cell above, dropped for the
same reason as the third — no lane prints a timing for that path, and the `77` came from
another session's `ns/byte` control. Its row has no warm figure either, because
`benchDecodeFullFast` never times anything.)

**The last row carries no per-step figure on purpose** (`codec-audit-round-six` R7-27): an earlier revision
printed `~31,200 ns/step`, and no run table anywhere in this document produced it —
`benchDecodeFull` prints one **batch** figure (`decodeFull byte [n]: <ns>/op`), and
that is the only form the lane emits. A per-step figure with no committed run behind
it is the same defect as the withdrawn `52.4 − 27.4`. The row is kept, the number is
not: quote `benchDecodeFull`'s own output if you need this lane. The two burst rows are the ones a gap may
be taken from, and only as a range.

**The `packedCands` row, and a figure that has now been withdrawn twice.** The old
entry here claimed **3 ns/call on a hot, constant array**. **That claim is deleted,
not qualified.** It came from a sink of `(…).length` — a constant `1` for a codec with
one candidate — so the optimiser dropped nearly the whole call; a function that
indexes an array cannot cost 3 ns in a tree where the bare index measures **65–67 ns
per call** (the `arrayRead` burst row below). An earlier revision made this argument
against `~12`, which is the _withdrawn_ per-step division the `arrayRead` note three
paragraphs down deletes as a 700× inversion (`codec-audit-round-eight` S-1: the
conclusion survived, the premise was the number this very section repudiated). It was
never a `packedCands` number.

The replacement is the lane in `benchDecodeShapes`, which is a **burst** over 8
buffers that differ _at the cursor_ (buffers differing only at byte 0 yield the same
candidate and an invariant sink — the gate now rejects that), with the candidate
values folded into the sink. **This row is the 8-buffer variant, unlike every other
burst row here** (`codec-audit-round-eight` N-5): its closures ignore the buffer
`benchBurst` hands them and index `bufs[j % 8]` themselves, so its working set is
8 × 4 KiB rather than one buffer — the `(burst@8buf)` lane below is the same shape
printed side by side, and the difference between the two rows is the price of that
working set rather than of `packedCands`:

| lane              | burst (min / median / max, ns per call) |
| ----------------- | --------------------------------------- |
| `packedCands k=1` | 85 / 86 / 87                            |
| `packedCands k=2` | 105 / 106 / 107                         |

Two calibration notes, both of which cost a wrong figure this session:

- **`lean --run` is the interpreter, not the compiled cost.** A `lean --run` probe of
  this exact call reads ~850–1050 ns/call. Quoting that against the compiled 86 is a
  10× error in the other direction. Only rows printed by the `lake build bench`
  executable may be quoted.
- The interleaved-lane figure (**430–650 ns/call**, two runs, above) is _cold_: it
  re-touches a 4 KiB array per call. It is a memory figure wearing a compute label,
  which is exactly the confusion this section exists to keep apart.

**What the numbers say, stated at the strength the evidence supports.** In a warm
loop the packed decoder is **27.37–28.54 ns/step** (the four committed **medians**, which is
what this document's rule says to quote) **against a 2.46–2.61 ns/step pure-Lean
floor** — **~10.5–11.6×** over those four medians (`27.37/2.61 = 10.49` to
`28.54/2.46 = 11.60`), agreeing with the same-run `~10.5×` two paragraphs up because both
terms move together — and the whole of that gap is per-step work (a `List`
cell, the search, the accumulator), not memory bandwidth. The decoder's per-step
figure is quoted in **one** column only — the warm one. Its cold cell is `see note`
in the table above (`codec-audit-round-eight` §4): the `49 ns/step` this paragraph
used to restate has no run behind it, and repeating an unsourced number in prose is
how a withdrawn figure survives its own deletion. For a cold figure, read what
`benchRatio "decodeFullArray"` prints — that lane is the source, and it answers a
_throughput_ question, which is not the compute floor the warm column measures.

**One thing the table above does _not_ cover — now measured.** `Codec.byte` has
**exactly one candidate per cursor position**, so `decodeFullArraySearch` never
iterates on that workload: the `~10.5–11.5×` is the degenerate `k = 1` case of a
backtracking search. The `k > 1` lane prices the difference. Its codec is
`satisfy (fun _ => true) | satisfy (fun _ => true)` — **two candidates at every
position**, each consuming one byte and each able to complete the buffer — and the
lane **asserts its premise** (`packedCands` length is 1 at `k = 1` and 2 at `k = 2`)
before timing, so a run that silently degenerates fails instead of reporting a
number.

Measured in one session (**run vintage: 2026-11-07**), two consecutive `bench 4096 4096` runs at load ~2.9 on 10
cores, burst medians. **The burst span differs by row and the per-step figures each
use their own:** `idealCursor` runs **4096** steps per burst (the full `n`), while
`decodeFullArray` and `decodeFullArray k=2` run **512** (`n/8`, a different window
decoded per call). An earlier revision captioned this table "512 steps per burst"
and it was wrong for the `idealCursor` row by 8×, which made the floor look 8× worse
than it is to a reader who divided by the caption instead of the row
(`codec-audit-round-five` R6-26):

| lane                        | run 1 (min / median / max) | run 2 (min / median / max) | ns/step         |
| --------------------------- | -------------------------- | -------------------------- | --------------- |
| `idealCursor`               | 10136 / 10253 / 10446      | 10573 / 10709 / 10828      | 2.50 / 2.61     |
| `decodeFullArray` (`k = 1`) | 14467 / 14615 / 14695      | 13965 / 14087 / 14346      | **28.5 / 27.5** |
| `decodeFullArray k=2`       | 27695 / 28105 / 28210      | 25767 / 26173 / 26546      | **54.9 / 51.1** |

**The `packedCands` rows are deliberately _not_ in this table.** They are a
_different_ run of a _different_ lane (`benchDecodeShapes`, 200 steps per burst),
and an earlier revision of this document printed them here next to a set of figures
from another session — which is how the same lane came to be quoted as **two
different triples** for `k = 1`. One figure, one run, one table. The `packedCands`
numbers are the ones two paragraphs above: **86 / 106 ns per call** (`k = 1` /
`k = 2`), from `benchDecodeShapes`. The earlier triples that used to sit here were
produced by a **bug in that lane** — its closure computed `j % (a.size + 1)` and the
accompanying bound proof inside the measured region, so it priced a `Nat` modulus and
a proof-term construction rather than `packedCands`. `Bench.lean` records the fix (the
cursor is now hoisted out of the closure and the premise asserts it). **Both earlier
triples are withdrawn, and so is any derivation from them** — their _values_ are
deliberately not reproduced here (`codec-audit-round-eight` N-4: quoting a withdrawn
figure in the paragraph that forbids quoting withdrawn figures re-fires the claim, the
same trap the footprint arm's `FP_BOTH`/`FP_PROPEXT` stripping exists to avoid). They
are in the git history if you need to check them.

**What that says — the search is linear in `k`, and its cost is not all in
`packedCands`.**

- The second candidate costs **~24–26 ns/step** — one whole extra decode step, so the
  backtracking search runs at **~1.9×** the `k = 1` decode. **Derived from the
  table above, both terms the same lane in the same run:** `54.9 − 28.5 = 26.4`
  (run 1, medians) and `51.1 − 27.5 = 23.6` (run 2, medians). Quote it as that
  range with its run number, never as a point. **An earlier revision said "~25
  ns/step (52.4 − 27.4)" and both terms were wrong:** `52.4` appears nowhere else
  in this document, and `27.4` belongs to the _first_ `bench 4096 4096` table (the
  interleaved lane, run 1) — so the subtraction crossed both tables **and** runs,
  which is exactly what the "same lane in the same run" rule three bullets below
  forbids. The orphan is deleted (`codec-audit-round-five` R6-08). The `~10.5–11.5×`
  headline is therefore a **lower bound** for a real backtracking codec; the gap to the
  floor is **~19.55–21.96×** (run 1: `54.9 / 2.50 = 21.96`; run 2: `51.1 / 2.61 = 19.5522`,
  both recomputed with `python3` rather than by eye — `codec-audit-round-nine` §2.7). The
  earlier form `~19.6–22.0×` was itself a padded range — `19.58 < 19.6` and `21.96 < 22.0`
  — which is the exact defect the paragraph is about, caught by the round's own review
  (A-9). The
  range is the two run-points, not their midpoint, and it must be **wide enough to
  contain its own endpoints** — an earlier revision wrote "~20–22×", whose lower bound
  `20` excludes run 2's own quotient of `19.55`, and the form before this one,
  `~19.6–22.0×`, still excluded both. A range written from one run and stretched to fit
  the other is this document's recurring defect; `~19.55–21.96×` is the two quotients
  with no padding at either end.
- `packedCands` moves **86 → 106 ns/call** for the extra candidate: **~20 ns** of the
  ~24–26 ns per-candidate cost. So **~4–6 ns/step is _not_ `packedCands`** — it is the
  `decodeArray` re-list plus the singleton `PackedCand` allocation in
  `decodeFullArraySearch`. That residue is what a rewrite would have to attack, and
  it is a measured number rather than a guess. (That ~20 ns is taken from the
  `benchDecodeShapes` pair above, not from this table — the subtraction is
  legitimate only because both terms are the same lane in the same run, which is
  exactly the property the withdrawn pair did not have.)
- `packedCands` measures **86 ns/call** at `k = 1` and **106** at `k = 2` in the
  compiled burst lane. The older "3 ns/call hot" figure is **withdrawn outright** —
  it was a folded-away sink, not a measurement (see the note above).

**Nothing was optimised as a result.** The task was to price the term _before_
rewriting it, and the numbers say the rewrite is worth **~4–6 ns/step** of a
**51.1–54.9 ns/step** decode — real, but neither the dominant term nor a change to make
on a guess. The range is `24–26 − 20 = 4–6`, and its upper end is `26.4 − 20 = 6.4`; an
earlier revision wrote "~4–7", which no term in the derivation produces
(`codec-audit-round-six` R7-25). The decode figure was `~55 ns/step`, a _point_ for a
two-run range whose lower end is `51.1` — the padded-point form of the same defect the
ranges above had (review P1-NB11).

### The hand-written C reference — the yardstick that was missing

Every figure above is relative to this repository's own pure-Lean cursor loop.
That answers "how much per-step work does the codec do above the cheapest Lean
loop", which is a real question — but not the one a reader asks, which is **how far
is this from a hand-written C parser over the same bytes**. `AGENTS.md` has said for
several revisions that a `memcpy` ratio is a category error here (it moves a byte;
a parser does per-element work) and — **historically** — that "the honest reference
is a hand-written C parser, which this repo does not yet measure". **That last clause
is quoted as what `AGENTS.md` used to say, not as current text**
(`codec-audit-round-five` R6-25): `AGENTS.md` now reads "This repo now measures
one", so an unqualified quote reads as a claim the file still makes. It does not.

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

Measured in one session (**run vintage: 2026-11-07**), two consecutive runs, load ~1.4 on 10 cores, burst medians.
**The burst span is given per row**, because the three lanes do not share one:

| lane                           | steps/burst | run 1 (min / median / max, ns) | run 2 (min / median / max, ns) | ns/step         |
| ------------------------------ | ----------- | ------------------------------ | ------------------------------ | --------------- |
| `idealCursor` (Lean loop)      | **4096**    | 10380 / 10532 / 10669          | 9982 / 10059 / 10643           | 2.57 / 2.46     |
| **C reference** (hand-written) | 512         | 3501 / 3598 / 3783             | 3482 / 3507 / 3575             | **7.03 / 6.85** |
| `decodeWhole` (Lean)           | 512         | 14487 / 14623 / 15477          | 13755 / 13811 / 14197          | **28.6 / 27.0** |
| **Lean ÷ C**                   | —           | **4.1×**                       | **3.9×**                       | **~4×**         |

**The span column is not decoration — an earlier caption said "512 steps per burst
(the window every row here decodes)", and it was wrong for the first row**
(`codec-audit-round-six` R7-11). `10532 / 512 = 20.57`, not the `2.57` the row states;
`10532 / 4096 = 2.57`. The figure was always correct for its own span and only the
caption was wrong, so the fix is the caption, **not a re-run**. This is the same
defect (`R6-26`) that was fixed in the table above while this one was being written.

**What that settles, including one thing it upsets.**

1. **The gap to hand-written C is ~4×, not 10–21×.** The 10–21× figures are _against
   this repo's own floor_, and quoting them as "off C" was the category error
   `AGENTS.md` warned about, committed by omission — there was no C column, so the
   Lean-relative number was the only one available and it read as an absolute.
2. **The Lean floor is itself ~2.7× _faster_ than the C reference** (`2.46–2.57`
   against `6.85–7.03` ns/step, the actual cells — `codec-audit-round-nine` §2.6: an
   earlier revision wrote `2.5 vs 6.9`, and **neither is a cell of the table this
   sentence cites**; the quotient runs `2.67–2.86×`). That is not a paradox and not a
   win: the floor sums bytes and allocates
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
the same samples, and, **recorded by hand beside each result**, the load average).
The last one is a documentation practice, not a feature of the lane: no lane reads
or prints load (`codec-audit-round-eight` S-4 — an earlier revision listed it among
the things `benchDecodeShapes` "prints", which was a claim about tooling that the
tooling does not make). It is a
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
