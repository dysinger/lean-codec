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
is the `List UInt8` model; `ByteArray` is the later executable wrapper (§7),
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
The provable core is `List UInt8`; `ByteArray` (whose FFI-backed ops do not
reduce under `simp`) is the later executable wrapper transported on top.

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
`_spec`/`_rel` laws. The efficient `ByteArray` wrapper + benchmark remain future
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
