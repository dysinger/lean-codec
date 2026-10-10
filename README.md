# codec

A verified, bidirectional codec library for Lean 4 (repo directory: `lean-codec`).

**Intent.** Take Rendel & Ostermann's *"Invertible Syntax Descriptions:
Unifying Parsing and Pretty Printing"* (Haskell Symposium 2010) and make it
**more dependently typed, more provable — and binary.**  The paper gives the
idea: one description, two directions, related by invertibility.  `codec` is
the same idea, carried further in Lean, to completion:

- **Provable, not asserted.**  The paper *states* the `Iso` invariant and
  notes in passing (§7.5) that it "would be interesting to see" it encoded
  dependently.  `codec` answers: the inverse law is a **field**, so an `Iso`
  without its proof cannot exist, and the roundtrip is a **closed theorem**.
  Invertibility is enforced by the type system, not documented in prose.
- **Dependently typed where the paper is loose.**  The paper's `Iso` invariant
  is "modulo equivalence classes" in places — because it *loses* optional bytes.
  `codec` removes the loss (departure #4), so the strict inverse law holds
  **unconditionally**; the "relaxation" is not carried, it is *eliminated*, and
  the precise law is a type-checked field.
- **Binary, and more.**  The paper is text-only (`String`/`Char`) and never
  considers binary.  `codec`'s core is a byte sequence, so it covers fixed-width
  integers, endianness, image files, and LEB128 varints — and text/Unicode is
  rebuilt downstream as a codec composed on top of bytes.

One description, two directions.  `decode (encode x) = x`, *proved*, for every
well-formed `x` — not tested, not asserted, and not discharged by a solver.

- **Pure framework.** `codec` ships `Iso`, `Codec`, `Rel`, the two
  interpreters, and the laws — **zero domain-specific leaf codecs** (not even
  `u8`; the only descriptions are the primitives `byte` and `pure`).
- **Byte concrete syntax.** Everything concrete is a downstream package built by
  composition: `lean-binary` (binary leaves) and `lean-text` (text/Unicode).
- **Proof-carrying by construction.** There is no "verified vs unverified"
  tier; every codec is verified by its type.

See `openspec/invertible-binary/proposal.md` for the full design, and
`openspec/invertible-binary/tasks.md` for the task ledger.

---

## From the paper to a dependent, binary codec

The paper is the **foundation**, not a spec to transcribe.  We change exactly
**four** things about its *observable semantics* — and strengthen it in ways
that are not semantic changes at all.

**Departures** (observable-semantics changes):

1. **`String`/`Char` → `ByteArray`/`UInt8` (bytes become the base unit).**  The
   paper's concrete syntax is textual (`Rel : [(α, String)]`, `token : δ Char`).
   Our core targets binary (fixed-width integers, endianness, image files, LEB128
   framing); a byte base is the natural fit, and bytes become the primitive,
   with text rebuilt downstream in `lean-text` on top of them.

2. **Nondeterministic list-decoder → a deterministic decoder.**  The paper's
   decoder returns a *list* of results (`[(α, String)]`) — a relation — and the
   paper itself admits it is exponential (§4.4).  We need speed, so `decode`
   returns a single result plus the remaining bytes.  This is a real semantic
   narrowing (the paper's §4.3 "decode = find a pair" becomes "decode = the
   unique pair"), made explicit: on the `Unambiguous` domain — at most one value
   per input, a **per-codec proof obligation the library does not decide** — the
   deterministic decode is sound and complete w.r.t. `Rel`.

3. **`|` becomes committed choice, not full backtracking.**  A consequence of
   determinism (a single result cannot try both branches), not a forced re-base.
   §4.4 notes predictive `|` (Parsec) is a common *deviation* from full
   backtracking — evidence that committed choice is practical — but determinism
   is the actual reason we adopt it.  Backtracking and peeking are out of scope.

4. **Lossless capture — "allowed" bytes are kept, not discarded.**  The paper
   (§3.1, §6.3) deliberately *discards* optional bytes (`ignore`/`skipSpace` map
   arbitrary whitespace to `unit` and back to a single blank), and therefore
   **abandons a strict isomorphism** in favor of "modulo equivalence classes".
   We reject that weakening: a run of bytes a codec allows is captured as a
   value and re-emitted verbatim — realized by the existing `many (subset p
   byte)` idiom, *not* a new primitive.  Consequently `decode (encode x) = x`
   holds **byte-for-byte** — a true isomorphism, in place of the paper's
   "modulo equivalence classes" weakening.  There is therefore **no `ignore`
   combinator in core**; it is the one thing that would reintroduce the loss.

`encode` staying partial (`Option`) is **not** a departure — it is a *kept*
property: `empty`/`pure x`/`subset p` reject out-of-domain values exactly as the
paper's `Maybe` encoder does.  We deliberately do **not** totalize `encode`.

**Strengthenings** (not semantic changes — we complete paper under-specifications
and remove text-flavored naming):

- **`Iso` invariant, made a field — and it now holds *unconditionally*.**  The
  paper §3.1 states the inverse invariant in prose and admits it is unchecked;
  §7.5 notes in passing that it "would be interesting to see" it encoded in a
  dependently typed language.  We answer: `Iso.law` is a **field**, so an `Iso`
  without its proof cannot be built, and `codec_roundtrip` is a **closed
  theorem** over `Codec`.  Crucially, because departure #4 removes the
  lossy `ignore` primitive, the strict law
  `∀ a b, apply a = some b ↔ unapply b = some a` holds for **every** core
  combinator — there is no residual "modulo equivalence classes" escape hatch.
  (The paper's lossy combinators would need a *coarser* law; we simply do not
  have them.)
- **Naming made format-agnostic.**  `Syntax`/`parse`/`print`/`token` are the
  paper's text vocabulary (its §1 says concrete syntax is "sequences of
  characters"; its §3.4 says `token` "relates each **character** with itself").
  On bytes those names mislead, so we use `Codec`/`decode`/`encode`/`byte`.  This
  is a rename, not a semantic change.
- **A format-agnostic core with zero *domain-specific* leaf codecs.**  A *scope*
  decision: the only primitive descriptions in core are `byte` and `pure`;
  nothing in `Iso`/`Codec`/`Rel` mentions `u8`, `varint`, or `utf8`, so we ship
  none and put every concrete format downstream (`lean-binary`, `lean-text`).
  Separation of concerns, not a claim of forced necessity.

Everything else is **kept**, and kept strongly: `Rel` is preserved as the
*specification* (determinism is an operational constraint layered on top of it),
and partial encoding is preserved.

---

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

-- Layer 2: denotational semantics (the paper §4.3)
def Rel (d : Codec α) (x : α) (s : ByteArray) : Prop := ...

-- the two interpreters (format-agnostic naming):
--   decode : Codec α → ByteArray → Except DecodeError (α × ByteArray)  -- returns errors
--   encode : Codec α → α → Option ByteArray                            -- partial

-- the two theorems that make "one description = one relation" precise:
--   bidirectional:  Unambiguous d → (Rel d x s ↔ decode d s = .ok (x, empty))
--   roundtrip:      encode d x = some s → decode d s = .ok (x, empty)
```

Every `Codec` is a composition of `Iso`s via `$`/`*`/`|`/`pure`/`byte`, so the
inverse guarantee is **structural**: the `Iso` law is a field, and the two
`Rel` theorems above close by composition — no solver, no per-combinator lemma.

---

## Scope

- **`codec`** (this package): the pure framework.  `Iso`, `Codec`, `Rel`,
  `decode`/`encode`, error reporting, and the laws.
- **`lean-binary`** (downstream): `u8`, `u16le`/`u16be`, `u32le`/`u32be`,
  `u64le`/`u64be`, `bytes n`, `count n`, `varint`, `lengthPrefix`, image-header
  and Protobuf demos, and the speed benchmark.
- **`lean-text`** (downstream): `utf8 : Iso String (List UInt8)` plus `text`/
  `identifier`/`whitespace` — the paper's §6 text domain, re-based on bytes.

The core contains **no domain-specific leaf codecs** (its descriptions are `byte`
and `pure`); the first downstream leaf (`u8`, a one-line `byte`) is the
acceptance test that the framework is genuinely expressive.

---

## Status

Planning/review complete (`openspec/invertible-binary/`).  Implementation has
not yet started; the task ledger (`tasks.md`) is the authority for what comes
next.
