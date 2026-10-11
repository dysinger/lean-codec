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
  `codec` removes the loss (departure #4), so the strict inverse law holds
  **unconditionally**; the "relaxation" is not carried, it is *eliminated*, and
  the precise law is a type-checked field.
- **Binary, and more.** The paper is text-only (`String`/`Char`) and never
  considers binary. `codec`'s core is a byte sequence, so it covers fixed-width
  integers, endianness, image files, and LEB128 varints — and text/Unicode is
  rebuilt downstream as a codec composed on top of bytes.

One description, two directions. `decode (encode x) = x`, *proved*, for every
well-formed `x` — not tested, not asserted, and not discharged by a solver.
(The encode→decode direction is the *unconditional* `roundtrip` law; the
decode→encode converse holds byte-for-byte only for *functional* descriptions —
see the `Functional` predicate in `Codec.Sound`, since backtracking `|` may map
one value to several byte strings.)

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

The paper is the **foundation**, not a spec to transcribe. We change exactly
**four** things about its *observable semantics* — and strengthen it in ways
that are not semantic changes at all.

**Departures** (observable-semantics changes):

1. **`String`/`Char` → `List UInt8`/`UInt8` (bytes become the base unit).** The
   paper's concrete syntax is textual (`Rel : [(α, String)]`, `token : δ Char`).
   Our core targets binary (fixed-width integers, endianness, image files, LEB128
   framing); a byte base is the natural fit, and bytes become the primitive,
   with text rebuilt downstream in `lean-text` on top of them. The provable core
   is the `List UInt8` model; `ByteArray` is the later executable wrapper (§7).

1. **Nondeterministic list-decoder → kept, not narrowed.** The paper's
   decoder returns a *list* of results (`[(α, String)]`) — a relation. We once
   narrowed this to a deterministic single-result decoder for speed (the paper's
   §4.4 admits the nondeterministic decoder is exponential), but that narrowed
   `|` into *committed* choice, which is **incompatible with the paper's `|`
   and `many`** (an empty branch always wins; `nil`/`cons` are never
   prefix-disjoint). We have **restored** the paper's semantics: `decode :
   Codec α → List UInt8 → List (α × List UInt8)`, with `|` as list
   concatenation. The laws are now *unconditional*. Efficiency is future work
   (§4.4's open problem), not a reason to change the semantics.

1. **`|` is the paper's backtracking union, not committed choice.** `decode
   (d₁ | d₂) s = decode d₁ s ++ decode d₂ s`, matching `Rel (d₁ | d₂) = Rel d₁
   ∨ Rel d₂` by construction. (The earlier committed-choice deviation and its
   prefix-disjointness gate are gone; see departure #5.)

1. **Lossless capture — "allowed" bytes are kept, not discarded.** The paper
   (§3.1, §6.3) deliberately *discards* optional bytes (`ignore`/`skipSpace` map
   arbitrary whitespace to `unit` and back to a single blank), and therefore
   **abandons a strict isomorphism** in favor of "modulo equivalence classes".
   We reject that weakening: a run of bytes a codec allows is captured as a
   value and re-emitted verbatim — realized by the existing repetition over a
   `subset p byte` step (`relRepeat (Rel (subset p byte))` denotation,
   `decodeRepeat`/`encodeRepeat` interpreters), *not* a new primitive. Consequently `decode (encode x) = x`
   holds **byte-for-byte** — a true isomorphism, in place of the paper's
   "modulo equivalence classes" weakening. There is therefore **no `ignore`
   combinator in core**; it is the one thing that would reintroduce the loss.

1. **`|` needs no prefix-disjointness condition.** This was the one *open*
   departure under the (now-reversed) committed choice. With `|` as the paper's
   backtracking union (departure #2/#3 above), no prefix condition is required —
   and none works for repetition anyway (`[]` is a proper prefix of every
   non-empty string, so `nil | cons` is never prefix-disjoint). The former
   `NonNull`/`PrefixDisjoint`/`Disjoint` machinery is deleted.

`encode` staying partial (`Option`) is **not** a departure — it is a *kept*
property: `empty`/`pure x`/`subset p` reject out-of-domain values exactly as the
paper's `Maybe` encoder does. We deliberately do **not** totalize `encode`.

**Strengthenings** (not semantic changes — we complete paper under-specifications
and remove text-flavored naming):

- **`Iso` invariant, made a field — and it now holds *unconditionally*.** The
  paper §3.1 states the inverse invariant in prose and admits it is unchecked;
  §7.5 notes in passing that it "would be interesting to see" it encoded in a
  dependently typed language. We answer: `Iso.law` is a **field**, so an `Iso`
  without its proof cannot be built, and the roundtrip is a **closed
  theorem** over `Codec`. Crucially, because departure #4 removes the
  lossy `ignore` primitive, the strict law
  `∀ a b, apply a = some b ↔ unapply b = some a` holds for **every** core
  combinator — there is no residual "modulo equivalence classes" escape hatch.
  (The paper's lossy combinators would need a *coarser* law; we simply do not
  have them.)
- **Naming made format-agnostic.** `Syntax`/`parse`/`print`/`token` are the
  paper's text vocabulary (its §1 says concrete syntax is "sequences of
  characters"; its §3.4 says `token` "relates each **character** with itself").
  On bytes those names mislead, so we use `Codec`/`decode`/`encode`/`byte`. This
  is a rename, not a semantic change.
- **A format-agnostic core with zero *domain-specific* leaf codecs.** A *scope*
  decision: the only primitive descriptions in core are `byte` and `pure`;
  nothing in `Iso`/`Codec`/`Rel` mentions `u8`, `varint`, or `utf8`, so we ship
  none and put every concrete format downstream (`lean-binary`, `lean-text`).
  Separation of concerns, not a claim of forced necessity.

Everything else is **kept**, and kept strongly: `Rel` is preserved as the
*specification* (decoding is the paper's full relation; no narrowing layered on
top of it), and partial encoding is preserved.

______________________________________________________________________

## Departure #5, resolved: the committed-choice detour and its reversal

This departure is **closed**. The committed-choice `|` (and the
prefix-disjointness machinery it required — `NonNull`, `PrefixDisjoint`,
`Disjoint`, `Unambiguous`, and the prefix trichotomy) was a consequence of
attempting a deterministic single-result decoder for speed. We discovered,
over several sessions, that committed `|` is *incompatible* with the paper's
`|` and `many`:

  * `decode (nil $ pure ()) s` always succeeds consuming 0 bytes, so a
    committed `many p = nil | cons $ p * many p` always returns `[]` and never
    reaches `cons`.
  * even reordered, `nil` and `cons` are never prefix-disjoint, because `[]`
    is a proper prefix of every non-empty string — so no prefix condition can
    gate repetition, regardless of `NonNull p`.

Both facts were proved in the process (`ProperPrefix [] s ↔ s ≠ []`), showing
the *approach* was unsound, not merely unfinished. The fix was to **restore the
paper's semantics** (departure #2/#3): `decode : Codec α → List UInt8 →
List (α × List UInt8)` with `|` as list concatenation. Then `Rel (d₁ | d₂) =
Rel d₁ ∨ Rel d₂` and `decode` agree by construction, the laws became
unconditional, and the entire prefix-disjointness section was deleted.

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

The list combinators built *on* `many` — `sepBy`/`sepBy1`, `chainl1`/`chainr1` —
are likewise re-derived as relations, decoders, and encoders (over
`relRepeat`/`decodeRepeat`/`encodeRepeat`, keeping `Iso.foldl`/`Iso.foldr`
unchanged), each with an unconditional `_spec` (bidirectional) and `_rel`
(encoder-soundness) law; productivity appears only as the decoder's `hsep`
argument.

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
