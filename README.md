# codec

A verified, bidirectional codec library for Lean 4.

One *description* gives two directions: a **decoder** (bytes → value) and an
**encoder** (value → bytes), provably inverse to each other. `codec` takes the
idea from Rendel & Ostermann's *Invertible Syntax Descriptions: Unifying Parsing
and Pretty Printing* (Haskell Symposium 2010) and carries it further in Lean:
**more dependently typed, more provable, and binary.**

## TL;DR

The paper's core idea — one specification drives both parsing and printing
because every building block is a *partial isomorphism* whose two directions are
each other's inverse — is the whole design. `codec` makes three moves on top of
it:

- **Prove it, don't assert it.** The inverse law is a *field* of `Iso`: you
  literally cannot construct an isomorphism without its proof. The roundtrip
  (`encode` then `decode` reproduces the value, byte-for-byte) is a closed
  theorem, holding **unconditionally** for every description.
- **Rest on bytes, not characters.** The concrete syntax is a byte sequence
  (`UInt8`), so the framework covers fixed-width integers, endianness, images,
  and LEB128 — and text is rebuilt downstream, on top of bytes.
- **Keep the full semantics.** The decoder returns *all* `(value, remainder)`
  pairs and `|` is the paper's backtracking union. No committed choice, no
  "unambiguous grammar" caveat — the laws hold for every description, exactly
  because the semantics were kept faithful.

That is the summary. The rest of this file gives context and pointers; the
**proofs** live in the code (`Codec/*.lean`, each declaration documented in
place), and the **full design rationale** lives in
`openspec/changes/invertible-binary-core/`.

## From the paper to a binary codec

The paper is the *foundation*, not a spec to transcribe. The canonical record of
every place `codec` differs from it (or completes it) is anchored below as
`[D#]` (a **departure** — an observable-semantics change) and `[S#]` (a
**strengthening** — no semantics change, but the paper left it unfinished).
These anchors are cross-referenced from the code and the design docs.

### Departures

| | Departure | In brief |
|---|---|---|
| **[D1]** | `String`/`Char` → bytes | The base unit is `UInt8`, the base string a byte sequence; text is rebuilt on top. |
| **[D2]** | Nondeterministic decoder *kept* | `decode` returns *all* `(value, remainder)` pairs (the paper's list decoder), not a single committed result. |
| **[D3]** | `\|` is backtracking union | `decode (d₁ \| d₂) s = decode d₁ s ++ decode d₂ s`, matching `Rel (d₁ \| d₂) = Rel d₁ ∨ Rel d₂`. |
| **[D4]** | Lossless capture | No `ignore`: allowable bytes are *kept* as part of the value and re-emitted verbatim, so no "modulo equivalence classes" hedge. |
| **[D5]** | No prefix-disjointness gate | A *removed* departure — backtracking `\|` needs none, and none can work for repetition. |
| **[D6]** | `Codec` is an inductive AST | Descriptions are ordinary values you can structurally recurse over, not a §3.4 typeclass. |
| **[D7]** | `iterate` omitted | Its forward/backward fixpoints need not agree, so no field law exists; `foldl`/`foldr` are defined directly. |
| **[D8]** | `Decidable` witnesses | `pure`/`element`/`subset` carry `[DecidableEq]/[DecidablePred]`, the proof-backed form of the paper's `Eq`/`Bool`. |

`encode` being *partial* (`Option`) is **not** a departure — it is the paper's
`Maybe` printer kept as-is.

### Strengthenings

| | Strengthening | In brief |
|---|---|---|
| **[S1]** | `Iso.law` is a field | The inverse invariant is type-enforced and holds unconditionally. |
| **[S2]** | Format-agnostic names | `Codec`/`decode`/`encode`/`byte` instead of the text-world `Syntax`/`parse`/`print`/`token`. |
| **[S3]** | Zero leaf codecs in core | Only `byte`/`pure` primitives; concrete formats ship downstream. |
| **[S4]** | `foldl`/`foldr` are fresh | Well-founded (not `inverse ∘ foldl ∘ inverse`, which is type-incoherent), with a termination witness. |
| **[S5]** | Least-fixpoint *proved* | `relRepeat_induction` makes "repetition is the least fixpoint" a theorem, not a claim. |
| **[S6]** | Unbounded `many` is semantic | Repetition is `relRepeat`/`decodeRepeat`/`encodeRepeat`, not a (proof-opaque) `Codec` node. |

The per-item reasoning — *why* each choice, in lay terms, for a reader who does
not write Lean — is in `openspec/changes/invertible-binary-core/` (the
"departures & strengthenings" sections) and is what a porter should read before
reproducing any of it.

## What it is, in one picture

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

The precise types, the denotational relation `Rel`, the repetition split
(`relRepeat`/`decodeRepeat`/`encodeRepeat`), and all the laws are defined and
documented in `Codec/*.lean` — the above is the shape, not the full API.

## Scope

- **`codec`** (this package): the pure framework — `Iso`, `Codec`, `Rel`, the
  interpreters, and the laws. **No domain-specific leaf codecs** (not even `u8`;
  the primitives are `byte` and `pure`).
- **`lean-binary`** (downstream): `u8`, `u16le`/`u16be`, … , `varint`,
  `lengthPrefix`, image/Protobuf demos, and the speed benchmark.
- **`lean-text`** (downstream): `utf8` plus `text`/`identifier`/`whitespace` —
  the paper's §6 text domain, re-based on bytes.

## Status

The core is implemented and proven: zero `sorry`, zero warnings, and every law
closed with only the two standard axioms (`propext`, `Quot.sound`) in the
footprint. `iterate` is deliberately omitted (`[D7]`); unbounded `many` is
semantic (`[S6]`); the `chainl1`/`chainr1` family is fully computable (extractable).

Still open (see the task ledger `openspec/changes/invertible-binary-core/tasks.md`,
§11): the extraction + benchmark, and the efficiency spike (the paper's own §4.4
open problem). Neither changes the semantics — the proofs above already hold.

## Building

The toolchain (Lean 4 + the `openspec` CLI) comes from the Nix flake:

```bash
nix develop      # enter the dev shell
lake build       # compile + verify (the proof gate)
```
