# Design

## Context

See `proposal.md` — Why. `codec` is a verified `Bytes n` substrate; `fstar-basen`
is the proven reference for four bases. The Lean package is a _re-derivation_ of
those four (Base08/16/32/64) plus three _new_ bases (2/4/10) we define ourselves.
The package is pure Lean (no C seam), stdlib-only, `[propext, Quot.sound]`-only.

## Goals / Non-Goals

**Goals:**

- `lean-basen` (package `basen`, module namespace `BaseN`) depending only on
  `codec`, initialized from `lean-nix-flake-template`.
- Seven bases, each with `encode`/`decode` + a proved roundtrip law.

**Non-Goals:**

- No `String`/`Char` substrate (all ASCII alphabet via `UInt8` bytes).
- No `vbin`/`text`/`proto` dependency.
- No per-format C, no `@[extern]` seam, no `Classical.choice`/`sorry`.

## Decisions

### D1 — Namespace `BaseN`, package `basen`, repo `lean-basen`

Matching the `ecosystem` spec's prefix-drop rule and the F* `fstar-basen` → `basen` /
`Data.BaseN` convention. The Lean namespace is `BaseN` (capital `N`), matching
the F* `Data.BaseN` rather than the English-plural-looking `Basen`. Module
layout: `BaseN.Base2`, `BaseN.Base4`, `BaseN.Base8`, `BaseN.Base10`,
`BaseN.Base16`, `BaseN.Base32`, `BaseN.Base64`, plus a `BaseN` facade re-exporting
them (mirroring `fstar-basen`'s `Data.BaseN.fst`).

> **SUPERSEDED (facade only).** The facade shipped as **module re-exports only**
> — no `Base` inductive and no dispatcher; see D4 below and `tasks.md` 4.1. The
> namespace / module layout decided here is unchanged.

### D2 — Substrate is the `codec` `Bytes n`, surface is `Codec` values

Each base is a `codec` `Codec` value over the `Bytes n := Fin n → UInt8`
substrate, **not** a bespoke `encode : List UInt8 → List UInt8` / `decode :
List UInt8 → Option (List UInt8)` function. The fixed-width bases (2/4/8/10/16)
have element `Codec UInt8` (one byte per element); the block bases (32/64) have
element `Codec (List UInt8)` (a 5-byte / 3-byte block). The run triple is
`decode{X} = decodeRepeat {x}Elem {x}ConsumesByte` / `encode{X} = encodeRepeat
{x}Elem` / `rel{X} = relRepeat (Rel {x}Elem)`, and the whole-input decoder is
`Codec.decodeFull {x}Elem {x}ConsumesByte`. (An earlier phase used bespoke
`encode`/`decode` over `List UInt8`; that was superseded by
`basen-uniform-leaf-api`, archived.)

### D3 — Port the four RFC 4648 bases verbatim, then add 2/4/10

Base08 (octal, 3 digits/byte), Base16 (hex, uppercase, no padding), Base32
(`A-Z2-7`, `=` padding), Base64 (`A-Za-z0-9+/`, `=` padding) are ported from
`fstar-basen` lemmas (`nibble_roundtrip`, `encode_single`, append-distribution,
single-byte, full roundtrip). Base2 (8 bits, `0`/`1`), Base4 (quartets,
`0-3`), and Base10 (decimal digits, the boxed-arithmetic hot spot) are defined
here: bit/quartet/nibble-style digit extraction for 2/4, and repeated `÷10`/`%10`
digit math for 10.

### D4 — One inherited roundtrip law per base, plus a facade

> **SUPERSEDED (the facade half).** As built and shipped, `BaseN` re-exports the
> seven modules as **modules only**: there is no `Base` inductive, no
> `BaseN.roundtrip` and no `encode (b : Base)` / `decode (b : Base)` dispatcher.
> Each base is its own `Codec` value decoded/encoded by the uniform
> `Codec.decodeFull` / `encodeB{32,64}`, so the radix lives in the value the
> caller holds rather than in a dispatch index. See `tasks.md` 4.1 (and the
> 5.x finding at `tasks.md` 119–120, which records that the stale `Base`-enum
> bullet described a facade that does not exist). The **inherited roundtrip law**
> half of this decision is unchanged and is what shipped.

Each `BaseN.BaseX` proves `roundtrip (bs) : decodeFull {x}Elem {x}ConsumesByte
(encode{X} bs) = some bs` (inherited from `decodeRepeat_spec`/`encodeRepeat_rel`;
no bespoke proof per base). The facade `BaseN` re-exports the seven modules and
an inductive `Base := B2 | B4 | B8 | B10 | B16 | B32 | B64`. Known vectors are
`example … := rfl`-checked in a bench lane (RFC 4648 §10 for 16/32/64; hand
vectors for 2/4/8/10) at the block-`iso` `unapply` direction.

### D5 — Build shape mirrors the template + codec

`lakefile.lean` (`package basen`, `lean_lib basen` with `roots := #[`BaseN]`),
`flake.nix`/`default.nix`with`native`/`check`targets,`require codec from git`
injected as a flake input (`codec-src`+`codec-native` `.olean`artifacts) per
the`ecosystem`dependency-injection convention.  (No`bench`/`cli` executable
yet — the bench lane is task 4.2.)

> **SUPERSEDED (last sentence only).** The `bench` executable did land — it is
> task 4.2, and `packages.bench` runs it (`installPhase` executes the binary, so
> `nix build '.#bench'` verifies the vectors rather than merely producing one).
> The build shape decided here is unchanged.

### D6 — Base10 is three zero-padded decimal digits per byte (RESOLVED this

session)

The design's open question (variable-width decimal vs. byte-oriented) is
resolved in favor of **three zero-padded decimal digits per byte**, MSB-first
(`v/100`, `(v/10)%10`, `v%10`), decoding rejects a triple `> 255`. This is the
only "byte-oriented, no sign" reading that makes `decode (encode bs) = some bs`
hold unconditionally: a variable-width decimal (the whole byte list as one
big-endian number) drops leading zero bytes, and a per-byte _variable_-width
decimal (`12` = `1``2` vs. `12`) is ambiguous. The fixed 3-digit width is
bijective per byte, mirroring base8's 3-octal-digits-per-byte.

## Risks / Trade-offs

- **[Base10 digit math is the boxed-arithmetic hot spot]** → accepted pure-Lean
  (~20–40× off C); it is a parsing primitive, not a bulk seam; the proof (not the
  speed) is the gate.
- **[Base2/4 "base-N" is over-specified — 1 byte ↔ 8 bits/4 quartets]** → define
  bit order MSB-first and no padding in the spec; base2 = 8 chars/byte, base4 =
  4 chars/byte.
- **[`decode` rejects vs. leniently skips malformed input]** → `Option`, reject on
  any bad byte or wrong arity (matching `fstar-basen`).
- **[Facade `Base` dispatch adds a layer between the per-base lemmas]** → keep it
  thin (one `match`), prove it by cases; the per-base lemmas are the real proofs.
  **SUPERSEDED:** the dispatch layer was not built at all (`tasks.md` 4.1), so
  this risk was retired rather than mitigated.

## Migration Plan

1. `git init` `lean-basen` from `lean-nix-flake-template`; rename to
   `basen`/`BaseN`; wire `require codec from git` (flake input injection); verify
   `lake build`.
2. Port Base16 (smallest) end-to-end first as the pattern: alphabet + encoder +
   decoder + roundtrip + vectors; then Base08, Base32, Base64.
3. Add Base2, Base4, Base10 with their own spec-defined digit math.
4. Add the `BaseN` facade + `Base` dispatch + a bench lane (vectors + roundtrip).
   **SUPERSEDED (the dispatch half):** shipped as module re-exports only
   (`tasks.md` 4.1); the bench lane landed as 4.2.
5. Gate: `lake build` zero `sorry`/warnings, `#print axioms` = `[propext,
Quot.sound]`, `nix flake check` green.

## Open Questions

- ~~Whether base10 needs a leading-`-`/sign convention~~ — **RESOLVED** (D6):
  three zero-padded decimal digits per byte, no sign. A sign convention for
  arbitrary-precision integers is out of scope for a byte-oriented codec.

## Next session (re-anchored, 2026-10-20): Codec-value rewrite is DONE

This change's bespoke-surface phase is **closed**. All seven bases were
re-expressed as `Codec` values by `basen-uniform-leaf-api` (archived;
lean-basen commits `7eefebc`…`bef44ae`), and the facade + bench were rewired to
the Codec-value surface (`bef44ae`). (The "facade" here means the `BaseN`
**re-export module**, not a `Base` dispatch — that was never built; see D4.) `lake build` is green, zero
`sorry`/warnings, `#print axioms` on every per-base `roundtrip` =
`[propext, Quot.sound]`, and `nix flake check` is green (codec is a public
`github:dysinger/lean-codec` flake input; `flake.lock` pins `77c1c54`, not the
stale `88e4c36` — see `bef44ae`).

**Status update (2026-11-05): there is no remaining work, and no other active
change.** The RFC-conformance work this paragraph used to defer to was landed by
`basen-rfc-conformance-theorems` (archived 2026-10-27), which subsumed the
bespoke-surface review findings 5.1 (non-terminal padding) / 5.7 (smoke
coverage) / 5.10 (base16 lowercase). All 36 tasks of this change are closed and
it is ready to archive; see `tasks.md` §5 for which review findings were
superseded rather than re-derived here.
