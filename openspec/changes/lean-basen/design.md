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

### D2 — Substrate is `List UInt8`, mirroring the `codec` element type

Each `encode : List UInt8 → List UInt8` and `decode : List UInt8 →
Option (List UInt8)`. This keeps `basen` directly composable with `codec`'s
`Bytes n` (whose element type is `UInt8`), without forcing `basen` to depend on
`codec`'s _length-indexed_ wrapper for its own surface — the plain `List UInt8` is
the transport, and a `codec` consumer lifts it. (Rationale: `fstar-basen` itself
works over `list UInt8` and only _imports_ `Data.Codec.Types` for the `byte` alias;
we do the same.)

### D3 — Port the four RFC 4648 bases verbatim, then add 2/4/10

Base08 (octal, 3 digits/byte), Base16 (hex, uppercase, no padding), Base32
(`A-Z2-7`, `=` padding), Base64 (`A-Za-z0-9+/`, `=` padding) are ported from
`fstar-basen` lemmas (`nibble_roundtrip`, `encode_single`, append-distribution,
single-byte, full roundtrip). Base2 (8 bits, `0`/`1`), Base4 (quartets,
`0-3`), and Base10 (decimal digits, the boxed-arithmetic hot spot) are defined
here: bit/quartet/nibble-style digit extraction for 2/4, and repeated `÷10`/`%10`
digit math for 10.

### D4 — One roundtrip law per base, plus a facade aggregator

Each `BaseN.BaseX` proves `lemma_baseX_roundtrip : decode (encode bs) = some bs`.
The facade `BaseN` proves a single `roundtrip (b : Base) (bs : List UInt8)` over a
small inductive `Base := B2 | B4 | B8 | B10 | B16 | B32 | B64` dispatching to the
per-base lemma. Known vectors are `#eval`-checked in a bench lane (RFC 4648 §10
for 16/32/64; hand vectors for 2/4/8/10).

### D5 — Build shape mirrors the template + codec

`lakefile.lean` (`package basen`, `lean_lib basen` with `roots := #[`BaseN]`),
`flake.nix`/`default.nix`with`native`/`check`targets,`require codec from git`
injected as a flake input (`codec-src`+`codec-native` `.olean`artifacts) per
the`ecosystem`dependency-injection convention.  (No`bench`/`cli` executable
yet — the bench lane is task 4.2.)

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

## Migration Plan

1. `git init` `lean-basen` from `lean-nix-flake-template`; rename to
   `basen`/`BaseN`; wire `require codec from git` (flake input injection); verify
   `lake build`.
2. Port Base16 (smallest) end-to-end first as the pattern: alphabet + encoder +
   decoder + roundtrip + vectors; then Base08, Base32, Base64.
3. Add Base2, Base4, Base10 with their own spec-defined digit math.
4. Add the `BaseN` facade + `Base` dispatch + a bench lane (vectors + roundtrip).
5. Gate: `lake build` zero `sorry`/warnings, `#print axioms` = `[propext,
Quot.sound]`, `nix flake check` green.

## Open Questions

- ~~Whether base10 needs a leading-`-`/sign convention~~ — **RESOLVED** (D6):
  three zero-padded decimal digits per byte, no sign. A sign convention for
  arbitrary-precision integers is out of scope for a byte-oriented codec.

## Next session (2026-10-19): Base32, Base64, then facade + bench + gate

Five of seven bases are landed and proven (`[propext, Quot.sound]`-only, zero
`sorry`): Base16 (§8), Base8, Base10, Base2, Base4. The remaining `lean-basen`
work, in order:

1. **Base64 (task 2.4)** — the RFC-faithful `encodeN`/`decodeN` definitions, the
   alphabet bijection (`b64ToVal ∘ valToB64 = id`), and the byte-extraction
   identities (F* `lemma_b64_byte0..2`) were written this session and are
   `omega`-provable; what remained is the `decodeN_triple`/`single`/`pair` and
   `roundtripN` final steps (the `simp [encodeN, decodeN]` over-reduction produced
   an `omega`-unfriendly goal) plus the `UInt8` surface. Resume there. The
   proven technique for the 4-range alphabet bijection: prove
   `valToB64_not_pad` via `exact decide_eq_false_iff_not.mpr (by omega)` after
   `by_cases` on each range, and close the `62`/`63` tail with
   `rcases (show i = 62 ∨ i = 63 by omega) with rfl | rfl <;> decide`. For the
   decode roundtrip, drive the proof with `rw`-chains (not `simp [decodeN]`, which
   splits the `&&`/`if` into `true = true ∧ …` residue) and finish with `omega` on
   the reduced byte-extraction forms.

2. **Base32 (task 2.3)** — same 5-bit cross-byte bit-slicing as base64 but 5-bytes
   → 8-chars and five pad cases (pad_count 0/1/3/4/6); port `fstar-basen`
   `Data.BaseN.Base32` verbatim (its `decode_base32_group` + `b32_val`), prove the
   `lemma_b32_byte0..4` extraction identities with `omega` (like `byte0..2`), and
   apply the same `by_cases`-per-range alphabet technique over the `A-Z2-7` alphabet.

3. **Facade (task 4.1)** — un-comment `BaseN.Base32`/`BaseN.Base64` imports,
   restore `B32`/`B64` to the `Base` inductive (currently scoped to
   B2/B4/B8/B10/B16), and extend `BaseN.roundtrip`'s `cases`.

4. **Bench lane (task 4.2)** — value-check each base byte-for-byte against RFC
   4648 §10 (16/32/64) and hand vectors (2/4/8/10); the vectors are pinned in
   `rfc4648.md`.

5. **Gate (task 4.3)** — `lake build` zero `sorry`/warnings; `#print axioms` on
   `BaseN.roundtrip` and each `lemma_baseX_roundtrip` = `[propext, Quot.sound]`;
   `nix flake check` green; commit + push `lean-basen`.
