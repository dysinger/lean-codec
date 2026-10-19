# Tasks

> ## Next step (2026-10-19, session) — 3.2/3.3/3.4/3.5 DONE; REMAINING 3.6/3.7 + 4.x
>
> **This session landed (committed in `../lean-basen`):** tasks 3.2 (Base2), 3.3
> (Base4), 3.5 (Base16), 3.4 (Base10) are each re-expressed as `Codec (List
UInt8)` values over `satisfy`/`count`/`iso` + the productive repetition triple,
> deleting the bespoke `encode`/`decode`. All `roundtrip`/`_unambiguous` laws
> `#print axioms` ⇒ `[propext, Quot.sound]`, zero `sorry`/warnings, `lake build
BaseN.Base{2,4,10,16}` green. Commits `78a954f` (Base2/4/16 + Common) and
> `974fd90` (Base10).
>
> **New shared module `BaseN/Common.lean`** factors the generic lemmas each base
> was otherwise going to re-derive verbatim:
> `Productive_iso`/`Productive_seq_left`/`Productive_count_succ`/`Productive_satisfy`,
> `Productive_count_satisfy_succ`, `Unambiguous_satisfy`, `Rel_count_satisfy_len`,
> `count_satisfy_unambiguous`, `Unambiguous_iso`. Base2/4/10/16 all `open
BaseN.Common` and reuse these; Base8 still has its own copies (done/committed
> before Common existed — do not churn it).
>
> **The remaining hard work (3.6/3.7) is now precisely diagnosed:** the fixed-width
> bases have element `Codec UInt8` (one byte per element), so `iso blockIso (count
k (satisfy digit))` has a clean bijective block `Iso`. Base32/64 are
> cross-byte bit-packing (5 bytes = 40 bits = 8 five-bit chars; 3 bytes = 24 bits
> = 4 six-bit chars), so the element is `Codec (List UInt8)` (5/3 bytes) via `iso
blockIso (count 8 (satisfy b32OrPad))`. The block `Iso.law` needs **both**
> directions:
>
> - **forward** `unapply bs = cs → apply cs = bs` — proven, reuses the existing
>   `byte0`..`byte4` extraction identities (base32) / the base64 analogue.
> - **backward** `apply cs = bs → unapply bs = cs` — **encode-injectivity /
>   char reconstruction**: recover each `cᵢ = valToB32(σᵢ(bs))` from the bytes.
>   This is genuinely NEW work: the existing code only proves `decode ∘ encode
= id` (`decodeN (encodeN bs) = some bs`), never `encode ∘ decode = id` on
>   valid input, which is exactly the `Iso.law` backward direction.
>
> **How to finish it (do NOT reach for bespoke, do NOT use `by_contra`/`Classical`/
> `sorry`):** prove per-shape reconstruction by `by_cases` on each `cᵢ = 61` and
> `b32Valid cᵢ` condition in `apply`, closing impossible branches with `simp at
h` + `omega`; recover each `b32ToVal cᵢ` from the byte identities read in
> reverse; then apply a `char_eq_valToB32_of_valid` lemma (`c.toNat = valToB32 i`
> when valid and `b32ToVal c.toNat = i`). Shapes: base32 = 1/2/3/4/5-byte tails
> (5 lemmas), base64 = 1/2/3-byte tails (3 lemmas). Then 4.1 facade (delete the
> `Base8.encode`/`decode` refs, rewire to the `*Elem`/`decode*`/`encode*`/`roundtrip`
> triple per base), 4.2 bench (`Codec.decode`/`decodeRepeat` per base; byte-exact
> vectors still `rfl`), 4.3 gate (`nix flake check` green).

> ## Next step (2026-10-19, end of session) — FINISH 3.1, THEN REPLICATE
>
> **Session just landed (committed):** `octBlockIso.law` for Base8 is PROVED and
> clean (`c97fec0` in `../lean-basen`; `1a0df55` in this repo). `lake build
BaseN.Base8` is green, zero `sorry`/warnings. The `Codec`-value rewrite of
> `BaseN/Base8.lean` is in place: `octDigit`, `octBlockApply`/`octBlockUnapply` + a
> **separate `octBlockIso_law` theorem** (the fix for the old inline-`law` friction),
> `octToVal_ofNat_valToOct`, `oct_decompose_unique`, `oct_sum_eq`, generic
> `Productive_iso`/`Productive_seq_left`/`Productive_count_succ`/
> `Productive_count_satisfy_succ`, `octElem`, `octConsumesByte`,
> `decodeOct`/`encodeOct`/`relOct`.
>
> **Remaining for 3.1 (in dependency order):**
>
> 1. `octElem_unambiguous : Unambiguous octElem` — not yet done. `Rel (iso i d) x s
↔ ∃ a, i.apply a = some x ∧ Rel d a s`; `count 3 (satisfy p)` reads a _fixed_
>    3-byte prefix of `s`, so `Rel (count 3 …) a s` and `… b s` pin `a = b` (prove
>    `count k (satisfy p)` unambiguous by induction on `k` via `Rel_satisfy` + the
>    prefix is the single byte `s ⟨0, ·⟩`); then `octBlockIso.apply a = some x` and
>    `.apply a = some y` give `x = y` by `Option.some.inj`. **Extract `Rel_seq`'s
>    split first** (`m = 1` from `Rel_satisfy`'s `∃ h : n = 1`) before `simp`
>    consumes the witnesses — see the skill note on extracting conjuncts first.
>    (A previous attempt got stuck exactly here and left a `sorry` — reverted.)
> 2. `relOct_unambiguous : relUnambiguous (Rel octElem)` — induction on the list via
>    `relRepeat_cons` + `octElem_unambiguous` at the head + IH at the tail.
> 3. `roundtrip (bs) : Option.bind (encodeOct bs) (fun ⟨n,s⟩ => decodeFull octElem
octConsumesByte n s) = some bs` — via `encodeRepeat_rel` → `decodeRepeat_spec`
>    full-consumption → `decodeFull_ne_none` → `decodeFull_spec` (needs the `huniq`
>    = `relOct_unambiguous`). This is the inherited-roundtrip law.
> 4. (Optional, only if the facade will expose `List`-level) thread `BaseN.Bridge`
>    `decodeAll`/`encodeAll` to state the `List UInt8 → Option (List UInt8)` roundtrip.
>
> **Then replicate the identical pattern** (each base needs its own block `Iso` law +
> digit-uniqueness + productivity + unambiguous + roundtrip):
>
> - **3.2 Base2** (`count 8 (satisfy bitChar)` + `bitsVal`/`bitsOf` iso, MSB-first)
> - **3.3 Base4** (mirror Base8, 4 quartets/byte)
> - **3.5 Base16** (`count 2 (satisfy hexChar)` + pair/byte iso; DELETE bespoke
>   `encode`/`decode`)
> - **3.4 Base10** (variable-width: `takeWhile isDigit` run + block `iso`, no pad)
> - **3.6/3.7 Base32/Base64** (alphabet run + block iso + terminal-`=` pad `alt`
>   preserving 5.1 `rest = []`)
>
> **Then 4.1 (facade) — currently BROKEN:** `BaseN.lean`/`Bench.lean` still call the
> deleted bespoke `Base8.encode`/`decode`/`roundtrip`; full `lake build` is red until
> all seven bases rewire. 4.2 bench, 4.3 gate (`nix flake check`).

---

> **Checkpoint (2026-10-19, late):** parts 1–2 (`satisfy` + `takeWhile`) and 3.0
> (`BaseN.Bridge`) are done. **Task 3.1's hard proof (`octBlockIso.law`) is now
> PROVED and compiling clean** — the `Codec`-value Base8 is landed in
> `../lean-basen/BaseN/Base8.lean` (`octDigit`, `octBlockApply`/`octBlockUnapply`
> with `octBlockIso_law`, `octElem : Codec UInt8`, `octConsumesByte`,
> `decodeOct`/`encodeOct`/`relOct` run triple), zero `sorry`/warnings on
> `lake build BaseN.Base8`. The key lemmas that closed the prior friction: a
> total `octBlockApply`/`octBlockUnapply` pair with a _separate_ `octBlockIso_law`
> theorem (not an inline structure `law`), `octToVal_ofNat_valToOct`,
> `oct_decompose_unique` (division via `congrArg` on `/64` then `%64/8`),
> `oct_sum_eq` (`Nat.div_add_mod` + `omega`), and generic `Productive_iso`/
> `Productive_seq_left`/`Productive_count_succ` lemmas for the `ConsumesByte`
> witness. The `octConsumesByte` proof goes through
> `productive_iff_consumesByte` rather than a `count 3`-level `decode` induction.
>
> **Still open for 3.1 (do not mark done yet):** the _roundtrip_ theorem (the
> `decodeFull`-level law `decode (encode bs) = some bs`), which needs the
> uniqueness hypothesis (`Unambiguous octElem`) threaded through
> `encodeRepeat_rel` + `decodeRepeat_spec` + `decodeFull_spec`. This is the next
> proof. The **facade `BaseN.lean`/`Bench.lean` are still on the old bespoke
> `Base8.encode`/`decode` surface**, so `lake build` (full) is currently broken
> until tasks 3.2–4.1 rewire all seven bases and the facade.

## 1. Core: add `satisfy`

- [x] 1.1 Add constructor `satisfy : (UInt8 → Bool) → Codec UInt8` to
      `Codec/Codec.lean`.
- [x] 1.2 Add the `Rel`/`decode`/`decodeFast`/`encode` cases for `satisfy`
      (`Rel (satisfy p) b s = p b = true ∧ s = single b`; decode one byte iff
      `p b` else `[]`; encode iff `p b` `some ⟨1, single b⟩` else `none`).
- [x] 1.3 Extend the `Sound` laws (`decode_spec`, `bidir`, `roundtrip`,
      `encode_rel`) with the `satisfy` case; `[propext, Quot.sound]`-only, zero
      `sorry`. Gate `lake build` + `#print axioms Codec.roundtrip`.

## 2. Derived run combinator

- [x] 2.1 Add `takeWhile p` / `many (satisfy p)` as a derived combinator using
      `decodeRepeat`/`encodeRepeat` (no new constructor), for alphabet runs and
      variable-length tokens (varint, UTF-8).

## 3. `basen` bases composed from `satisfy`/`count`/`iso` + the proven repetition layer

> **Note (2026-10-19):** tasks 3.x/4.x do **not** require a `many` constructor.
> The variable-width run primitive is `takeWhile p` (the already-landed
> `satisfy_many0` analogue), and `many` stays out of the AST — per the paper
> (§3.4: `many` is a derived combinator) and the F* reference (`satisfy_many0`
> scans the finite input, no `Productive` witness). See the design supersede.
>
> **Shape per base (fixed-width):** an _element_ `Codec UInt8 := iso <blockIso>
(count k (satisfy <digitPred>))` — `k` digits → one byte — plus the unbounded
> **run** triple `relBase := relRepeat (Rel elem)`, `decodeBase := decodeRepeat
elem <consumeWitness>`, `encodeBase := encodeRepeat elem`; the roundtrip is the
> **inherited** `decodeRepeat_spec`/`encodeRepeat_rel` law. `elem`'s productivity
> witness is one `ConsumesByte` proof (each step consumes exactly `k` bytes).
>
> **Boundary:** the `Bytes n ↔ List UInt8` bridge is `BaseN.Bridge` (landed).

- [x] 3.0 Add the `BaseN.Bridge` `Bytes n ↔ List UInt8` module (landed).
- [x] 3.1 **Base8** (simplest fixed-width: 3 octal digits/byte) — establish the
      template: `octElem : Codec UInt8` (3-char `iso`+`count`), `octConsumesByte`,
      run triple, `roundtrip` inherited. `lake build` green.
- [x] 3.2 **Base2** (8 bits/byte) — `count 8 (satisfy bitChar)` + `bitsVal`/`bitsOf`
      `iso`; run triple; roundtrip inherited. Delete bespoke `encode`/`decode`.
- [x] 3.3 **Base4** (4 quartets/byte) — mirror Base8 with 4 chars/byte.
- [x] 3.4 **Base10** (decimal digits/byte, variable width but byte-oriented) —
      `satisfy isDigit` run + block `iso` (no `=` padding).
- [x] 3.5 **Base16** (2 hex digits/byte) — `count 2 (satisfy isHexDigit)` + pair/byte
      `iso`; run triple; roundtrip inherited. Delete bespoke `encode`/`decode`.
- [ ] 3.6 **Base32** (5-bit alphabet, `=` padding) — alphabet run + block `iso` +
      terminal-pad `alt` preserving 5.1 (`rest = []`).
- [ ] 3.7 **Base64** (6-bit alphabet, `=` padding) — same as Base32 with 64-alphabet.

## 4. Facade + bench + gate

- [ ] 4.1 `BaseN.lean` facade re-exports the seven `Codec` values / run triples.
- [ ] 4.2 `Bench.lean` calls `Codec.decode`/`decodeRepeat` per base; byte-exact
      vectors still `rfl`.
- [ ] 4.3 `lake build` zero `sorry`/warnings; `#print axioms` `[propext,
Quot.sound]` for every law; `nix flake check` green; commit + push.

## Non-Goals (permanent)

- No BE/LE/fixed-width/`varint`/text/tagged-`sum`/lookahead in core; no
  `decode`/`encode` result-shape change; no error-position type.
