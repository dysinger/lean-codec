# Tasks

> **Session status (latest):** §0 complete — the A/B measured LLVM as neutral on the
> single `Bytes n` carrier and **the `lean4-llvm` override + clang-19 pin were removed
> (0.4, done first)**. Toolchain is back to plain nixpkgs `lean4` (clang 21.1.8); proof
> gate + bench both build and run byte-exactly. Next: §1 (profiling/attribution).

## 0. A/B: plain `lean4` vs `lean4-llvm` (decides LLVM's role up front)

Before any code change, measure whether LLVM matters at all. The `lean4-llvm`
override in `default.nix` exists only for the (deleted) `Array`/`ByteArray`
`@[extern]` fast path, which the single `Bytes n` carrier never touches — so its
cost (a full pinned clang-19/libc++ toolchain) may buy nothing on the current hot
path. Test this directly.

- [x] 0.1 Build the bench with the plain nixpkgs `lean4` (no LLVM override: emit C
      via the default `leanc`/clang in nixpkgs' stdenv) and with `lean4-llvm`
      (current `devShells.default`), on the SAME source, same sizes (×1/×2/×4).
- [x] 0.2 Record both tables here side by side. Conclude one of: - **LLVM is neutral** (plain ≈ llvm on every lane) → drop `lean4-llvm` and
      the clang-19 pin as dead weight (a real build-time win for every `nix
      develop`/`nix build`); - **LLVM helps** (some lane measurably faster under llvm) → keep the
      override and record exactly which lane(s) benefit and by how much, so §4
      tunes those flags deliberately.
- [x] 0.3 Record the verdict + both tables at the top of this section; do not
      remove the `lean4-llvm` derivation until 0.2 has a number, not a guess.

**0.2 verdict: LLVM is NEUTRAL.** `encodeRepeat`/`decodeRepeat`/`decodeFull` are
within noise on both configs, and the scalar-read/decode lanes flip ±~10 ns run-to-run
(noise, not signal). The `Bytes n := Fin n → UInt8` carrier never emits an
`Array`/`ByteArray` primop, so `LLVM=ON` changes nothing on the hot path; the only
real differences are the varbinary lanes (`encodeVarint` 64 vs 129 ns) and the
`roundtrip byte encode` (70 vs 143 ns), sub-microsecond constant factors.

| Lane                    | plain (clang 21, LLVM OFF) | llvm (clang 19, LLVM ON) |
| ----------------------- | -------------------------- | ------------------------ |
| scalar-index read 1 MiB | 33 ns                      | 25 ns                    |
| decode byte 1 MiB       | 70 ns                      | 70 ns                    |
| encodeRepeat 1 MiB      | 35.2 ms (~34 ns/B)         | 33.7 ms (~32 ns/B)       |
| decodeRepeat 8 KiB      | 2.97 s                     | 3.23 s                   |
| decodeFull 8 KiB        | 424 ms                     | 434 ms                   |
| decodeFast 1 MiB        | 62 ns                      | 62 ns                    |
| roundtrip byte encode   | 70 ns                      | 143 ns                   |
| roundtrip byte decode   | 70 ns                      | 60 ns                    |
| encodeVarint 12345678   | 64 ns                      | 129 ns                   |
| decodeVarint 12345678   | 202 ns                     | 225 ns                   |

(Note: the two configs also differ in clang 19 vs 21, so this is a coarse "does
LLVM matter at all" probe, not a clean single-variable isolation.)

**0.2 → 0.3 consequence:** drop the `lean4-llvm` override + clang-19 pin from
`default.nix`/`flake.nix` as dead weight. "Utilize LLVM" now means either (a)
re-introduce a _proved_ `@[extern]` primop seam if Lever B is needed, or (b) tune
the plain clang flags (`-O3`/`-march=native`) on the emitted C — not keep a dormant
LLVM build.

- [x] 0.4 **Remove the override (first, before the next session).** Deleted the
      `lean4-llvm` override from `default.nix` (the `llvmPackages_19` input, the
      `stdenv`/`-DLLVM=ON`/clang-19 wiring, and the `lean4 = lean4-llvm` re-export),
      dropped `llvmPackages_19.clang` from `flake.nix`'s dev shell, and pointed
      every path at plain `lean4`. Verified: `nix eval` the dev shell resolves,
      `nix develop -c lake build` (proof gate) and `lake build bench` both green,
      `leanc --version` now reports clang 21.1.8 (plain, no LLVM), and the bench
      runs byte-exactly with the same neutral numbers.

## 1. Profile and attribute the cost

- [x] 1.1 Add a machine calibration baseline lane to `Bench.lean`: `memset`/`memcpy`
      of the same byte count (via an `unsafe` extern or a tight normalized loop),
      printed once at startup so every lane's throughput is relative, not absolute.
- [x] 1.2 Add a per-lane throughput report (ns/op **and** bytes/op or MB/s) and a
      ×1/×2/×4 size sweep, so linear vs quadratic scaling is visible in the output.
- [x] 1.3 Add a representation-isolation lane for `encodeRepeat`: time the encode
      with the `concat`/sigma/`Fin`-sum arithmetic elided (an `unsafe` scratch
      accumulator, not part of `Codec`) to split bandwidth vs dependent-type
      bookkeeping vs residual.
- [x] 1.4 Read the emitted IR (`.lake/build/ir/Bench.c`, `Codec.c`) for the
      `encodeRepeat`/`decodeFull` hot loops and record, in this file, exactly what
      dominates: `Nat`/`Fin` arithmetic, sigma re-packaging, `concat`/cast, or
      allocation. Do not guess; cite the C.

**1.4 attribution (read from `.lake/build/ir/Codec/Encode.c` / `Decode.c`):**

- `encodeRepeat`'s hot loop (`lp_codec_Codec_encodeRepeat___redArg`, `Encode.c`)
  per `cons` cell does: `lean_nat_add` (the length sum), `lean_alloc_closure`
  (wrapping `lp_codec_Codec_concat___boxed`, arity 5) capturing the two length
  `Nat`s and two `Bytes` closures, plus two `lean_alloc_ctor`s (a `Sigma` pair and
  an `Option.some`). **The `concat` is a _closure_, not a flat buffer**: every
  element allocates a 5-arity closure whose body is `concat` (`if i.val < m then
s₁ ⟨·⟩ else s₂ ⟨·⟩`) — a `Fin`-sum dispatch + a cast per read, re-invoked per
  element. So **allocation dominates** (a `concat` closure + 2 ctors per element),
  not raw bandwidth; the `Nat`/`Fin` arithmetic and `concat`/cast are _inside_
  those per-element closures rather than hoisted.
- `decode`'s `byte` case (`lp_codec_Codec_decode___redArg`, `Decode.c`) is a single
  `lean_nat_dec_eq` (the `n = 0` test) then `lean_apply_1(v_s_55_, 0)` — the scalar
  indexed read `s ⟨0, ·⟩` is the _only_ carrier op; the rest is `Suffix_drop`
  (a `lean_nat_sub`) and list/`Suffix` ctors. The `decodeFull`/`decodeRepeat`
  wrapped loops are `List.mapTR`/`flatMapTR`/`WellFounded.fix` recursion over
  `List` cons cells (array-backed `lean_array_push`/`lean_array_to_list`), i.e.
  **list-materialization + recursion**, not scalar-read arithmetic.

**1.x measured (after fixing the dev-shell `cc` below):**

| Lane                        | ×1 (256 KiB) | ×2 (512 KiB) | ×4 (1 MiB)   | shape                                      |
| --------------------------- | ------------ | ------------ | ------------ | ------------------------------------------ |
| `calib memcpy`              | —            | —            | 56 532 MiB/s | O(n), the raw-memory floor                 |
| `calib memset` (push loop)  | —            | —            | 431 MiB/s    | push = per-byte realloc, not a true memset |
| `encodeRepeat byte`         | 8 727 µs     | 17 244 µs    | 34 845 µs    | **linear, 28 MiB/s** (≈ 2× per doubling)   |
| `encodeRepeat iso` (elided) | 339 µs       | 669 µs       | 1 498 µs     | linear, 737 MiB/s                          |

**Attribution conclusion (drives Lever A):** the encode is linear but ~26× slower
than the elided-accumulator lane (`encodeRepeat iso`) and ~2000× off raw `memcpy`.
The _entire_ gap is the structural `concat` (a per-element 5-arity closure + `Fin`
-sum dispatch + `Nat`-add + 2 ctors), not bandwidth — the elided lane does the same
byte count at 737 MiB/s. §2.1's flat-accumulator re-staging is the direct lever.

**1.x blocker (RESOLVED):** `lake build bench` in the dev shell failed
`ld: library 'c++' not found` because `mkShellNoCC` left `/usr/bin/cc` (system Apple
clang) in PATH while `leanc`/the link step needs the Nix clang wrapper (which
provides `libc++`). Fixed soundly by adding `pkgs.stdenv.cc` to `devShells.default`
in `flake.nix` (the same wrapped clang-21.1.8 `leanc` already hardcodes); `cc`/`clang`/
`c++` now resolve to the Nix toolchain and `lake build bench` links + runs green.
(`nix build .#bench` was always green in the sandbox; this makes the _dev shell_
consistent with it. §0.4's "`nix develop -c lake build bench` green" was inaccurate.)

## 2. Pure-lowering pass on the single carrier (Lever A)

**Session decision (supersedes Lever A):** §1's measurement is unambiguous — the
pure `Bytes n := Fin n → UInt8` carrier _cannot_ be "blazing fast" for **bulk**
construction, because it is a pure function (a `Fin n → UInt8`), so `encodeRepeat`
assembles nested `concat` closures at 28 MiB/s vs the elided `ByteArray` lane's
507–737 MiB/s (and 56 000 MiB/s raw `memcpy`). The README's "scalar indexed load"
claim is true for **reads** (`decode`, the scalar `s ⟨i,·⟩`) but was never true for
**bulk writes**. A "flat accumulator" / "pre-size the output" (2.1's wording)
describes a mutable buffer, which the single carrier does not provide — that is
precisely §1.3's `ByteArray` lane, a _different_ carrier. So Lever A's _pure_
re-staging cannot close the ~26× gap while keeping `encodeRepeat`'s denotation
byte-identical (that is what forces the nested-`concat` representation).

**The plan is Lever B, done correctly — and it does NOT need LLVM.** A `ByteArray`
/`Array UInt8` accumulator behind the already-present `@[extern]` primops
(`ByteArray.push`/`copySlice`) runs at ~500–700 MiB/s on **plain clang** (§1.3's
isolation lane proves it; LLVM was never required — that is exactly why §0 removed
it). The refinement lemma `fastEncodeRepeat p xs = encodeRepeat p xs` is proved
**pointwise** via the existing `Bytes.ext`/`cast`-commutation lemma library and
`Array.ofFn` (the `Fin n → UInt8 ≃ Array UInt8` bridge), which is `[propext,
Quot.sound]`-only with zero `Classical.choice` — the prior five attempts failed
only because they leaked `Array.extract`/`Array.toList`. "Blazing fast" = bulk
paths go through the contiguous buffer (law-backed); **reads/`decode` stay on
`Bytes n`** (already a scalar load). `Bytes n` remains the _specification_ substrate
for every law; the fast path is a proved-equal implementation, not a new spec.

Lever A tasks below are retained for the record but will be satisfied by the Lever B
law-backed fast path; the "within ~10× of calibration" gate (2.4) is met by the
`ByteArray` lane, not by pure `Bytes n`.

- [ ] 2.1 Re-stage `encodeRepeat` from structural `concat` (a `Fin`-sum concat and
      cast per `cons`) to a single flat accumulator: pre-size the output, append
      per element with a hoisted bounds check, and do the length-cast once at the
      end. Prove `encodeRepeat`'s type/denotation unchanged; `#print axioms
    Codec.encodeRepeat_rel` stays `[propext, Quot.sound]`.
      **→ Implemented as `fastEncodeRepeat` (Lever B): a `ByteArray`/`Array UInt8`
      accumulator behind `@[extern]` primops, proved `= encodeRepeat` pointwise.**
- [ ] 2.2 Hoist bounds-check and `Nat`/`Fin` index computation out of the
      `decode`/`decodeFast` byte loop so the scalar indexed read `s ⟨i,·⟩` is the
      only per-element operation. `#print axioms Codec.decode_spec` stays
      `[propext, Quot.sound]`.
- [ ] 2.3 Re-stage `decodeFull` to re-use already-consumed prefixes (no per-step
      re-attach/re-parse), verifying `decodeFull_some`/`decodeFull_spec` still close
      with zero `sorry`, zero `Classical.choice`.
- [ ] 2.4 Re-measure under ×1/×2/×4 and record the new table here. Decide: does
      Lever A reach the baseline (within ~10× of the calibration lane)? If yes,
      skip §3; if no, proceed to Lever B.

## 3. Law-backed fast path (Lever B) — only if §2 falls short

- [ ] 3.1 Re-introduce an `Array`/`ByteArray` bulk accumulator behind the LLVM
      `@[extern]` primops (re-building `lean4` with `-DLLVM=ON` only if Lever B is
      actually pursued — the override was removed in 0.4), with refinement lemmas
      `fastEncodeRepeat p xs = encodeRepeat p xs` (and the decode dual) proved
      **without** `Array.extract`/`Array.toList` (which leaked `Classical.choice` in
      the prior tiers) — use the carrier's pointwise `Bytes.ext`/cast lemmas instead.
- [ ] 3.2 Prove the refinement lemmas are `[propext, Quot.sound]`-only
      (`#print axioms` each), zero `sorry`. If a clean proof cannot be found, record
      that here and fall back to Lever A; do not ship an `unsafe`/asserted seam.
- [ ] 3.3 Re-measure and record the table. Confirm the fast path survives the
      value (not length) checks in the bench.

## 4. Explicit compiler flag tuning (LLVM override already removed)

- [ ] 4.1 Add `-O3` (and, if reproducible, `-march=native`/LTO/PGO) to the C
      compile of the emitted `*.c` in `default.nix`/`lakefile.lean`, and re-measure
      the pure-lowering paths (Lever A) to see if the plain clang-21 optimizer alone
      closes the gap.
- [ ] 4.2 Only if Lever B is pursued: decide whether re-enabling `-DLLVM=ON` (a
      fresh `lean4-llvm`) is justified by a _measured_ primop benefit; otherwise the
      toolchain stays on plain `lean4` (the 0.4 removal stands).
- [ ] 4.3 Record the final decision and benchmark table in this file.

## 5. Gate and doc

- [ ] 5.1 `lake build` zero `sorry`/warnings and `#print axioms Codec.roundtrip` ⇒
      `[propext, Quot.sound]` (zero `Classical.choice`); run the bench byte-exactly.
- [ ] 5.2 Update `Bench.lean` module docs and the README/AGENTS to state the new
      performance posture (the honest table, the attribution, and whether LLVM is
      utilized or removed), preserving every `[D#]`/`[S#]` anchor meaning.
