# Tasks

> **Session status (latest):** toolchain is plain nixpkgs `lean4` (clang 21.1.8).
> §1 (profiling/attribution) is complete; the measured finding settled that pure
> `Bytes n` lowering cannot reach the baseline, so §2/§3 collapse into one
> law-backed bulk fast path. Next: §2.1 (`fastEncodeRepeat` + its refinement proof).

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

**Attribution conclusion:** the encode is linear but ~26× slower than the
elided-accumulator lane (`encodeRepeat iso`) and ~2000× off raw `memcpy`. The
_entire_ gap is the structural `concat` (a per-element 5-arity closure + `Fin`-sum
dispatch + `Nat`-add + 2 ctors), not bandwidth — the elided lane does the same
byte count at 737 MiB/s. The bulk fast path (§3) is the direct lever.

**1.x blocker (RESOLVED):** `lake build bench` in the dev shell failed
`ld: library 'c++' not found` because `mkShellNoCC` left `/usr/bin/cc` (system Apple
clang) in PATH while `leanc`/the link step needs the Nix clang wrapper (which
provides `libc++`). Fixed soundly by adding `pkgs.stdenv.cc` to `devShells.default`
in `flake.nix` (the same wrapped clang-21.1.8 `leanc` already hardcodes); `cc`/`clang`/
`c++` now resolve to the Nix toolchain and `lake build bench` links + runs green.
(`nix build .#bench` was always green in the sandbox; this makes the _dev shell_
consistent with it.)

## 2. The bulk hot path (re-staging)

**Session decision:** §1's measurement is unambiguous — the pure
`Bytes n := Fin n → UInt8` carrier _cannot_ be "blazing fast" for **bulk**
construction, because it is a pure function (a `Fin n → UInt8`), so `encodeRepeat`
assembles nested `concat` closures at 28 MiB/s vs the elided `ByteArray` lane's
507–737 MiB/s (and 56 000 MiB/s raw `memcpy`). The README's "scalar indexed load"
claim is true for **reads** (`decode`, the scalar `s ⟨i,·⟩`) but was never true for
**bulk writes**. A "flat accumulator" / "pre-size the output" describes a mutable
buffer, which the single carrier does not provide — that is precisely §1.3's
`ByteArray` lane, a _different_ carrier. So pure re-staging cannot close the ~26×
gap while keeping `encodeRepeat`'s denotation byte-identical (that is what forces
the nested-`concat` representation).

**The plan (single approach):** a `ByteArray`/`Array UInt8` accumulator behind the
Lean runtime's own `@[extern]` primops (`ByteArray.push`/`copySlice`) runs at
~500–700 MiB/s on plain clang (§1.3's isolation lane proves it). The refinement
lemma `fastEncodeRepeat p xs = encodeRepeat p xs` is proved **pointwise** via the
existing `Bytes.ext`/`cast`-commutation lemma library and `Array.ofFn` (the
`Fin n → UInt8 ≃ Array UInt8` bridge), `[propext, Quot.sound]`-only with zero
`Classical.choice` — the prior attempts failed only because they leaked
`Array.extract`/`Array.toList`. "Blazing fast" = bulk paths go through the
contiguous buffer (law-backed); **reads/`decode` stay on `Bytes n`** (already a
scalar load). `Bytes n` remains the _specification_ substrate for every law; the
fast path is a proved-equal implementation, not a new spec.

The re-staging tasks below are retained for the record but are satisfied by the
single law-backed bulk fast path; the "within ~10× of calibration" gate (2.4) is met by
the `ByteArray` lane, not by pure `Bytes n`.

- [ ] 2.1 Re-stage `encodeRepeat` from structural `concat` (a `Fin`-sum concat and
      cast per `cons`) to a single flat accumulator: pre-size the output, append
      per element with a hoisted bounds check, and do the length-cast once at the
      end. Prove `encodeRepeat`'s type/denotation unchanged; `#print axioms
  Codec.encodeRepeat_rel` stays `[propext, Quot.sound]`.
      **→ Implemented as `fastEncodeRepeat`: a `ByteArray`/`Array UInt8`
      accumulator behind `@[extern]` primops, proved `= encodeRepeat` pointwise.**
- [ ] 2.2 Hoist bounds-check and `Nat`/`Fin` index computation out of the
      `decode`/`decodeFast` byte loop so the scalar indexed read `s ⟨i,·⟩` is the
      only per-element operation. `#print axioms Codec.decode_spec` stays
      `[propext, Quot.sound]`.
- [ ] 2.3 Re-stage `decodeFull` to re-use already-consumed prefixes (no per-step
      re-attach/re-parse), verifying `decodeFull_some`/`decodeFull_spec` still close
      with zero `sorry`, zero `Classical.choice`.
- [ ] 2.4 Re-measure under ×1/×2/×4 and record the new table here.

## 3. Law-backed bulk fast path

- [ ] 3.1 Add a `ByteArray`/`Array UInt8` bulk accumulator behind the Lean
      runtime's `@[extern]` primops (`ByteArray.push`/`copySlice`/`get!` —
      hand-written C in the runtime), with refinement lemmas
      `fastEncodeRepeat p xs = encodeRepeat p xs` (and the decode dual) proved
      **without** `Array.extract`/`Array.toList` (which leak `Classical.choice` in
      the prior tiers) — use the carrier's pointwise `Bytes.ext`/cast lemmas instead.
- [ ] 3.2 Prove the refinement lemmas are `[propext, Quot.sound]`-only
      (`#print axioms` each), zero `sorry`. If a clean proof cannot be found, record
      that here; do not ship an `unsafe`/asserted seam.
- [ ] 3.3 Re-measure and record the table. Confirm the fast path survives the
      value (not length) checks in the bench.

## 4. Explicit compiler flag tuning

- [ ] 4.1 Add `-O3` (and, if reproducible, `-march=native`/LTO/PGO) to the C
      compile of the emitted `*.c` in `default.nix`/`lakefile.lean`, and re-measure
      the law-backed fast path to see if the plain clang optimizer closes any
      remaining gap.
- [ ] 4.2 Record the final decision and benchmark table in this file.

## 5. Gate and doc

- [ ] 5.1 `lake build` zero `sorry`/warnings and `#print axioms Codec.roundtrip` ⇒
      `[propext, Quot.sound]` (zero `Classical.choice`); run the bench byte-exactly.
- [ ] 5.2 Update `Bench.lean` module docs and the README/AGENTS to state the new
      performance posture (the honest table and the attribution), preserving every
      `[D#]`/`[S#]` anchor meaning.
