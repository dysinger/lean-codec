# AGENTS.md

Guidance for AI coding agents working in this repository.

## Project

`codec` — a verified, byte-exact, bidirectional codec library in Lean 4
(repo directory `lean-codec`). Takes Rendel & Ostermann's _Invertible Syntax
Descriptions_ (2010) and makes it dependently typed, provable, and binary.

Stdlib-only (no mathlib). Build with `lake build`; the proof gate is the same
build with zero `sorry`.

## Toolchain / environment: read first

**This is a Nix flake project. Every tool is in the flake `devShells.default`, not
on the host PATH.** Before doing anything, enter the dev shell:

```bash
nix develop
```

That shell provides the pinned `lean`/`lake` (Lean 4.34.1), `elan`, and the
**`openspec` CLI** (spec-driven workflow tool) — none of which are guaranteed to be
on the host. Then run the same commands (e.g. `openspec list --json`,
`openspec status --change … --json`, `lake build`, `nix build '.#bench'`).

Do **not**:

- search the host filesystem to locate tools (e.g. `find / -name openspec …`) —
  they live in the Nix store, reached via `nix develop`;
- assume `openspec`/`lake`/`lean` are already on PATH — check with `nix develop`
  first;
- fall back to hand-editing `openspec/` artifacts when `openspec` is unavailable
  on the host — get it from `nix develop`.

**Long builds (HARD RULE):** never run a long `nix build` (toolchain, bench, or
proof gate) in the foreground of a tool call, and never set a huge tool timeout
(`600000`/`900000` seconds = days-to-weeks — absurd and forbidden). Long-running
Nix builds cost real calendar time:

- launch them detached with `nohup … > /tmp/<name>.log 2>&1 &` and **poll** the
  log with short `bash` calls (seconds, not minutes) to check progress;
- keep the `bash` tool `timeout` small (≤ ~120s) for polling; keep blocking work
  tiny. If a command will exceed that, it must go detached;
- never `sleep` for minutes inside a single foreground call to "wait out" a
  build.

(For Nix usage details see the `nix` skill; this note is the project-specific
reminder that the toolchain is _flake-scoped_, not host-global.)

Source of truth:

- Task ledger: `openspec/changes/invertible-binary-core/tasks.md`.
- Reference paper: `PAPER.md`.
- Design rationale: `openspec/changes/invertible-binary-core/{proposal,design}.md` and `README.md`.

## Next session — handoff

> What's done, what's open, and the decisions to resolve before coding. Read first.

**Done** (compiles clean: zero sorries, zero warnings; `#print axioms Codec.roundtrip` ⇒ `[propext, Quot.sound]`):

- `Codec/Iso.lean` — `Iso` + folded combinators: `foldl` (§5.3), `foldr` (the
  right-fold dual, a _fresh_ well-founded recursion with step `Iso (β × α) α`,
  **not** `inverse ∘ foldl ∘ inverse` which is type-incoherent), `optionSome`,
  plus the structural isos (`nil`/`cons`/`unit`/`commute`/`associate`/`element`/
  `subset`/`inverse`). `[propext, Quot.sound]` only.
- `Codec/Codec.lean` (+`Rel`, `relRepeat`, `Productive`), `Codec/Decode.lean`
  (`decode`, `decodeRepeat`, `ConsumesByte`, `byteRepeat`), `Codec/Encode.lean`
  (`encode`, `encodeRepeat`), `Codec/Sound.lean` (the **unconditional** laws:
  `decode_spec`, `bidir`, `encode_rel`, `decode_encode`, `roundtrip`,
  `productive_iff_consumesByte`, `decodeRepeat_spec`, `encodeRepeat_rel`).
- `Codec/Combinators.lean` — §6.1/§6.2 derived combinators. **§9 resolved:**
  `partial def many` is **deleted** (its `Rel` was irreducibly opaque). Unbounded
  repetition is semantic, not a `Codec` value: `relRepeat` (denotation),
  `decodeRepeat p h` (decoder), `encodeRepeat p` (encoder). The `many`-shaped
  list combinators are re-derived over these three — `sepBy`/`sepBy1` as
  `relSepBy`/`decodeSepBy`/`encodeSepBy`, and `chainl1`/`chainr1` as
  `relChain*`/`decodeChain*`/`encodeChain*` (folds via the unchanged
  `Iso.foldl`/`Iso.foldr`, decoders taking `hsep : ConsumesByte …`), each with an
  unconditional `_spec`/`_rel` law. Finite combinators unchanged: `seqRight`/
  `seqLeft`/`between`, `optional`/`maybe`, `choice`, `count`/`manyUpTo`.
- `Codec/Codec.lean` also defines `abbrev Bytes := List UInt8` (the provable
  substrate, used everywhere the core wrote `List UInt8`; _reducible_, so every
  `List` lemma applies unchanged).
- `Codec/Buffer.lean` — the packed, `ByteArray`-backed **transport surface** (§10.4):
  `Buffer` (newtype over `ByteArray`), `toBytes`/`ofBytes` (routed through
  `ByteArray.data`, the reducible `Array`, _not_ the opaque `ByteArray.toList`),
  and the transported interpreters `decodeBuffer`/`encodeBuffer` with the
  bar-transferred laws `decodeBuffer_eq`/`encodeBuffer_eq`/`decodeBuffer_spec`/
  `roundtripBuffer`.
- `Codec/Sound.lean` also gained `relFunctional`/`relUnambiguous` (relation-level
  forms) and `encodeRepeat_ne_none`; `Codec/Combinators.lean` gained the six chain
  converse laws (§10.3a): `encodeChainl1_ne_none`/`encodeChainr1_ne_none`,
  `encodeChainl1_of_decode`/`encodeChainr1_of_decode` (under `relFunctional`),
  `encodeChainl1_injective_of_unambiguous`/`encodeChainr1_injective_of_unambiguous`
  (under `relUnambiguous`).

**Decisions already made** (read before continuing):

1. `Bytes` (= `List UInt8`) for the provable core; `Buffer` (a `ByteArray`-backed
   newtype) is the separate, later executable transport surface — _not_ the proof
   substrate.
1. **`|` is the paper's backtracking union, not committed choice** (restored;
   `NonNull`/`Disjoint`/`PrefixDisjoint` deleted). Do not reintroduce a
   deterministic/committed decoder.
1. `foldl`/`foldr` are done and proved; `chainl1`/`chainr1` are re-derived as
   semantic decoders/encoders over `decodeRepeat`/`encodeRepeat` (not `Codec` values).
1. `Codec` is an inductive description AST, not the paper's §3.4 typeclass.
1. `iterate` (paper §5.3) is deliberately omitted (no field law; forward/backward
   fixpoints can differ).
1. **Unbounded `many`/`some`/`sepBy`/`chainl1` are _semantic_, not `Codec`.** An
   infinite AST cannot be a finite `Codec`, and a `partial def` is proof-opaque;
   repetition lives as `relRepeat`/`decodeRepeat`/`encodeRepeat` (cf. §9).

**Open, in order** (full detail in `tasks.md` §11):

> **Compiler-tier direction change — ARCHIVED this session (the plan was dumb).**
> The FFI/compiler "GC-less C backend" plan (`compiler-tier-extraction`) was
> killed and archived as `openspec/changes/archive/2026-10-12-compiler-tier-extraction/`.
> Reviewer finding (read-only, against pinned `lean4` 4.34.1): the plan was
> **not sound enough to start** — `Nat → size_t` is a _semantic_ change Lean's IR
> doesn't support (bignum `Nat` is not a scalar `lean_object *`), `WellFounded.fix`
> is genuinely higher-order (the codec's own `decodeFullByteArray` is a backtracking
> search, not a tail loop, so "erase the measure → `while`" only holds for a _different_
> function), there is no F\*-style "separate tool" seam in Lean (emitters are
> in-tree, compiled into `lean`), and the `memchr` acceptance criterion was
> self-contradictory (a function returning a heap `List` vs zero-allocation `memchr`).
> The real, cheaper unblock is a **zero-copy `(ptr,len)`/`USize`-indexed, slice-returning
> entry point** that the existing `EmitC` can already print unboxed — an _interface_
> change, not a compiler. Do **not** re-open a "new backend" plan until that cheaper
> first step is tried and shown insufficient. The `@[extern]` stopgap
> (`extern-c-fast-path`) is DONE and, per its corrected record, was also a
> mechanism demo (no real speedup) — so the efficiency question is genuinely open,
> and the next move is the slice-returning API, **not** another compiler plan.

> **NEXT-SESSION PLAN — `slice-returning-run-model` (DONE → superseded by
> `single-carrier-bytes`).** The efficiency
> question is now answered by changing the _result carrier_, not the compiler and
> not the byte loop. OpenSpec change **`openspec/changes/slice-returning-run-model/`**
> (validated): ship a **`USize`-indexed, `ByteArray`-span decode surface**
> (`decodeByteArraySlice : Codec α → ByteArray → USize → Option (α × USize)`,
> `decodeFullByteArraySlice : ByteArray → USize → Option (ByteArray × USize)` —
> `byte` case O(1), full-consumption returns a packed `ByteArray`, never a `List`), and a
> **packed, amortized-O(n) `ByteArray.push` encode accumulator** (`encodeByteArrayBytes`,
> promoted from the `extern-c-fast-path` lemmas) — each proved equal to the `Bytes`
> spec `[propext, Quot.sound]`-only, no new axiom. The key insight (from the two
> failures): `USize` _is_ a scalar in Lean's IR (unlike bignum `Nat`), so the existing
> `EmitC` already prints a `size_t` loop with no representation fiction; the zero-copy
> slice's lifetime is a **named trust seam** ("span valid while source `ByteArray` is
> referenced"). Bench acceptance: decode ~300 µs → sub-µs packed copy; encode ~20 ms →
> ~1.5 ms. First, do **not** revisit a compiler backend unless this is proven insufficient.

1. _*Efficiency — the F*-style carrier refinement (Paper §4.4, "work faster")._*
   **Tier A done** (`efficient-backtracking-decoder`, archived): `decodeFull`/
   `decodeRepeatFull`/`decodeFast` proved denotationally equal, `[propext, Quot.sound]`,
   ~20,000× on the full-consumption ask. **Tier B (buffer carrier) done** — the
   OpenSpec change **`openspec/changes/buffer-carrier-decoders/`** is implemented: the
   F* two-tier move (spec over `List`, run-model over `Array UInt8` + index,
   proved-equal) _without_ FFI or a compiler. Shipped: `Codec/DecodeArray.lean`
   (`decodeArray d a i : List (α × Nat)`, the relative-consumed internal `decodeArrayRel`,
   `decodeArray_eq`/`decodeArrayRel_eq`, the `decodeFull`-composed `decodeFullArray` +
   `decodeFullArray_spec`, helpers `decode_suffix`/`drop_add_length_of_append`/
   `flatMap_congr`), `Codec/EncodeArray.lean` (`encodeArray d x : Option (Array UInt8)`,
   `encodeArray_eq`), and three transfer laws in `Codec/Sound.lean` (`decodeArray_spec`,
   `encodeArray_rel`, `roundtripArray`) — all `[propext, Quot.sound]`-only. **Lesson 1:**
   `Array` is the reducible `List`-backed structure (`a.toList`, not `a.data`); the
   membership-form refinement `(x,j) ∈ decodeArray d a i ↔ (x, drop j) ∈ decode d (drop i)`
   is **wrong** for non-consuming `pure` (and empty remainders), because `drop` discards the
   index — use the function-level form `decodeArray d a i = (decode d (drop i)).map
(fun (x,r) => (x, i + (drop i).length - r.length))`, which is correct for every `d`.
   **Lesson 2:** the measured carrier win on the _non-LLVM_ toolchain is _not_ the
   design's hoped ~5–20× — stdlib `Array.size = a.toList.length` is structural O(n)
   (no cached length) when LLVM is compiled out, so `decodeArray`'s `i < a.size` guard
   walked the list each call. **Resolved by the `llvm-lean4-toolchain` change** (below):
   with LLVM enabled, `a.size` lowers to the `@[extern]` `lean_array_get_size` (O(1))
   and `a[i]` to `lean_array_fget_borrowed` (O(1)).
   **Tier B (densest carrier) also done** — the OpenSpec change
   **`openspec/changes/bytearray-carrier-decoders/`** adds the `ByteArray` carrier
   (packed `uint8_t*`, no per-byte boxing) plus the F\* LEB128 `varint : Iso Nat Bytes`
   and its `ByteArray`-carrier run-model (`decodeVarint`/`encodeVarint`), all proved
   equal to the `Bytes` spec `[propext, Quot.sound]`-only. See the handoff entry below.

> Resolved this session: §10.1 (namespace — no type rename; `Rel`/`relRepeat`/`Productive`
> now live at `Codec.*`), §10.1a/10.1b/10.1c (organization/naming/docs), §10.2
> (README/CHANGELOG/LICENSE), §10.3a (chain converse laws), §10.4 (`Buffer` transport),
> §10.5 (extraction + benchmark, see below). The `Codec` type was **not** renamed —
> Lean lets the type `Codec` and namespace `Codec` coexist; the fix was to restore the
> uniform `namespace Codec` in `Codec/Codec.lean`. New substrate/transport naming:
> `Bytes` = `abbrev Bytes := List UInt8` (proof substrate, reducible), `Buffer` = packed
> `ByteArray` newtype (`Codec.Buffer`, transport via `ByteArray.data`).

> **Extraction + benchmark (§10.5, task 1.6) — DONE this session.** Tooling decision:
> the pinned `lean4` 4.34.1 reports `--features []` and `-b` (LLVM) asserts
> `-DLLVM=ON`, so extraction is the **C backend** (`lake env lean -c`, and lake's own
> `lean_exe` link emitting `.c`/`.c.o` under `.lake/build/ir/`) — no LLVM toolchain
> provisioned. Deliverable: `Bench.lean`, a top-level `lean_exe` (root-level `main`) that
> drives `decode`/`encodeRepeat`/`decodeRepeat`/`Buffer.ofBytes`/`Buffer.toBytes` on a
> synthetic `byte`/`many` description; wired as `default.nix#bench` (installs `bin/bench`,
> `meta.mainProgram = "bench"`) and `flake.nix#packages.<system>.bench`. **Measured
> (arm64, reps=20):** `encodeRepeat`/`Buffer.ofBytes`/`Buffer.toBytes` scale linearly
> (64 ms / 8 ms / 14 ms at 2 MiB); `decode byte` is O(1) (~100 ns); the backtracking
> `decodeRepeat byte [16384]` ≈ 13.8 s (quadratic, paper §4.4 — the §10.6 target).
> Hot-path audit clean: `decode` uses `match` (no `getElem`-with-proof leak),
> `Buffer.toBytes` uses `ByteArray.data` (reducible `Array`), not the opaque
> `ByteArray.toList`. `lake build` (proof gate) stays `defaultTargets = ["codec"]`;
> the `bench` exe is built only via `lake build bench` / the Nix `bench` derivation.

> **Efficiency (Tier A) — DONE this session** (`efficient-backtracking-decoder`).
> `decodeFull`/`decodeRepeatFull` (`Codec/Decode.lean`, `Option (List α)` full-consumption
> "many", `WellFounded.fix` on `s.length`, no `partial`) and `decodeFast` (list-fused
> `decode`, `map` replacing `flatMap`-over-singleton in `seq`) are proved
> denotationally equal (`decodeFull_spec` under a full-consumption-uniqueness
> hypothesis `huniq`; `decodeFast_eq` via `List.map_eq_flatMap`; transfer laws
> `decodeFast_spec`/`bidir_decodeFast`/`roundtrip_decodeFast`/`decodeRepeatFull_spec`
> in `Sound.lean`), all `[propext, Quot.sound]`-only. `Bench.lean` gained
> `decodeFull`/`decodeRepeatFull`/`decodeFast` legs; measured **~20,000× faster**
> (`decodeFull byte [16384]` = 545 µs vs `decodeRepeat` = 11.2 s). **Tier B
> (memoizing chart) is a separate, deferred change.**

> **LLVM toolchain (Tier B carrier speedup) — DONE this session**
> (`llvm-lean4-toolchain`). The `buffer-carrier-decoders` run-model was _correct but
> slow_ because the pinned `lean4` was built **without LLVM**, so `Array`/`ByteArray`
> fell back to pure-`List` (`Array.size = List.length` O(n), no `@[extern]` C++
> primops), and `lake build bench` even failed to link (`ld: library 'c++' not found`).
> **Fix (no FFI, no compiler authored — a stock build-configuration change):**
> build `lean4` with `LLVM=ON` and the _consistent_ LLVM 19 toolchain
> (`llvmPackages_19.stdenv` — clang 19.1.7 + libc++ 19.1.7 + llvm 19.1.7), wiring it
> into every path (`default.nix`'s `lean4` input, `flake.nix`'s dev shell + packages).
> Two non-obvious findings (see `openspec/changes/llvm-lean4-toolchain/design.md`):
>
> - `-DLLVM=ON` must be a **raw** string flag (`:BOOL=` typing makes it a `BOOL` cache
>   var that Lean's top-level `CMakeLists.txt` does not forward to the stage0/stage1
>   `ExternalProject` sub-builds, silently disabling LLVM in every stage).
> - The **whole toolchain** must be LLVM 19, not just `llvm` libs: upstream
>   `lean_llvm_parse_bitcode` aborts on cross-major bitcode (`Unknown attribute kind
(102) (Producer: 'LLVM21.1.8' Reader: 'LLVM 19.1.7')`), so mixing the host stdenv's
>   clang 21 with `llvmPackages_19.llvm` fails at stage1 stdlib build.
>   **Result:** `lean --features` ⇒ `[LLVM]`; `lake build bench` links (libc++ present);
>   the extracted `decodeArray byte` lowers to `lean_array_get_size`/`lean_array_fget_borrowed`
>   (O(1), confirmed flat ~73–188 ns over a 1024× size range) vs the O(n) `List.length`
>   baseline. Proof gate green, axiom record unchanged (`[propext, Quot.sound]`).

> **ByteArray carrier + LEB128 varint — DONE this session**
> (`bytearray-carrier-decoders`). On top of the LLVM-enabled toolchain, the **densest
> stdlib carrier** is added: `ByteArray` (`structure ByteArray where data : Array UInt8`,
> the packed `LeanScalarArray` — a contiguous `uint8_t*` with cached size/capacity,
> `lean_byte_array_get`/`lean_sarray_size`/`lean_sarray_push` primops, `memcmp` equality,
> **no per-byte boxing**), where `Array UInt8` still boxes each byte. Shipped:
>
> - `Codec/DecodeByteArray.lean` — the **native** index recursion `decodeByteArrayRel`
>   (structurally identical to `decode`, reading `a[i]` via the O(1) `lean_byte_array_get!`
>   in the `byte` case, recursing `i + m` through `seq`; no `List` is materialized),
>   the public `decodeByteArray d a i = (decodeByteArrayRel d a i).map (fun (x,n) => (x, i+n))`,
>   and `decodeByteArrayRel_eq`/`decodeByteArray_eq`/`decodeByteArray_byte`. Plus the **native**
>   full-consumption `decodeFullByteArray` (`WellFounded.fix` on `a.size - i`, reading `a[i]`)
>   with its spec `decodeFullByteArray_spec` (membership form, mirrors `decodeFull_spec`, same
>   `huniq`) and the step/candidate lemmas (`decodeFullByteArrayStep_some`/`_ne_none`,
>   `mem_decodeByteArrayRel_to_decode`/`_of_decode`, `drop_of_mem_decode_byteArray`).
>   **Native re-write (tasks 4.1–4.2):** an earlier draft defined `decodeByteArray d a i =
decodeArray d a.data i` _by composition_, re-materializing `a.data.toList` — so no packed
>   byte was ever read; the native recursion fixes that (the extracted C lowers to
>   `lean_byte_array_fget`, no `.toList`).
> - `Codec/DecodeArray.lean` — `decodeFullArray` is **now native too** (`WellFounded.fix` on
>   `a.size - i` reading `a[i]`), proved by `decodeFullArray_spec` (task 4.3); removes the
>   same `.toList` materialization the compositional draft had (extracted C uses
>   `lean_array_fget_borrowed`).
> - `Codec/EncodeByteArray.lean` — `encodeByteArray d x = (encodeArray d x).map ByteArray.mk`,
>   `encodeByteArray_eq` (one `ByteArray.mk`/`ByteArray.data` rewrite).
> - Three transfer laws in `Codec/Sound.lean` — `decodeByteArray_spec`,
>   `encodeByteArray_rel`, `roundtripByteArray`.
> - `Codec/VarBinary.lean` — the F\* LEB128 varint as the **spec** `varint : Iso Nat Bytes`
>   (`varintBytes`/`varintDecodeStep`/`varintUnapply`, 7 data bits/byte + continuation
>   high bit, `0 ↦ [0]`, `128 ↦ [0x80,0x01]`, `300 ↦ [0xAC,0x02]`), its roundtrip law
>   (`dec_enc`/`enc_dec`, the **encode ∘ decode** direction rejecting overlong/non-canonical
>   forms), **plus** the `ByteArray`-carrier run-model `decodeVarint`/`encodeVarint` and
>   their `decodeVarint_eq`/`encodeVarint_eq`/`roundtripVarint` laws. All `[propext, Quot.sound]`-only.
>
> **Finding:** `ByteArray` is the densest stdlib carrier; the toolchain (LLVM) was the
> blocker, now the carrier is the **last lever**. Measured packed-carrier legs (`Bench.lean`,
> arm64 reps=20): `encodeVarint 12345678` ≈ 52 ns/op, `decodeVarint` ≈ 108 ns/op,
> `encodeByteArray byte` ≈ 62 ns/op, **`decodeByteArray byte [1 MiB]` = 83 ns** (the native
> re-write's win — was ≈ 0.4 ms when defined by composition and paying the one-time
> `Array.toList` transport, so ~4800×), `decodeFullByteArray byte [8192]` ≈ 298 µs /
> `decodeFullArray byte [8192]` ≈ 302 µs (native, but full-consumption is
> result-list-construction-bound so ≈ `decodeFull` ~271 µs — the O(1)-index carrier win
> is on the single/multi-byte _reads_, not the list-building path). This change _uses_
> the now-enabled `@[extern]` primops (no new proof axioms, no `[D#]`/`[S#]` anchor
> change).

> **`@[extern]` C fast path (extern-c-fast-path) — DONE this session.** The
> **stopgap** (formerly `compiler-tier-extraction` task 4.3, since archived),
> landing _before_ any full
> GC-less C backend: it splices hand-written, trusted C into the _already proved_
> `ByteArray` run-model's hot path via Lean's `@[extern]` FFI (shape 2 — a `def` whose
> **Lean body still elaborates** — the stdlib `ByteArray.get`/`size`/`push` pattern and
> the F\*-trusts-KaRaMeL posture). **Shipped:**
>
> - `Codec/ExternFastPath.lean` — two primitives, each a plain `def` with an elaborating
>   body + an `@[extern "codec_…"]` C symbol: `byteSlice a i : ByteArray` (body
>   `a.extract i a.size`; C symbol `codec_byte_array_slice`, a `memcpy`-style suffix copy)
>   and `encodeAppend a b : ByteArray` (body `a.push b`; C symbol `codec_encode_append`,
>   an amortized `lean_byte_array_push`). Plus the **routed fast paths** with equality laws:
>   `decodeFullByteArrayByte a i : Option (List UInt8 × Nat)` (one `codec_byte_array_slice` +
>   a `List` materialization at the boundary; `decodeFullByteArrayByte_eq` replaces the
>   `WellFounded.fix` per-byte recursion), and `encodeByteArrayBytes xs : ByteArray` (fold
>   `codec_encode_append` into a pre-sized packed buffer; `encodeByteArrayBytes_eq` via a
>   `foldl`-push `= List.toArray` lemma). Supporting lemmas: `byteSlice_data_toList`,
>   `decodeRepeat_byte_full`/`decodeRepeat_byte_unique` (the `huniq` `decodeFull_spec` needs),
>   `foldl_push_toArray`/`foldl_ba_push`, `encodeRepeat_byte`. All `[propext, Quot.sound]`-only.
> - `Codec/ExternFastPath.c` — the hand-written C: `#include <lean/lean.h>`, libc `memcpy`,
>   calling the runtime's inline sarray primitives (`lean_alloc_sarray`/`lean_sarray_cptr`/
>   `lean_unbox`/`lean_byte_array_push`); no new `lean_rt` dependency.
> - **Build wiring:** the TOML lakefile became a **`lakefile.lean`** script, adding
>   `target externFastPathO : FilePath := … buildLeanO oFile (Job.pure srcFile) …` (the
>   `leanc`-compiled object) and `lean_exe bench where moreLinkObjs := #[externFastPathO]`;
>   `@[default_target]` on `lean_lib codec` replaces the TOML `defaultTargets`. Verified the
>   emitted `.lake/build/ir/Codec/ExternFastPath.c` calls `codec_byte_array_slice`/
>   `codec_encode_append` (not the Lean bodies). **Lake lesson:** `@[default_target]` is the
>   attribute (the TOML `defaultTargets` field maps to `LakefileConfig`, not a `.lean`
>   `PackageConfig.where` field); `buildLeanO`/`compileO` (from `Lake.Build.Common`/
>   `Actions`) compile hand-written C with `leanc`'s include path (`lean.h`) and matching
>   flags; `leanc` self-resolves its C compiler (clang 19) without `clang` on PATH.
> - `Bench.lean` gained an **extern tier lane**: `benchByteSlice` (the raw `memcpy`-loop
>   throughput ceiling), `benchDecodeFullByteArrayByte`, `benchEncodeByteArrayBytes`,
>   `benchEncodeAppend` — against the `List` spec / boxed `ByteArray` lanes above.
>
> **The prove-vs-trust seam decision (named, isolated):** the two C symbols are **trusted**
> to match their declared contract (the F\* stance toward KaRaMeL), and the `_eq` laws pin
> the _Lean_ meaning, so the codec's laws stay `[propext, Quot.sound]`-only and no proof
> axiom is introduced; the bench lane checks byte-exact output.
>
> **Honest outcome (corrected — NOT a speedup).** The two primitives are **thin shims over
> the stdlib's own `@[extern]`s** — `byteSlice` is the already-C `ByteArray.extract`/
> `copySlice` (`lean_byte_array_copy_slice`) specialized to the suffix; `codec_encode_append`
> forwards to `lean_byte_array_push`. The apparent "7×/12.5×" deltas were measured against
> _weaker_ baselines, not the already-committed packed carriers: `decodeFullByteArrayByte`
> beats the boxed figure only because both are dominated by the `List UInt8` result
> materialization (the _spec-interface_ cost, untouched by any C loop), and
> `encodeByteArrayBytes` beats `encodeRepeat` only because it replaces O(n²) `List.append`
> with a `ByteArray.push` fold — achievable with **no new C at all**. `byteSlice byte
[1 MiB]` = 13.2 µs is a real `memcpy` number but duplicates stdlib `copySlice`. **What is
> established:** the mechanism — elaborating-body `@[extern]` + a hand-written `.c` linked
> via a `lakefile.lean` `buildLeanO`+`moreLinkObjs` target, verified codegen, byte-exact
> bench checks, `[propext, Quot.sound]`-only — and the named trust seam. **What is NOT
> established:** any material speedup. The real bottleneck (the `List` boundary + O(n²)
> append) is an _interface/codegen_ problem — the proposed full GC-less backend
> (`compiler-tier-extraction`) was **archived as unsound/too-dumb**, leaving the
> **zero-copy `(ptr,len)`-returning entry point** as the next move.

> **`slice-returning-run-model` — DONE this session.** The "carrier swap, not
> compiler" fix the failed plans pointed to. Shipped `Codec/DecodeByteArraySlice.lean`
> and `Codec/EncodeByteArraySlice.lean` (wired into the `Codec` root):
>
> - `decodeByteArraySlice d a i : Option (α × USize)` — a **native, `USize`-indexed
>   greedy decoder** (`decodeByteArrayHead` recursion reads `a[i]`, threads `i + m`
>   through `seq`, no `List` cell); `byte` case O(1). **Sound but not complete** (it
>   short-circuits and does not backtrack across `seq`/`alt` — unlike the relational
>   `decode`), which `decodeByteArrayHead_sound`/`decodeByteArraySlice_spec` state
>   precisely (`some` result ⇒ valid `decode`).
> - `decodeFullByteArraySlice a i : Option (ByteArray × USize)` — full consumption
>   returns the **packed suffix** (never `Option (List α × Nat)`);
>   `decodeFullByteArraySlice_eq` closes against `decodeFullByteArray_spec`.
> - `encodeByteArrayBytes xs : ByteArray` — the **committed** amortized-O(n)
>   `ByteArray.push` accumulator (no custom `@[extern]`), `encodeByteArrayBytes_eq_encodeRepeat`
>   against the `List.append` denotation.
>
> All `[propext, Quot.sound]`-only (zero `Classical.choice`). **Bench (arm64, reps=20):**
> `encodeByteArrayBytes` 20.5 ms → **1.34 ms** at 1 MiB (~15×); `decodeFullByteArraySlice`
> ~5× faster than the `List`-cons `decodeFullByteArray` (no per-element result box).
> **Named trust seam:** the zero-copy span's lifetime (result aliases `a`) is documented,
> not proved — "valid while `a` is referenced". **Honest tradeoff (important):** the
> sub-µs `memcpy` floor is the `@[extern]` `byteSlice` (above), _not_ this `@[extern]`-free
> surface, because the stdlib `Array.extract`/`drop` content lemmas (`Array.toList_extract`,
> `Array.getElem_extract`, …) pull in `Classical.choice` — so `decodeFullByteArraySlice`'s
> `_eq` law uses the same `rfl`-clean `ByteArray.mk ((drop i).toArray)` transport as the
> proven `byteSlice`, trading a list-materialization intermediate (→ the C codegen pays
> the `List→LeanScalarArray` copy, so ~8 ms at 1 MiB, not sub-µs) for an axiom-free
> refinement. The next sub-µs step remains the `@[extern]` seam, not a compiler.

> **NEXT-SESSION PLAN — `single-carrier-bytes` (active, in progress).** The five
> carrier attempts above all failed for one shared reason: the library _proves on
> `List UInt8` but runs on packed `ByteArray`_, and the representation transfer is
> the whole cost (and its `Array.extract` lemmas leak `Classical.choice`). The fix is
> a **single length-indexed byte string** `Bytes n := Fin n → UInt8` — one type that is
> simulaneously reducible (proofs) and a scalar indexed load (IR), with **no second
> carrier, no transfer lemma**. OpenSpec change
> **`openspec/changes/single-carrier-bytes/`** (validated). Thread `n` through the core:
> `Rel d x (s : Bytes n)`, `decode d (s : Bytes n) : List (α × Suffix n)`,
> `encode d x : Option ({n} × Bytes n)`, `relRepeat`/`decodeRepeat`/`encodeRepeat`;
> delete the whole transfer tier (`DecodeArray`/`EncodeArray`/`DecodeByteArray`/
> `EncodeByteArray`/`DecodeByteArraySlice`/`EncodeByteArraySlice`/`ExternFastPath`/
> `Buffer`, the `lakefile.lean` `externFastPathO` target, the matching `Bench.lean`
> lanes). **DONE so far (compiles clean, `[propext, Quot.sound]`-only):** tasks 1.1–1.3
> (substrate) and 2.1/2.2 (`decode`/`decodeFast`/`decodeRepeat`/`ConsumesByte`;
> `encode`/`encodeRepeat`). **Two design decisions made this session** (recorded in
> `design.md` and the task notes — resolve or accept before continuing):
>
> 1. **`Suffix n` shape** is `{ remaining : Nat, hle : remaining ≤ n, bytes : Bytes remaining }`
>    — the spec's `({m} × Bytes m)` with the `m ≤ n` witness — _not_ the design's
>    `{ consumed, remainder : Bytes (n - consumed) }`, because `seq` composes suffixes by
>    threading `m₂ ≤ m₁ ≤ n` transitively (`Suffix.trans`), with no `Nat.sub`
>    re-derivation of `(n − c₁) − c₂`. `Suffix.consumed`/`Suffix.empty`/`Suffix.id`/
>    `Suffix.drop` accessors cover the rest.
> 2. **`decodeFull`/`decodeRepeatFull` spec proofs dropped** (`decodeFull_some`/
>    `decodeFull_ne_none`/`decodeFull_spec`, which fed `Sound.decodeRepeatFull_spec`).
>    `decodeFull` is **not a spec requirement** (the spec defines `decode`/`decodeRepeat`/
>    `encode`/`encodeRepeat` and the laws, never `decodeFull`); it was the Tier-A
>    efficiency-only optimization. The efficient `decodeFull` _definition_ + `decodeFull_zero`
>    are retained. Re-prove only if full-consumption efficiency is re-added.
>
> **REMAINING:** task 3.1 is **~90% done** (see the "CONTINUE the single-carrier re-derivation"
> block below for the three remaining `sorry`s: `decode_spec` `seq`-backward, `decode_spec` `byte`,
> `decodeRepeat_spec`); 3.2/3.3 (`decodeRepeat_spec` + `Combinators.lean` over the `Fin`-split
> carrier), 4.1–4.3 (delete transfer modules; simplify `lakefile.lean`; rewrite `Bench.lean`;
> re-derive `VarBinary.lean`), 5.1–5.2 (gate + README/AGENTS docs).
> `Codec/Sound.lean` is re-stated and **mostly proven** (only the three `sorry`s above);
> `Codec/Combinators.lean`, `Codec/VarBinary.lean` and the transfer modules are still on the
> **old `List UInt8` substrate** and do not build against the new `Codec/Codec`/`Decode`/`Encode`
> until re-derived — the tree is **intentionally in an atomic-change intermediate state**
> (the full `lake build` does not pass).

> **NEXT-SESSION PLAN — CONTINUE the single-carrier re-derivation (option #1 chosen).**
> Task 2.3 is now **DONE and landed clean** (`lake build Codec.Codec`, zero warnings,
> zero `sorry`): `prepend_assoc` (the `seq`-case reassociation, with the required
> `h : t₂.prepend s₂ = t₁.bytes` hypothesis) and `prepend_single_bdrop` (the `byte`-case
> reconstruction `(Suffix.drop 1 s).prepend (single (s ⟨0, ·⟩)) = s`), plus the supporting
> substrate lemmas `Rel_cast`/`Rel_cast_symm` (length-cast transport of `Rel` — `subst`-closed),
> `bdrop_splice`, and `prepend_eq_of_eq_splice`. The stale cast-reduction-finisher recipe below
> (the `prepend_assoc` proof transcript) is now folded into `Codec/Codec.lean`; the cast library
> (`splice_add`, `cast_fin_symm`, `cast_bytes_val'`, `Nat.eq_irrel`, `concat_assoc`, `sub_sub_add`)
> is unchanged. `Sound.lean` is **in progress**: the file is fully re-stated over the length-indexed
> carrier and **typechecks** (`lake build Codec.Sound` — only `sorry` warnings), with these pieces
> **proven** (`encode_rel`, `decode_seq_mem`, `decode_spec`'s `iso`/`alt`/`empty` cases); the rest
> are clean `sorry` markers. **Key `Sound` statement corrections made this session** (do not
> regress): `bidir` uses `Suffix.empty n` (remaining 0), NOT `Suffix.id n s` (remaining n);
> `decode_encode` is the `concat s r` formulation
> (`(x, Suffix.drop m (concat s r)) ∈ decode d (concat s r)`, with `s : Bytes m`, `r : Bytes q`);
> `Functional`/`relFunctional` compare `Sigma` pairs `(⟨n₁, s₁⟩ : Sigma fun n => Bytes n) = ⟨n₂, s₂⟩`
> (two `Rel` witnesses may have different lengths), `relUnambiguous`/`Unambiguous` quantify
> `{n} (s : Bytes n)`.
>
> **REMAINING, in order (three `sorry`s in `Sound.lean`, then onwards):**
>
> **Done this session — most of `Sound.lean` is now proven.** Six **new substrate
> lemmas** landed in `Codec/Codec.lean` (all `[propext, Quot.sound]`-only, `lake build
Codec.Codec` clean, zero `sorry`): `relRepeat_cast` (length-cast transport of `relRepeat`),
> `prepend_empty`/`prepend_empty_eq` (empty-remainder prepend reconstruction),
> `prepend_id` (identity-suffix prepend = `s`), `splice_cast_commute` (cast commutes past a
> `splice` prefix), and **`splice_splice_assoc`** (the three-way `splice` associativity —
> the session's hard blocker, now proven pointwise). In `Codec/Sound.lean`, proven:
> `encode_rel`, `decode_seq_mem`, `decode_spec` `iso`/`alt`/`empty`/`pure` (both directions)
> and `seq` **forward**, `bidir`, `decode_encode`, `roundtrip`, `productive_iff_consumesByte`,
> `relRepeat_unbounded_of_empty`, `not_productive_pure`, `encodeRepeat_rel`, `encode_ne_none`,
> `encode_of_decode`, `encode_injective_of_unambiguous`, `encodeRepeat_ne_none`.
> `#print axioms Codec.encode_rel` ⇒ `[propext, Quot.sound]` (zero `Classical.choice`).
>
> **Three `sorry`s remain (all the same cast-heavy reconstruction class):**
>
> 1. `decode_spec` `seq` **backward** — the `←` direction; the forward dir is already proven
>    (uses `prepend_assoc` + a fresh `hcast` + `splice_cast_commute`). Backward needs
>    `bdrop_prepend_splice` (prove it: `bdrop m (r.prepend (splice hm s₁ s₂)) = concat s₂ r.bytes`
>    up to a length cast, by chaining `splice_splice_assoc` → `bdrop_splice`, both already in
>    `Codec.lean`), then `prepend_eq_of_eq_splice` for the `s = (Suffix.drop m s).prepend s₁` step
>    and `Suffix.trans` field-reconstruction for `r`.
> 2. `decode_spec` `byte` — `Rel_byte` + `prepend_single_bdrop`, transported from `Bytes n`
>    (with `n ≠ 0`) to `Bytes ((n−1)+1)`; the recurring `(Suffix.drop 1 s).remaining` vs `n − 1`
>    transparency needs a `dsimp [Suffix.drop]` in the right position.
> 3. `decodeRepeat_spec` (task 3.2, well-founded on `n`) — same re-parenthesization as
>    `seq`-backward via `splice_splice_assoc` + `bdrop_prepend_splice`; mirror the old
>    `s.length` proof but over `Suffix n`.
>
> 4. Task 3.3 `Combinators.lean` (over `Bytes n`; the `sepBy`/`chainl1`/`chainr1` triples take
>    `relRepeat`/`decodeRepeat`/`encodeRepeat` at the `{n} → Bytes n` level).
> 5. Task 4.1–4.3: delete the transfer tier (`DecodeArray`/`EncodeArray`/`DecodeByteArray`/
>    `EncodeByteArray`/`DecodeByteArraySlice`/`EncodeByteArraySlice`/`ExternFastPath.{[lean](lean),c}`/`Buffer`),
>    simplify `lakefile.lean`, rewrite `Bench.lean` (drop array/byte-array/slice/extern lanes;
>    add a `Bytes`-substrate lane), re-derive `VarBinary.lean` over `Bytes n`.
> 6. Task 5.1–5.2: `lake build` (zero `sorry`/warnings), `#print axioms Codec.roundtrip` ⇒
>    `[propext, Quot.sound]`, run the Nix checks detached, update README `[D#]`/`[S#]` anchors.
>    The full `lake build` does **not** yet pass (the transfer modules still import the old substrate);
>    the tree is **intentionally in an atomic-change intermediate state** until task 4.1 deletes them.
>
> **Lean lessons earned this session (already appended to the `lean` skill):** `Rel_cast` is
> `subst`-trivial; `induction d` on an `iso`-containing AST generalizes the value into the motive
> (IH takes the value explicitly: `ih a hs`); `⟨n,s⟩` `Sigma` notation is ambiguous in equalities
> (annotate `(⟨n,s⟩ : Sigma fun k => Bytes k)`); `(k+1)-k` does not reduce (unlike `(k+1)-1`) — use
> `omega`/`Nat.sub_sub_self`/`Nat.add_sub_cancel_left`; `prepend_assoc` needs the `h` hypothesis.
> See `Codec/Codec.lean` for the landed forms.
>
> **Second Lean lesson (`2026-10-16` changelog entry in the `lean` skill):** the length-indexed
> carrier's remaining laws are all _splice-cast-commutation_ — `splice_splice_assoc` (three-way
> re-parenthesization, closed only by explicit `splice_apply` + ordered `cast_fin_symm` rewrites,
> **not** `simp`, which produces an un-reducible `cast (concat (cast (concat …)))`) ,
> `splice_cast_commute` (`subst e; simp`-trivial), `prepend_empty`/`prepend_id` (`Bytes.ext` +
> `Nat.sub_zero`/`Nat.sub_self` named `have`s). The recurring trap is `(Suffix.drop 1 s).remaining`
> not reducing to `n − 1` — `dsimp [Suffix.drop]`/`unfold Suffix.id` _in position_ before the cast
> unifies. And `encode_of_decode` closes via `hd x s s' hrels hrel' : ⟨n, s⟩ = ⟨n', s'⟩` + `.symm`
> with `hrels` from `(bidir d x n s).2` — avoid `Sigma.mk.inj`/`HEq` fallout entirely.

> **Documentation conventions (this session):** the README is the **full
> architecture statement** — _about the project and the paper only_. It carries the
> complete `[D1]`–`[D8]`/`[S1]`–`[S6]` departures/strengthenings (each with a layman
> "why"), and a short getting-started at the bottom. It has **no** status/issues
> section and **no** process/history narrative (the project is greenfield/unreleased;
> "we used to / reverted / formerly" belongs to `openspec/`'s task ledger, never the
> README). Engineering state = `openspec/` + this file; user-facing docs = README +
> `CHANGELOG.md` + `LICENSE.md`. When adding code, keep every departure/
> strengthening cross-referenced to a `[D#]`/`[S#]` anchor in the README table, and
> keep the axiom record consistent (`[propext, Quot.sound]`, never the stale
> `Classical.choice`).

## Openspec workflow

This repo uses OpenSpec (spec-driven). Changes live under
`openspec/changes/`. Planning artifacts (proposal / spec delta / design / tasks)
are created before implementation; see `.pi/prompts/opsx-*.md`.

## Git conventions

- Commit **individual files**, never `git add -A` or broad globs. Print the exact
  staged set before committing.
- `lake-manifest.json` and `flake.lock`: `lake-manifest.json` is gitignored
  (library shouldn't pin deps); `flake.lock` (Nix) _is_ tracked for reproducibility.

## Skills

- Global Lean theorem-proving skill: `lean4` (official).
- Our supplement (project-layout, proving-over-primitives, `partial`/coinduction
  lessons): global skill `lean`. Keep it generic — no project-specific details.
- Lean PR/convention/proof/MWE skills: `lean-pr`, `lean-bisect`, `lean-proof`,
  `lean-mwe`, `mathlib-build`, `mathlib-pr`, `mathlib-review`, `nightly-testing`,
  `lean4-setup` (all under the `leanprover` skill family).
- Nix tooling: **multiple Nix skills exist** — the repo is a Nix flake
  (`flake.nix`/`default.nix`); use `devenv` / `devenv-migration` only when actually
  migrating to devenv, never for this flake's own `devShells.default` (which is
  plain `pkgs.mkShellNoCC`).
