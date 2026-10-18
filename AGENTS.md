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

## Map of the repo

- **Reference paper:** `PAPER.md`.
- **Architecture statement (complete `[D#]`/`[S#]` departures/strengthenings, each
  with a layman "why"):** `README.md`.
- **Engineering state & task ledger (spec-driven):** `openspec/`. Every change
  lives under `openspec/changes/` as proposal / spec delta / design / tasks. The
  **active change is `shipped-c-fast-path`** (planning done — keep the pure `Bytes n`
  spec slow, ship fast C via `@[extern]` seams + per-format specialized decoders,
  each proved `[propext, Quot.sound]`-equal to the spec) — consult
  `openspec/changes/shipped-c-fast-path/tasks.md` for the current task status and
  next steps. History ("we used to / reverted / this session") belongs in that
  ledger, **never** in this file or the README.
  (`single-carrier-bytes` is archived as
  `openspec/changes/archive/2026-10-17-single-carrier-bytes`; `carrier-performance-tuning`
  is complete 11/11; `partial-remainder-fast-path` is complete 7/7.)
- **Library source (module `Codec`):** `Codec/`.
  - `Iso.lean` — partial isomorphisms + folded combinators (`foldl`/`foldr`).
  - `Codec.lean` — the description AST, the length-indexed substrate `Bytes n`,
    `Rel`/`relRepeat`, and the substrate/cast-commutation lemma library.
  - `Decode.lean` / `Encode.lean` — the backtracking decoder and partial encoder.
  - `Sound.lean` — the bidirectional + roundtrip laws (unconditional).
  - `Combinators.lean` — derived combinators (`many`, `*>`, `<*`, …).
- **Executable/bench:** `Bench.lean`, wired through `lakefile.lean` and Nix
  `default.nix`/`flake.nix`.
- **Downstream ecosystem (sibling repos, not in this tree):** each verified
  format/protocol is its own git repo, initialized from
  `lean-nix-flake-template`, prefix-dropped internally (`lean-basen` → package
  `basen`/module `BaseN`; `lean-vbin` → `vbin`; …), depending on `codec` by
  flake-input + `require codec from git` injection (never vendored), and
  inheriting the single-`Bytes n`-substrate + `[propext, Quot.sound]`-only
  discipline. The full ordering/layering is the `port-fstar-stack-to-lean`
  change's `ecosystem` spec (`openspec/changes/port-fstar-stack-to-lean/specs/`).
  **The active downstream is `lean-basen`** (sibling dir `../lean-basen`), the
  base-2/4/8/10/16/32/64 package — consult
  `openspec/changes/lean-basen/` (proposal / design / tasks / `rfc4648.md`) for
  its state and next steps, and work in that repo's own `lake`/`nix develop`,
  not this one's. All seven bases are landed and proven, the facade dispatches
  `BaseN.roundtrip` over `B2..B64`, and `Bench.lean` value-checks them
  byte-for-byte (`lake build bench` green, `#print axioms` =
  `[propext, Quot.sound]` for every law). The **only** open item is task 4.3's
  `nix flake check green`: `checks.lean` runs `lake build` in the Nix sandbox,
  which `require codec from git`-clones the `codec` dep, but the sandbox has
  neither `git` nor network (`could not execute external process 'git'`) — see
  `openspec/changes/lean-basen/design.md` "Next session": inject `codec-src` +
  `codec-native` `.olean` as a flake input (the task-1.1 injection half that was
  never landed; `flake.nix` still has no `codec` input).

## Active work (single carrier — archived; now `carrier-performance-tuning`)

The core (`Codec`/`Decode`/`Encode`/`Sound`/`Combinators`) is
**re-derived over the single length-indexed substrate `Bytes n := Fin n → UInt8`**,
`[propext, Quot.sound]`-only (no `Classical.choice`, zero `sorry`). (`VarBinary` was
removed from core this session — LEB128 `varint` belongs in a downstream package,
not the core spec/proof library.) The old transfer-tier
modules (`DecodeArray`/`EncodeArray`/`DecodeByteArray`/`EncodeByteArray`/
`DecodeByteArraySlice`/`EncodeByteArraySlice`/`ExternFastPath`/`Buffer`) are
**deleted**. `single-carrier-bytes` is **archived** (19/19 tasks, `#print axioms
Codec.roundtrip` = `[propext, Quot.sound]`, `nix build .#checks.aarch64-darwin.lean
.#bench` green), including the section-6 post-review hardening.

Axiom discipline: every law must stay `[propext, Quot.sound]`-only. `#print axioms
Codec.roundtrip` is the check.

### Next session: the packed carrier (speed-run implementation first, prove after)

The §1 profiling already settled the question: the pure `Bytes n` carrier is a
scalar _read_ substrate (already a single load) but a **nested-closure** _bulk-write_
substrate (`encodeRepeat` builds one `concat` closure per element → 28.7 MiB/s vs the
elided `ByteArray` lane's ~667–747 MiB/s (737.5/747.4/667.6 at ×1/×2/×4) and
`memcpy`'s 56 532 MiB/s ≈ 55.2 GiB/s). Pure re-staging is a dead end; the plan is a
**law-backed bulk fast path** (the `@[extern]` `ByteArray`/`Array UInt8` accumulator
hits ~500–700 MiB/s on the plain `cc`).

**Status:** `fastEncodeRepeat`/`pushBytesFrom`/`array_readback`/`list_ofFn_getElem_clean`/
`ofFn_concat`/`pushBytesFrom_eq` are **done** in `Codec/Encode.lean` (committed, all
`[propext, Quot.sound]`-only). `Codec/Packed.lean` holds the **packed carrier
definitions** (`decodeArray`, `decodeFullArray`, `encodeArray`, `encodeByteArrayBytes`,
`consumedAbs`, `decodeArray_bounded`). **Both the encode _and_ decode refinements are now
proved**: `encodeArray_eq`/`encodeByteArrayBytes_eq` (List-level readback, via
`ofFn_concat` + `Array.toList_append`), and — this session's win —
`decodeArray_eq`/`decodeFullArray_spec` (`[propext, Quot.sound]`-only, zero `sorry`). The
decode side rests on the **genuine-suffix invariant of `decode`** (`decode_genuine_suffix`
in `Codec/Decode.lean`): every result suffix `t` satisfies `t.bytes = bdrop t.consumed s`,
proved pointwise (`decode_genuine_suffix_pointwise`, via a `suffix_consumed_lt` bound helper)
then lifted to the `bdrop` form by `Bytes.ext`. The `seq` bridge goes through
`decode_cast` (decode insensitive to a length cast — proved by `subst; simp`, _not_ the
membership-bound spelling), `Suffix_cast_remaining`, `bdrop_consumedAbs_eq`, and
`consumedAbs_cast_trans`, threading membership via `List.map_inj_left` on the `.flatten` of
the two `flatMap`s.

**Tasks 1.3 and 3.1 are DONE.** 3.1's IR inspection (`.lake/build/ir/Codec/Packed.c`) is
**in**: the `Nat` cursor is boxed bignum (`lean_nat_dec_lt`/`lean_nat_add`/
`lean_array_fget_borrowed` at C ~402–416, `lean_object *`), **not** `size_t` — so the
"`USize` → `size_t` scalar with no backend" premise is **false/unverified** (the carrier
cursor is `Nat` by the binding decision above).

**Two binding decisions, already made (do not re-litigate):**

1. **Cursor is `Nat`, not `USize`.** (unproven `System.Platform.numBits = 64` platform
   fact would break the `[propext, Quot.sound]`-only gate; `Nat` is the proof carrier;
   the `size_t` question is answered by IR inspection, task 3.1 — done, boxed bignum.)
2. **Speed-run the implementation; gate _provability_ before volume.**

**Concrete order for next session (the Layer-2 trust seam + bench/gate):**

**DONE this session.** Tasks 4.1, 4.2, 5.1, 5.2 (and the Layer-2 half of 5.3) landed:

1. **Task 4.1 — `@[extern]` `byteSlice` (Layer 2)** is in, as a fresh module
   `Codec/ByteSlice.lean` + `Codec/ByteSlice.c`, wired via `lakefile.lean` (`target
byteSliceO` → `buildLeanO`, `moreLinkObjs := #[byteSliceO]` on the `bench` exe only,
   never the proven library). Signature `byteSlice (a : ByteArray) (i : USize) : ByteArray`
   — shape-2 extern: `@[extern "codec_byteSlice"]` with an elaborating Lean body
   (`ByteArray.mk (a.data.extract i.toNat a.data.size)`), so `#print axioms Codec.byteSlice`
   reports **no axioms**. The emitted `.lake/build/ir/Codec/ByteSlice.c` is the GC-less
   shape the design promised: `USize` → `size_t` (`lean_unbox_usize`), `ByteArray` →
   borrowed `lean_object *`, and the call `v_res_6_ = codec_byteSlice(v_a_3_, v_i_boxed_5_)`
   (a real C call, not the body). The C does one `memcpy` over `lean_sarray_cptr` via
   `lean_alloc_sarray` + `lean_sarray_size` (the public `lean.h` sarray API).
2. **Task 4.2 — trust contract documented verbatim** in `Codec/ByteSlice.lean`'s module
   header (F\*-vs-KaRaMeL posture), and Layer 2 is **excluded** from the `#print axioms` gate
   (only Layer 1 laws are verified `[propext, Quot.sound]`-only).
3. **Task 5.1 — bench** has a new Layer-2 lane `benchByteSlice` (value-checked **byte-for-
   byte** against the Lean _body_, never a length check), swept at ×1/×2/×4. Measured
   `[measured]` (128 KiB linear sweep): `byteSlice L2` **108695 MiB/s** (`575` ns/op moving
   `n/2` bytes) vs `calib memcpy` **30994 MiB/s**; `fastEncodeRepeat` **30 MiB/s** vs
   `encodeRepeat` spec **32 MiB/s**. (The `byteSlice` lane now reports `bytesPerOp = n/2`,
   the bytes it actually moves, not `n` — a review fix. The `fastEncodeRepeat` lane
   value-checks byte-for-byte while `encodeRepeat` checks only length, so the 30/32 gap is
   partly measurement asymmetry.) The 1 MiB default sweep is slow because the
   `fastEncodeRepeat` value check forces pointwise `Fin → UInt8` equality over the
   nested-closure carrier — pre-existing, not a regression; the 128 KiB sweep is the
   recorded complete run. **`byteSlice` is a standalone seam** — no library-internal call
   (the proven `decodeFullArray` keeps its axiom-clean `List.toArray.drop` body rather than
   call the trusted `@[extern]`); the bench lane is the packed-path consumer that exercises it.
4. **Task 5.2 — gate green**: `lake build` zero `sorry`/zero warnings;
   `#print axioms Codec.roundtrip` ⇒ `[propext, Quot.sound]`; every Layer-1 law
   `[propext, Quot.sound]`-only.

**Remaining (5.3 final half + task-log close):** update `openspec` task checkboxes and the
final `README`/`AGENTS` wording (the two-layer statement is in `README.md` §Performance;
`Bench.lean` already states the Layer-2 lane honestly).

**Critical review of the Layer-2 work (this session, COMPLETE).** An independent reviewer
pulled no punches and found **zero soundness issues** (all proofs axiom-clean, C ABI and
`memcpy` semantics match the Lean `byteSlice` body byte-for-byte, correct ref-counting) but
**one Critical** and three Warnings, all since fixed and re-verified:

1. **Critical — untracked `Codec/ByteSlice.c` breaks `nix build .#bench`** from a clean clone
   (Nix `src = ./.` snapshots only git-tracked files). Fixed by `git add`ing the file.
2. **`byteSlice` is a dead seam** — no library-internal caller (only the bench lane). Corrected
   the prose: it is a _standalone_ seam; "wired only onto a packed path" is a how-to-use rule,
   not a current-wiring claim.
3. **`byteSlice` bench throughput was 2× inflated** — it passed `bytesPerOp = n` but copies only
   the `n/2` suffix. Fixed to `n - n/2`; re-measured `[measured]` figures.
4. **The trust seam is invisible to Lean** — the review's deeper lesson: `@[extern]` swaps only
   emitted C, so `#print axioms` sees only the Lean body and the C is `[propext, Quot.sound]`-clean
   _regardless_; calling `byteSlice`'s trust "the single proof step" was a category error (it is a
   runtime contract, documented in prose, not a law).

**The synthesis (this session): the four carriers already answered the question — carrier #5 is
not a carrier.** `List UInt8` → `Buffer`/`ByteArray` → `Bytes n` → packed `Array UInt8`/`Nat` all
cap at the _accumulator floor_ (~750 MiB/s) because a pure immutable value can't be built by
`memcpy`; the only thing at `memcpy` speed (~80 GiB/s) is the trusted `@[extern]` `byteSlice`. The
next move is **a return-type + wiring decision, not a new carrier**: keep the `Bytes n` spec, keep
the proven packed decoder, and let `byteSlice` be the one `memcpy` that materializes a `ByteArray`
remainder **on commit** (once per chosen result, never per backtracking branch). This is written up
as the seed note `openspec/changes/carrier-performance-tuning/design-note-5th-move.md` and, after
review + a from-scratch rewrite fixing three Criticals, as the new change
**`openspec/changes/partial-remainder-fast-path`** (validated; planning complete).

## Session status: `partial-remainder-fast-path` DONE

The plan (see `openspec/changes/partial-remainder-fast-path/`) is **implemented**: `byteSlice` is
wired onto a **partial-remainder commit**. The packed decoder returns `(value, Nat cursor)`
(`decodeArray`); the single `memcpy` that turns a chosen cursor into a `ByteArray` remainder is
the `USize`-indexed `commitRemainder` (`byteSlice` wrapper), with a definitional law.

**Landed (7/7 tasks):**

1. **`commitRemainder (a : Array UInt8) (c : USize) : ByteArray := byteSlice (ByteArray.mk a) c`**
   in `Codec/ByteSlice.lean` — `USize`-indexed on purpose (matches `byteSlice`'s index, so **no**
   `Nat ↔ USize` roundtrip and **no** `System.Platform.numBits` premise; the `Nat → USize`
   conversion is the caller's, once, at the call site).
2. **`decodeArrayFast := decodeArray`** in `Codec/Packed.lean` — a documented rename stating the
   "decode yields cursors, no materialization during decode" contract (the `Nat` cursor is a fixed
   binding decision).
3. **`commitRemainder_spec : commitRemainder a c = ByteArray.mk (a.extract c.toNat a.size)`** proved
   by `rfl` (`#print axioms Codec.commitRemainder_spec` ⇒ no axioms). The refinement to `decode d`
   stays the existing `decodeArray_eq`; **no** new equality to `decode d`.
4. **Bench lane** `benchCommitRemainder n` at a mid-buffer cursor `c = (n/3).toUSize`, value-checked
   byte-for-byte against `Array.extract`, a distinct Layer-2 lane. `[measured]` (128 KiB sweep):
   `~1450–3669 MiB/s` across ×1/×2/×4 (131072 bytes: `57452` ns/op).
5. **Gate green**: `lake build` zero `sorry`/warnings; `#print axioms Codec.roundtrip` ⇒
   `[propext, Quot.sound]`; `commitRemainder_spec` ⇒ no axioms (definitional).

**Two invariants that held (do not re-litigate):** the `Bytes n` spec and its laws are untouched
(the two carrier requirements in `codec`/`codec/byte-string` are **relaxed**, not removed, via
MODIFIED deltas that carry over all existing scenarios); and the `byteSlice`/C trust is a runtime
contract excluded from the axiom gate, never folded into a law.

## Findings (this session): pure-Lean parsing has a hard ~20-40x-off-C ceiling

Goal was "very fast encode/decode", tested against an RFC 3339 date-time (the
canary: if a 23-byte fixed-shape timestamp can't be C-fast in Lean, the TLS-HTTP
buildup can't either). Measured after several optimization passes, and **the
result is a toolchain ceiling, not a code-quality issue** (confirmed three ways —
IR inspection, a `sum64` probe, and a failed optimization pass):

- **`Nat`/`UInt8`/`UInt64` arithmetic is boxed** in Lean 4.34.1's C backend
  (`lean_nat_mul`/`add`/`sub`, `lean_uint8_to_nat`, `lean_uint64_*` — all
  `lean_object*` heap calls). A pure-Lean `sum64` loop lowers to `instAddUInt64`/
  `instMulUInt64` (boxed). There is **no** pure-Lean escape (`@[implemented_by]`,
  `native_decide`, `bv_decide` are reflection/compile-time, not unboxed runtime).
- **`USize` is the only raw scalar (`size_t`), and only as an `@[extern]` argument**;
  as soon as it's stored in a `Prod`/`Option` field it re-boxes (`lean_box_usize`),
  and `USize.toNat` at each boundary adds bignum churn. Rewriting the parser to a
  `USize` cursor made it **slower** (206→~440ns) for this reason.
- **Pure-Lean `parseTimestamp` ≈ 200-400 ns/op vs ~10 ns/op for the C `strptime`
  equivalent (~20-40x off).** `encode` via `ByteArray.push` is already amortized;
  pre-sizing (`emptyWithCapacity`) didn't help. No pure-Lean code reshaping closes
  the gap because the boxed digit math (`acc*10+digit`) is irreducible inside Lean.
- **Benchmark numbers here are noisy (±2x with machine load/thermal).** The `calib
memcpy` baseline itself swung 66↔300 ns across runs; cross-check against it
  before believing any single `[measured]` figure, and don't micro-optimize under
  an unstable baseline.

**Decision (do not re-litigate):** all codecs are **pure Lean**; C is only the
generic bulk byte-movement seams (`byteSlice`/`blitBytes`/`findByte`/`commitRemainder`
= `memcpy`/`memchr`). **No per-format C, no C that parses digits/numbers/fields.**
Pure-Lean codecs are accepted at ~20-40x off C; for TLS-later the crypto is
FFI'd (OpenSSL/etc.), and 20-byte header parsing is irrelevant to TLS throughput.

## Session status: `review-polish-proof-doc` DONE (archived)

An independent reviewer gave the README a full rewrite (committed earlier). The
**code/proof** actions from that review — plus the comparative F\* audit — are now
**all landed** and the change is **archived** as
`openspec/changes/archive/2026-10-18-review-polish-proof-doc/`. Pointer only (the
ledger lives in openspec); the summary below records what actually landed this
session:

1. **`decodeArray_bounded` docstring** (`Codec/Packed.lean`) no longer claims
   "at most `a.size`"/"never overruns" (that was false: `pure x` returns `(x, i)`
   for _any_ `i`). It now states the proved `i ≤ c` monotonicity fact, and the
   missing upper bound is proved as `decodeArray_bounded_upper` under the
   load-bearing `i ≤ a.size` precondition.
2. **`decodeArray_unambiguous_value` is now PROVED** (`Codec/DecodeOne.lean`),
   `[propext, Quot.sound]`-only — the genuine outstanding proof gap is closed. The
   forward bridge: `decodeArray_eq` + `decode_spec` give `Rel d x s₀`; same count
   pins `t₁.remaining = t₂.remaining`; `decode_genuine_suffix_pointwise` +
   `Suffix.ext` pin `t₁ = t₂`; then the new `splice_prefix_read`/
   `prepend_prefix_read`/`prepend_prefix_eq` lemmas (`Codec/Codec.lean`) extract
   equal prefixes, and `Unambiguous d` forces value equality. The `DecodeOne`
   header is restored to present tense ("the committed decoder _equals_ the unique
   result").
3. **Layer-2 `blitBytes` trust seam fixed.** Its Lean body previously appended
   `Array.extract`s (variable-length results on "src too short"/"off past end"),
   which did **not** match its C or its prose intent. The body is now the clamped
   full-`dst` window replacement (`dc := min dstOff n`, `sc := min srcOff slen`,
   `lc := min len (min (n-dc) (slen-sc))`), matching the C; `blitBytes_spec` stays
   `rfl`. The C's clamps are overflow-stable (`copyLen > n - dstOff` etc., not
   `dstOff + copyLen > n`), and a new `benchSeamBoundaries` lane value-checks all
   three seams (`byteSlice`/`blitBytes`/`findByte`) on the out-of-range cases.
4. **F\* comparative audit** delivered as
   `openspec/changes/archive/2026-10-18-review-polish-proof-doc/fstar-comparison.md`,
   tabulating paper-vs-Lean-vs-F\* across `[D1]`–`[D8]`/`[S1]`–`[S6]`. Confirmed: the
   F\* `codec` is far more deviant (8-field `codec a` record, Z3-discharged
   roundtrip, `wfcv`/`rest_cond`, ASCII-only `text` `% 256`, Pulse layer) than the
   Lean port, which keeps the paper's `Iso`/`Rel` core.

`shipped-c-fast-path` is **archived as abandoned**
(`openspec/changes/archive/2026-10-18-shipped-c-fast-path/`) — its per-format C plan
was misguided (contradicts "all codecs pure-Lean, no per-format C").

## Critical review of the single-carrier change (COMPLETE)

The re-derivation is a proof-critical rewrite and was reviewed critically. The review
verified: (1) LEB128 byte-exactness by `#eval` (`0→[0]`, `128→[0x80,0x01]`, `300→[0xAC,0x02]`,
`127→[0x7F]`, `16384→[0x80,0x80,0x01]`, `624485→[0xE5,0x8E,0x26]`, overlong encodings rejected);
(2) `encodeVarint_eq`/`decodeVarint_eq` are intended `rfl` collapses and `decodeVarint`'s
whole-buffer form is acceptable; (3) `sepBy` is one-or-more and `chainl1`/`chainr1` keep
their operand list types; (4) every `_spec` law enumerates all prefixes (no dropped case);
(5) no dangling `Buffer`/`ByteArray`/`Array UInt8` references, and the root re-exports
exactly `Iso`/`Codec`/`Decode`/`Encode`/`Sound`/`Combinators`/`VarBinary`; (6) README is
single-carrier throughout; (7) `Bench.lean` scope matches spec 4.2. No unsound proof, no
vacuous antecedent, no `Classical.choice`, zero `sorry`. All new `decodeFull_*` laws are
`[propext, Quot.sound]`-only (`#print axioms Codec.decodeFull_spec`).

**Section-6 hardening (reviewer findings closed):** re-derived `decodeFull_some`/
`decodeFull_ne_none`/`decodeFull_spec` over the `Suffix` carrier (the dropped
`decodeFull_spec` full-consumption law is now proved, with the same uniqueness hypothesis
as its `List`-substrate predecessor), fixed the stale `ByteArray` docstring, added the
`decodeVarint` whole-buffer note, justified `relChainl1_cast`/`relChainr1_cast`, and
hardened the `Bench.lean` `decodeFull`/`decodeFast` checks. The toolchain is plain
nixpkgs `lean4` (clang 21).

(`single-carrier-bytes` is now **archived** as
`openspec/changes/archive/2026-10-17-single-carrier-bytes`.) The concrete-vector smoke checks
(`#eval varintBytes 300`, …) remain not-yet-permanent; they can become a test lane during the
`carrier-performance-tuning` gate (task 5.1).

## Openspec workflow

This repo uses OpenSpec (spec-driven). Changes live under
`openspec/changes/`. Planning artifacts (proposal / spec delta / design / tasks)
are created before implementation; see `.pi/prompts/opsx-*.md`.

**Consider every open OpenSpec change/proposal when forming or validating a new
plan.** Before authoring a new change's spec deltas (and before validating any
plan — new or in-flight), run `openspec list --json` to see _all_ active
(`in-progress`, `complete`-not-yet-archived) and open changes, and read their
spec deltas under `openspec/changes/<name>/specs/**` alongside the main specs
`openspec/specs/**`. Two changes that each clarify the _same_ requirement
(e.g. both MODIFY `codec`'s "Nondeterministic (backtracking) decoding") can add
_different_ scenarios to the same block; whichever syncs/archives first leaves
the other's MODIFIED block stale, and a MODIFIED requirement replaces the whole
block, so a later `openspec validate` flags the dropped scenario. Reconcile such
overlaps at planning/review time — carry every scenario into each delta's
MODIFIED block — rather than discovering the collision during archive. This
happened with `partial-remainder-fast-path` and `shipped-c-fast-path` (each
added a distinct third scenario to the same requirement).

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
  `pkgs.mkShellNoCC` **plus `pkgs.stdenv.cc`** — the Nix clang wrapper is added so
  `cc`/`clang`/`c++` resolve to a `libc++`-aware toolchain and `lake build bench`
  links in the dev shell, matching the `nix build .#bench` sandbox).
