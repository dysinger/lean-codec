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
  **active change is `carrier-performance-tuning`** (profiling done, law-backed
  bulk fast path next) — consult
  `openspec/changes/carrier-performance-tuning/tasks.md` for the current task
  status and next steps. History ("we used to / reverted / this session")
  belongs in that ledger, **never** in this file or the README.
  (`single-carrier-bytes` is archived as
  `openspec/changes/archive/2026-10-17-single-carrier-bytes`.)
- **Library source (module `Codec`):** `Codec/`.
  - `Iso.lean` — partial isomorphisms + folded combinators (`foldl`/`foldr`).
  - `Codec.lean` — the description AST, the length-indexed substrate `Bytes n`,
    `Rel`/`relRepeat`, and the substrate/cast-commutation lemma library.
  - `Decode.lean` / `Encode.lean` — the backtracking decoder and partial encoder.
  - `Sound.lean` — the bidirectional + roundtrip laws (unconditional).
  - `Combinators.lean`, `VarBinary.lean` — derived combinators and LEB128 varint.
- **Executable/bench:** `Bench.lean`, wired through `lakefile.lean` and Nix
  `default.nix`/`flake.nix`.

## Active work (single carrier — archived; now `carrier-performance-tuning`)

The core (`Codec`/`Decode`/`Encode`/`Sound`/`Combinators`/`VarBinary`) is
**re-derived over the single length-indexed substrate `Bytes n := Fin n → UInt8`**,
`[propext, Quot.sound]`-only (no `Classical.choice`, zero `sorry`). The old transfer-tier
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
`ofFn_concat`/`pushBytesFrom_eq` are **done** in `Codec/Encode.lean` (uncommitted, all
`[propext, Quot.sound]`-only — the earlier `toArray.toList` `Classical.choice` blocker is
resolved by reading back as a pure `List.ofFn`, see the `lean` skill 2026-10-17 entries).
`Codec/Packed.lean` now holds the **packed carrier definitions** (`decodeArray`,
`decodeFullArray`, `encodeArray`, `encodeByteArrayBytes`, `consumedAbs`, and the
`decodeArray_bounded` monotone invariant) — all building, `[propext, Quot.sound]`-only,
zero `sorry`. **The four refinement laws are still open**: `decodeArray_eq`,
`decodeFullArray_spec`, `encodeArray_eq`, `encodeByteArrayBytes_eq`.

**Two binding decisions, already made (do not re-litigate):**

1. **Cursor is `Nat`, not `USize`.** `USize`'s `+` is `Nat`-addition modulo `2^64` and
   `USize.size = 2^64` needs the unproven platform fact `System.Platform.numBits = 64`,
   so a `USize`-cursor refinement cannot close `[propext, Quot.sound]`-only. `Nat` is the
   proof/runtime carrier (same as `fastEncodeRepeat`). The "`USize` lowers to `size_t`"
   claim is settled by IR inspection (task 3.1), never by typing the cursor `USize`.
2. **Speed-run the implementation; gate _provability_ before volume.** Write the
   executable definitions first (keep `lake build` green with `sorry` placeholders
   temporarily), but run a one-case `#print axioms` spike _before_ committing to a
   carrier/readback shape (the cheapest way to learn a type leaks `Classical.choice`
   or a platform premise). The throwaway work should be the _implementation_, never a
   whole proof built on an unprovable carrier.

**Concrete order for next session:**

1. **Spike the encode readback inversion** (the one thing that stalled this session):
   prove `arr.toList = List.ofFn s → ⟨arr.size, fun i => arr[i]⟩ = ⟨n, s⟩` (or the
   `Array`-`ofFn`-clean equivalent) closes `[propext, Quot.sound]`-only. If clean, the
   encode refinements (`encodeArray_eq`, `encodeByteArrayBytes_eq`) each fall out in one
   induction using `ofFn_concat` + `Array.toList_append`/`List.append_toArray`.
2. **Prove `encodeArray_eq` / `encodeByteArrayBytes_eq`** (List-level readback form
   `(encodeArray d x).map (·.toList) = (encode d x).map (List.ofFn ∘ snd)`), gated by
   `#print axioms`.
3. **Prove the decode bridge** — the from-scratch `Suffix`-transport (`decode_cast`,
   `decode` insensitive to `cast (congrArg Bytes e) s`) — then `decodeArray_eq` and
   `decodeFullArray_spec`.
4. **Task 3.1 IR inspection** — cite the emitted `.c` (`.lake/build/ir/Codec/Packed.c`)
   to record whether the `Nat` cursor lowers to `size_t`/bignum, honestly; mark the
   "no backend"/"scalar index" premise true or false per the actual IR.
5. **Tasks 4.x / 5.x** — the `@[extern]` `byteSlice` trust seam, then bench + gate.

Reads/`decode` stay on `Bytes n`; **only the packed carrier + bulk shapes get the
contiguous-buffer fast path, proved equal to the spec.** Read the change's own
`openspec/changes/carrier-performance-tuning/tasks.md` session log for the finer log.

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
