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
  **active change is `single-carrier-bytes`** — consult
  `openspec/changes/single-carrier-bytes/tasks.md` for the current task status and
  next steps. History ("we used to / reverted / this session") belongs in that
  ledger, **never** in this file or the README.
- **Library source (module `Codec`):** `Codec/`.
  - `Iso.lean` — partial isomorphisms + folded combinators (`foldl`/`foldr`).
  - `Codec.lean` — the description AST, the length-indexed substrate `Bytes n`,
    `Rel`/`relRepeat`, and the substrate/cast-commutation lemma library.
  - `Decode.lean` / `Encode.lean` — the backtracking decoder and partial encoder.
  - `Sound.lean` — the bidirectional + roundtrip laws (unconditional).
  - `Combinators.lean`, `VarBinary.lean` — derived combinators and LEB128 varint.
- **Executable/bench:** `Bench.lean`, wired through `lakefile.lean` and Nix
  `default.nix`/`flake.nix`.

## Active work (single carrier)

The core (`Codec`/`Decode`/`Encode`/`Sound`/`Combinators`/`VarBinary`) is
**re-derived over the single length-indexed substrate `Bytes n := Fin n → UInt8`**,
`[propext, Quot.sound]`-only (no `Classical.choice`, zero `sorry`). The old transfer-tier
modules (`DecodeArray`/`EncodeArray`/`DecodeByteArray`/`EncodeByteArray`/
`DecodeByteArraySlice`/`EncodeByteArraySlice`/`ExternFastPath`/`Buffer`) are
**deleted**, the `lakefile.lean` extern target is dropped, and `Bench.lean` is a
single `Bytes`-substrate lane. `single-carrier-bytes` is **14/14 tasks complete, green**
(`lake build` zero `sorry`/warnings, `#print axioms Codec.roundtrip` = `[propext, Quot.sound]`,
`nix build .#checks.aarch64-darwin.lean .#bench` both green).

The change is **implemented but not yet critically reviewed / archived** — see
[Next: critical review](#next-critical-review-of-the-single-carrier-change).

Axiom discipline: every law must stay `[propext, Quot.sound]`-only. `#print axioms
Codec.roundtrip` is the check.

## Next: critical review of the single-carrier change

The re-derivation is green, but it is a **proof-critical rewrite** and must be reviewed
critically before archive. Review in this order (expensive/most-fragile first):

1. **`Codec/VarBinary.lean` backward (`enc_dec`/`varintUnapply_inj`) — the fragile part.**
   The `Sigma.ext` + `heq_of_eq`/`cast_heq`/`HEq.trans` reconstruction over the
   length-indexed carrier is subtle. Re-verify byte-exactness against concrete LEB128
   vectors — `varintBytes 0 = ⟨1, [0]⟩`, `128 → [0x80, 0x01]`, `300 → [0xAC, 0x02]` — via
   `#eval`/`#reduce`, _not_ just the roundtrip theorem. Confirm the `varint` is still
   `Iso Nat (Σ k, Bytes k)` with the SAME denotation as the old `Iso Nat (List UInt8)`
   (the carrier changed; the map `n ↦ canonical bytes` must not).
2. **`encodeVarint_eq`/`decodeVarint_eq` became `rfl` aliases.** The old versions were
   meaningful carrier-refinement lemmas; the new `encodeVarint = varintBytes` and
   `decodeVarint = varintUnapply` are definitional. Confirm this is the intended
   single-carrier collapse (no lost guarantee), and that `decodeVarint` losing the old
   absolute-offset `a i` argument (now whole-buffer) is acceptable — the old API could
   decode _at_ an offset; the new one consumes a whole `Σ k, Bytes k`.
3. **`Codec/Combinators.lean` list-combinator laws keep their _semantics_.** Confirm
   `relSepBy`/`decodeSepBy`/`encodeSepBy` still mean "head `p`, then many `(sep *> p)`"
   (one-or-more, empty list `= False`), and `relChainl1`/`relChainr1` still use
   `foldl`/`foldr` over `relRepeat (Rel (seq op arg))` with the operand list at the right
   type (`List (β × α)` for `chainl1`, `List (α × β)` for `chainr1`). The new
   `relChainl1_cast`/`relChainr1_cast` (`cases e; rfl`) are axiom-clean but trivially
   correct only if the relations are genuinely cast-invariant — eyeball that.
4. **Completeness of the `_spec` laws (forward direction).** `decodeSepBy_spec`/
   `decodeChainl1_spec`/`decodeChainr1_spec` enumerate _all_ prefixes; a subset bug reads
   green but is wrong. Re-run `#print axioms` on each new law (not just `roundtrip`), and
   sanity-check the `List.mem_flatMap`/`mem_filterMap` destructuring didn't drop a case.
5. **Deletion completeness.** Grep `Codec/` and `Bench.lean` for any dangling `Buffer`/
   `ByteArray`/`Array UInt8`/`DecodeArray`/`encodeByteArrayBytes`/`decodeVarint … i
(old-signature) reference; confirm the root `Codec.lean`re-exports exactly`Iso`,
`Codec`, `Decode`, `Encode`, `Sound`, `Combinators`, `VarBinary`.
6. **README/AGENTS/doc consistency.** Verify the README no longer claims a two-tier
   `List ✓ spec + ByteArray run-model` anywhere (stale fragments may remain past the
   sections edited this session), and that the `[D1]` anchor's link target
   (`#representations-one-length-indexed-byte-string`) resolves.
7. **`Bench.lean` scope.** Confirm dropping all array/byte-array/slice/extern lanes is
   exactly what the spec's 4.2 requires (it is), and that the surviving lanes
   (scalar-index read, empty-remainder roundtrip, encode length) still exercise the hot
   paths meaningfully.

Once reviewed, archive `single-carrier-bytes` (`/opsx-archive`) and decide whether the
concrete-vector smoke checks (`#eval varintBytes 300`, …) deserve a permanent test lane.

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
