import Lake
open Lake DSL
open System

/- Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later -/

package codec

@[default_target]
lean_lib codec where
  roots := #[`Codec]
  /- The proof gate, made real. `lake build` only *warns* on `sorry`
  (`declaration uses 'sorry'`), so a plain build goes green with an incomplete
  proof. `-DwarningAsError=true` promotes that warning to an error, making the
  **compiler** the authority instead of a parallel `sorry` lint that could drift
  (`admit`, a tactic-generated `sorryAx`, ...). This is what lets `AGENTS.md`
  call zero-`sorry` *enforced* rather than *observed*; it applies to every path
  that compiles the library, including `checks.lean`. -/
  moreLeanArgs := #["-DwarningAsError=true"]

/-- The axiom gate, made real — the other half of the proof gate above.

`-DwarningAsError` catches `sorry`; nothing else in a plain build collects **axioms**,
so a law that silently drifted to depend on `Classical.choice` would go unnoticed
until a reader chose to check it. `Axioms.lean` pins every public theorem's exact
`#print axioms` output with `#guard_msgs`, so a footprint regression is a build
error. It is a `@[default_target]` lib because that is what makes the gate ride on
`lake build` instead of on someone remembering to run it.

**On the direction this pattern travelled.** `../lean-basen` originated the *shape*
(a `@[default_target]` `Axioms` lib), and this file inherited it. The *mechanism* is
the other way round: `lean-codec`'s two audit rounds added the environment walk
(`publicTheorems` / `partitionInto`) plus the `partition` and `gateCoverage`
`run_cmd` checks, which make an un-gated law a **build failure** instead of a gap a
maintainer has to notice. `../lean-basen` carried 440 hand-written `#guard_msgs`
blocks with no `run_cmd` and no partition until `codec-audit-round-three` §1.0
ported this mechanism back to it. An earlier revision of this comment said basen
"is where this shape is proven in this ecosystem", which read as though the
weaker version were the reference — it is not. Copy the mechanism, not just the
lib shape.

The `warningAsError` flag is set for the same reason as on `codec`: the gate must
not be satisfiable by an unproven law, so a `sorry` reaching it has to fail too. -/
@[default_target]
lean_lib Axioms where
  roots := #[`Axioms]
  moreLeanArgs := #["-DwarningAsError=true"]

/-- Compile the Layer-2 trust seam C (`Codec/ByteSlice.c`) into an object file.
The `@[extern "codec_byteSlice"]` primitive is linked only into the `bench`
executable (the packed path that consumes it), never into the proven library. -/
target byteSliceO (pkg) : FilePath := do
  let oFile := pkg.buildDir / "ByteSlice.o"
  let srcFile := pkg.dir / "Codec" / "ByteSlice.c"
  buildLeanO oFile (Job.pure srcFile)

/-- Compile the **benchmark-only C reference parser** (`Codec/CRef.c`) into an
object file.

This is *not* a Layer-2 trust seam and is **not** part of the `#print axioms`
gate: nothing in the proven library calls it, it carries no `@[extern]`
primitive, and the library stays pure Lean. It exists only so the bench can
measure a hand-written C parser over the same bytes as the Lean decoder, which
`AGENTS.md` names as the honest reference for a per-element codec (a `memcpy`
ratio is a category error). Linked into `bench` only. -/
target cRefO (pkg) : FilePath := do
  let oFile := pkg.buildDir / "CRef.o"
  let srcFile := pkg.dir / "Codec" / "CRef.c"
  buildLeanO oFile (Job.pure srcFile)

lean_exe bench where
  root := `Bench
  /- **The exe root sets its own flag** (`codec-audit-round-nine` §1.8).
  `-DwarningAsError` on a `lean_lib` rides on the modules that lib *compiles*, so
  `codec` and `Axioms` are covered — but `Bench.lean` is an `lean_exe` root, not a
  module of either, so a `sorry` in its own theorems (`foldNorm_idem`, `foldNz`) was
  a **warning** and the lane still went green. An exe is a separate root and its
  options are its own; `AGENTS.md`'s "including `bench`" was an over-read of this
  (corrected there in §8.2). Set here, so the bench's proofs are enforced by the
  compiler for the same reason the library's are. -/
  moreLeanArgs := #["-DwarningAsError=true"]
  moreLinkObjs := #[byteSliceO, cRefO]
