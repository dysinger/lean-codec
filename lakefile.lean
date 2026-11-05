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
error. It is a `@[default_target]` lib (mirroring `../lean-basen/Axioms.lean`, which
is where this shape is proven in this ecosystem) because that is what makes the gate
ride on `lake build` instead of on someone remembering to run it.

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
  moreLinkObjs := #[byteSliceO, cRefO]
