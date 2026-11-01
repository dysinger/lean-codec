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
