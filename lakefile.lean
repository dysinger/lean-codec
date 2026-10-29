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

lean_exe bench where
  root := `Bench
  moreLinkObjs := #[byteSliceO]
