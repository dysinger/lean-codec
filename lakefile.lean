import Lake
open Lake DSL
open System

/- Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later -/

package codec

@[default_target]
lean_lib codec where
  roots := #[`Codec]

/-- Compile the Layer-2 trust seam C (`Codec/ByteSlice.c`) into an object file.
The `@[extern "codec_byteSlice"]` primitive is linked only into the `bench`
executable (the packed path that consumes it), never into the proven library. -/
target byteSliceO (pkg) : FilePath := do
  let oFile := pkg.buildDir / "ByteSlice.o"
  let srcFile := pkg.dir / "Codec" / "ByteSlice.c"
  buildLeanO oFile (Job.pure srcFile)

/-- Compile the varint-span trust seam C (`Codec/VarintFast.c`) into an object file.
Same shape as `byteSliceO`: linked only into the `bench` executable, never the
proven library. -/
target varintFastO (pkg) : FilePath := do
  let oFile := pkg.buildDir / "VarintFast.o"
  let srcFile := pkg.dir / "Codec" / "VarintFast.c"
  buildLeanO oFile (Job.pure srcFile)

/-- Compile the numeric-parse trust seam C (`Codec/NumParse.c`) into an object file. -/
target numParseO (pkg) : FilePath := do
  let oFile := pkg.buildDir / "NumParse.o"
  let srcFile := pkg.dir / "Codec" / "NumParse.c"
  buildLeanO oFile (Job.pure srcFile)

lean_exe bench where
  root := `Bench
  moreLinkObjs := #[byteSliceO, varintFastO, numParseO]
