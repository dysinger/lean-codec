import Lake
open Lake DSL
open System

/- Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later -/

package codec

-- The hand-written, trusted C fast path (`Codec/ExternFastPath.c`) backing the
-- `@[extern]` primitives in `Codec/ExternFastPath.lean`. Compiled to an object
-- file with the Lean toolchain's C compiler (`leanc`, which carries the
-- `lean/lean.h` include path and matching C flags) and linked into the `bench`
-- executable via `moreLinkObjs`.
target externFastPathO (pkg) : FilePath := do
  let oFile := pkg.buildDir / "ExternFastPath.o"
  let srcFile := pkg.dir / "Codec" / "ExternFastPath.c"
  buildLeanO oFile (Job.pure srcFile)

@[default_target]
lean_lib codec where
  roots := #[`Codec]

lean_exe bench where
  root := `Bench
  moreLinkObjs := #[externFastPathO]
