/- Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later -/

/-
# codec

A verified, byte-exact, bidirectional codec library for Lean 4.

See the repository `README.md` for the full design; this module aggregates the
library's components:

  * `Codec.Iso` — partial isomorphisms with the inverse law as a field
  * `Codec.Codec` — the description interface over bytes, plus `Rel`
  * `Codec.Decode` — the nondeterministic (backtracking) decoder
  * `Codec.Encode` — the partial encoder
  * `Codec.Sound` — the bidirectional and roundtrip laws
  * `Codec.Combinators` — derived combinators (`many`, `*>`, `<*`, …)
  * `Codec.Normal` — normal forms: the information-free-variation layer
-/

import Codec.Iso
import Codec.Codec
import Codec.Decode
import Codec.Encode
import Codec.Sound
import Codec.Combinators
import Codec.Normal
import Codec.Packed
import Codec.ByteSlice
import Codec.DecodeOne
