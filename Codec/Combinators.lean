/- Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later -/

import Codec.Codec

/-!
# Derived combinators

Generic, byte-agnostic combinators built from the primitives (the paper §6.1):

  * `many p` — zero or more, the paper's `many` (§3.4)
  * `p *> q`, `p <* q` — pair variants that ignore a side (the paper's `*>`, `<*`)
  * `between open close p` — `open *> p <* close`

`many` is recursive and hence `partial`; it introduces committed `alt`, so it is
outside the `NoAlt` fragment for which the roundtrip law holds unconditionally
(see `Codec.Sound`). `chainl1` is deferred: it needs `foldl`/`iterate`
(paper §5.2/§5.3), the coinductive `Iso` combinators not yet in `Codec.Iso`.
-/

namespace Codec

open Iso

/-- `p *> q` parses/prints `p` then `q`, keeping only `q` (ignoring `p`'s `()`).
`p * q : Codec (Unit × α)`, mapped by `commute ≫ inverse unit : Iso (Unit × α) α`. -/
def seqRight {α : Type} (p : Codec Unit) (q : Codec α) : Codec α :=
  Codec.iso (Iso.commute ≫ Iso.inverse (Iso.unit)) (Codec.seq p q)

/-- `p <* q` parses/prints `p` then `q`, keeping only `p` (ignoring `q`'s `()`).
`p * q : Codec (α × Unit)`, mapped by `inverse unit : Iso (α × Unit) α`. -/
def seqLeft {α : Type} (p : Codec α) (q : Codec Unit) : Codec α :=
  Codec.iso (Iso.inverse (Iso.unit)) (Codec.seq p q)

/-- `between open close p` is `open *> p <* close`. -/
def between {α : Type} (l r : Codec Unit) (p : Codec α) : Codec α :=
  seqRight l (seqLeft p r)

/-- `many p` describes a list: either empty, or one `p` followed by `many p`
(the paper's `many`, §3.4). Recursive, hence `partial`. -/
partial def many {α : Type} (p : Codec α) : Codec (List α) :=
  Codec.alt (Codec.iso (Iso.nil) (Codec.pure ()))
    (Codec.iso (Iso.cons) (Codec.seq p (many p)))

end Codec
