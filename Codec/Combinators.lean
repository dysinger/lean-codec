/- Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later -/

import Codec.Codec

/-!
# Derived combinators

Generic, byte-agnostic combinators built from the primitives (the paper §6.1):

  * `many p` — zero or more, the paper's `many` (§3.4)
  * `p *> q`, `p <* q` — pair variants that ignore a side (the paper's `*>`, `<*`)
  * `between open close p` — `open *> p <* close`

`many` is recursive and hence `partial`. Under the nondeterministic (backtracking)
decoder it is sound *unconditionally* — exactly the paper's `many` (§3.4): `decode
(many p) s` returns the empty-list result *and* every one-or-more result, so the
bidirectional law holds without any prefix-disjointness gate. `chainl1` (below) is
built on the proved `Iso.foldl` (paper §5.2/§5.3); its `law` is part of
`Iso.foldl`'s law field, not a separate proof.
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

/-- `chainl1 arg op f` parses/prints a *non-empty* left-associative chain of
`arg` separated by `op`, folding left via the step iso `f : Iso (α × (β × α)) α`
(the paper's `chainl1`, §6.1). Built on `Iso.foldl`; `measure`/`h` are the
well-foundedness witness (see `Iso.MeasureDecreases`). -/
noncomputable def chainl1 {α β : Type} (arg : Codec α) (op : Codec β)
    (f : Iso (α × (β × α)) α) (measure : α → Nat)
    (h : Iso.MeasureDecreases measure f) : Codec α :=
  Codec.iso (Iso.foldl f measure h) (Codec.seq arg (many (Codec.seq op arg)))

end Codec
