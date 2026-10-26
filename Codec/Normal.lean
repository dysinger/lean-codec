/- Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later -/

import Codec.Iso

/-!
# Normal forms: the information-free-variation layer

A binary format often accepts more than one concrete spelling of the same value:
RFC 4648 §8 requires a Base16 *decoder* to accept both `6F` and `6f`, because the
case of a hexadecimal digit carries no information. README `[D4]` answered the
paper's §3.1 remark ("the inverse invariant, read modulo equivalence classes") by
*capturing* a permitted run and re-emitting it verbatim, so that no `Iso` is
lossy. That conclusion is right, but its diagnosis was incomplete: the honest
object is not a relaxed law, it is a bijection with the **quotient of the concrete
syntax by the information-free variation**.

This module supplies that quotient as a *type*.

## The quotient lives in the object, not in the law

A partial isomorphism `Iso α β` (`Codec/Iso.lean`) is a bijection between two
types, with its inverse law carried as a **field**. Category theory puts a
quotient in the **object**; a relaxed law puts it in the **morphism** — and the
latter is exactly the prose invariant `[S1]` exists to abolish. So instead of
weakening `Iso.law` to hold "modulo equivalence classes", we name the quotient:

```
   Iso α (Normal S norm)
```

is an *ordinary* `Iso`, and every theorem about `Iso` — `Iso.trans`, `Iso.inverse`,
the roundtrip laws, `Unambiguous`, `Functional` — applies to it unchanged.

`Normal S norm` is the set of fixed points of `norm`, which for a total idempotent
`norm` is the quotient `S/~` where `s ~ t ↔ norm s = norm t`. Two facts make the
reification faithful rather than merely a subset, and both are proved below:
`fill nz s` reaches every normal form (`fill_surj`), and `norm` on a normal form is
the identity (`fill_fixed`).

## Why a subtype and not Lean's `Quotient`

`Quotient` is non-reducible: no law stated over it can be closed by `simp`/`rfl`,
and `Quot.sound` would enter the axiom gate of every law that touches it. For a
**decidable idempotent** `norm` the fixed-point subtype is definitionally the same
quotient, keeps the library's "reduce and compute" proof discipline, and stays
`[propext, Quot.sound]`-only (in fact these lemmas report `[propext]` or no
axioms).

## The laws: one on the arrow, one on the normalizer

This layer adds **no third law and weakens nothing**. `Iso.law` stays a field
holding unconditionally (untouched, in `Codec/Iso.lean`), and `Normalizer.idem`
states the normalizer is idempotent. The idempotence proof is carried in the
*structure*, not passed at each use: a per-call proof argument would make behaviour
depend on which witness a caller supplies, so two callers with different witnesses
for the same function would obtain only propositionally-equal results — the shape
`[S1]` exists to abolish.

`norm` is a **parameter** of `Normalizer`, not a projection field: with a
projection, `Normal S nz.norm` is opaque at the type level and every lemma needs a
cast; with a parameter, `Normal S norm` and `fill nz s` share one definitional
function.

## What this layer does NOT do

- **It is not an `Iso`.** `decodeNormal` is the normalizer composed *outside* an
  `Iso`. It has no inverse (`norm` is many-to-one), it accepts input the strict
  `Iso` rejects, and it must never be presented as a codec value or a combinator.
- **It does not touch `Unambiguous`/`Functional`.** Those are defined over
  `Codec α` (`Codec/Sound.lean`); this layer lives at the `Iso`, so there is no
  `Codec` for them to range over. The wrapper introduces no alternative results
  because `norm` is a *function* — that is a clarification of domain, not a
  theorem. Widening a decoder's input domain is constrained by the *canonicality*
  of encode, not by unambiguity.
- **It preserves length by construction.** The normal formats below are stated over
  an abstract `S`, but every intended instantiation is a single `Bytes n`, since
  `norm : Bytes n → Bytes n` cannot change the byte count. Case folding fits.
  Collapsing a whitespace run does **not**: three blanks to one is not a
  `Bytes n → Bytes n` map, and that variation needs a different carrier rather than
  a different normalizer. It is deliberately out of this layer's scope.
- **It keeps core free of domain leaves.** `[S3]` stands: this module is generic.
  The concrete ASCII fold lives downstream (`../lean-basen`).

## The obligation on a codec that uses this layer

`decodeNormal` on the encoder's own output reproduces the value **only if the
encoder emits a normal form** — `norm s = s` for the encoded `s`. That hypothesis
is not free: without it the wrapper can consume input the strict `Iso` accepted and
make decoding *fail* on its own encoder's output. It is a per-instance obligation,
stated and discharged by each codec (`decodeNormal_of_fixed` is the reusable step).
-/


namespace Codec

/-! ## The quotient -/

/-- The **normal forms** of a normalizer: the quotient `S/~` of a concrete syntax by
the variation `norm` treats as information-free, reified as the fixed points of
`norm`.

`s ~ t ↔ norm s = norm t`, and `normal`/'s `raw` projection exhibits the bijection
with `S/~` — `fill_surj` shows every normal form is reached, so this is a bijective
copy of the quotient, not merely a subset of `S`. -/
structure Normal (S : Type) (norm : S → S) where
  /-- The concrete string this normal form came from (and equals, by `fixed`). -/
  raw : S
  /-- The quotient witness: a normal form is unchanged by `norm`. -/
  fixed : norm raw = raw

/-- Extensionality for `Normal S norm`: two normal forms are equal when their
`raw` strings are. The `fixed` fields agree by proof irrelevance. -/
@[ext]
theorem Normal.ext {S : Type} {norm : S → S} {f g : Normal S norm} (h : f.raw = g.raw) :
    f = g := by
  cases f
  cases g
  simp_all

/-- A normalizer and the one law it owes: idempotence.

`norm` is a **parameter**, not a field, so `Normal S norm` is definitionally the
same type wherever it appears. The law is carried by the *type* rather than passed
at each use — a per-call proof argument would let behaviour depend on which witness
a caller supplies. -/
structure Normalizer (S : Type) (norm : S → S) where
  /-- `norm` fixes its own output, which is what makes the fixed points a quotient. -/
  idem : ∀ x, norm (norm x) = norm x

/-! ## The canonical representative -/

/-- `fill nz s` presents `s` as a normal form: the canonical representative of its
equivalence class. Its `fixed` field is the idempotence law, so `fill` needs no
other hypothesis. -/
def fill {S : Type} {norm : S → S} (nz : Normalizer S norm) (s : S) : Normal S norm :=
  ⟨norm s, nz.idem s⟩

@[simp]
theorem fill_raw {S : Type} {norm : S → S} (nz : Normalizer S norm) (s : S) :
    (fill nz s).raw = norm s := rfl

/-- `norm ∘ fill = id` on the quotient. This is the fixed-point witness, not a
separate law: the property the paper states informally ("modulo equivalence
classes") follows from idempotence alone.

Note the asymmetry, which is the content of the whole layer: `fill ∘ norm` is *not*
the identity, because `norm` forgets which spelling it was given. -/
theorem fill_fixed {S : Type} {norm : S → S} (nz : Normalizer S norm) (s : S) :
    norm (fill nz s).raw = (fill nz s).raw :=
  (fill nz s).fixed

/-! ## Faithfulness of the reification -/

/-- **`fill` is surjective onto the normal forms**: every normal form is the
canonical representative of its own class. Together with `fill_fixed` this shows the
fixed-point subtype is a bijective copy of the quotient `S/~`, not merely a
subset — the reification is faithful. -/
theorem fill_surj {S : Type} {norm : S → S} (nz : Normalizer S norm) (f : Normal S norm) :
    fill nz f.raw = f := by
  apply Normal.ext
  rw [fill_raw]
  exact f.fixed

/-- Two spellings occupy the same quotient class exactly when they normalise
equally. The usable form of "one class, many spellings". -/
theorem fill_inj {S : Type} {norm : S → S} (nz : Normalizer S norm) (s t : S) :
    fill nz s = fill nz t ↔ norm s = norm t := by
  constructor
  · intro h
    simpa using congrArg Normal.raw h
  · intro h
    apply Normal.ext
    simpa using h

/-! ## The normalising decoder (not an `Iso`) -/

/-- The **normalising decoder**: `norm` composed *outside* an ordinary
`Iso α (Normal S norm)`.

This is the lossy half of the layer and it is deliberately **not** an `Iso`: it has
no inverse, because `norm` is many-to-one. It accepts input the strict `Iso` itself
rejects — that is the entire point (RFC 4648 §8's "a decoder MUST accept both
cases"), and it is why it must never be presented as a codec value, a combinator,
or an inverse of the encoder.

It introduces no alternative results either: `norm` is a *function*, so one input
still yields at most one value. Widening the input domain is constrained by the
canonicality of `encode`, not by unambiguity. -/
def decodeNormal {S : Type} {α : Type} {norm : S → S} (nz : Normalizer S norm)
    (i : Iso α (Normal S norm)) (s : S) : Option α :=
  i.unapply (fill nz s)

/-- **The wrapper's law**, with its precondition: on an input that is already a
normal form, the wrapper agrees with the strict `Iso`. This is the reusable step for
the per-codec obligation below. -/
theorem decodeNormal_of_fixed {S : Type} {α : Type} {norm : S → S}
    (nz : Normalizer S norm) (i : Iso α (Normal S norm)) (s : S) (hfix : norm s = s) :
    decodeNormal nz i s = i.unapply ⟨s, hfix⟩ := by
  unfold decodeNormal
  rw [show fill nz s = ⟨s, hfix⟩ from Normal.ext (by simp [hfix])]

/-- **The obligation, and what it buys**: if the encoder emits a normal form
(`hfix`) and `apply` reaches it, the normalising decoder reproduces the value.

The hypothesis is *not* free and must be discharged per codec. Without it the
statement is false: `norm` applied before `unapply` can consume input the strict
`Iso` would have accepted, so a normalising decoder can fail on the encoder's own
output. This is the theorem that makes the layer useful — `fill_fixed` alone says
nothing about decoding. -/
theorem decodeNormal_encode {S : Type} {α : Type} {norm : S → S} (nz : Normalizer S norm)
    (i : Iso α (Normal S norm)) (x : α) (s : S) (hfix : norm s = s)
    (h : i.apply x = some ⟨s, hfix⟩) : decodeNormal nz i s = some x := by
  rw [decodeNormal_of_fixed nz i s hfix]
  exact (i.law x ⟨s, hfix⟩).1 h

end Codec
