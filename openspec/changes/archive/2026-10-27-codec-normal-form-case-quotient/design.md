# Design — `codec-normal-form-case-quotient`

## Context

See `proposal.md` — Why. The constraints, all already fixed by the library:

- **`Iso.law` is a field** (`Codec/Iso.lean:26`): `law : ∀ a b, apply a = some b ↔
unapply b = some a`. README `[S1]` exists to keep it that way.
- **`[D4]` answered the paper's §3.1 aside** by capturing a permitted run and
  re-emitting it verbatim, so no `Iso` is lossy. Its _conclusion_ is right; its
  _diagnosis_ is incomplete.
- **`Unambiguous`/`Functional`** (`Codec/Sound.lean:621`) are stated over a
  **`Codec`**, not over an `Iso`: `Unambiguous d := ∀ ⦃x y⦄ {n} (s : Bytes n),
Rel d x s → Rel d y s → x = y`. Anything built at the `Iso` layer is _outside_
  their scope — which matters for what may and may not be claimed (D4).
- **The spec substrate is single**: `Bytes n := Fin n → UInt8`. Any new type must
  not introduce a second carrier for the laws.
- **`Bytes n → Bytes n` is length-preserving.** This is the fact that makes case
  folding expressible and whitespace collapsing not (D6).
- **`Sound.roundtrip` already holds verbatim** (`encode d x = some ⟨n,s⟩ → (x,
empty) ∈ decode d s`); it does not, and cannot, say anything about a decoder that
  accepts spellings the `Iso` rejects (D3).

**Review provenance.** This design was reviewed adversarially before
implementation; D3, D5, D6, and D7 exist because that review found the first draft
had (a) omitted the only theorem that makes the layer useful, (b) smuggled the
idempotence hypothesis in as a per-call argument, (c) mislocated `Unambiguous`, and
(d) claimed whitespace support the carrier cannot provide.

## Goals / Non-Goals

**Goals:**

1. Name the information-free-variation layer in core so `basen` need not re-derive
   it, and so `[D4]` reads as "the identity case" rather than "the forbidden case".
2. Keep **one law on the arrow**. No existing field is weakened and no existing
   declaration changes shape.
3. State the layer's _useful_ theorem with its honest precondition (D3).

**Non-Goals:**

- No `Iso` relaxation, no `IsoMod`-style normed-equality law, no Lean
  `Quotient`/`Setoid` (D1).
- No new `Codec` constructor; the `Codec → Productive → Rel → Codec` impossibility
  is untouched, because `Normal` is a **type**, not a description node.
- No whitespace/case codec in core: `[S3]` (zero domain-specific leaves) stands.
  Core ships the generic normal-form type only; the concrete ASCII fold lives in
  `../lean-basen`.
- No length-changing normalisation (D6).
- No change to `decode`/`encode`/`Rel` or any proved law.

## Decisions

### D1 — The quotient is in the **object**, not in the law; reified as fixed points

```lean
structure Normal (S : Type) (norm : S → S) where
  raw   : S
  fixed : norm raw = raw        -- quotient witness, not a law to trust
```

`Normal S norm` is the type of `norm`'s fixed points, i.e. the quotient `S/~` for
`s ~ t ↔ norm s = norm t`, reified. `Iso α (Normal S norm)` is then an ordinary
`Iso` and every existing theorem applies verbatim.

_Why the fixed-point subtype is faithful:_ `fill := fun s => ⟨norm s, idem s⟩` is
surjective onto it (`fill f.raw = f`, D7), so the subtype is a bijective copy of the
quotient, not merely a subset. This direction is recorded as a lemma so the claim is
_shown_, not asserted.

_Alternatives rejected._ **`IsoMod` with a normed-equality law** — a second law,
re-introducing the prose invariant `[S1]` abolished. **Lean's `Quotient`** — not
reducible, so `simp`/`rfl` stop working and `Quot.sound` enters every law's gate,
for no gain over the subtype of normal forms, which is definitionally the same
quotient for a decidable idempotent `norm`. **Status quo (`norm = id`)** — correct
but refuses to model the layer.

### D2 — Totality and idempotence are carried by a **structure**, not by a proof argument

```lean
structure Normalizer (S : Type) where
  norm   : S → S
  idem   : ∀ x, norm (norm x) = norm x
  -- length-preservation is a per-instantiation fact (D6), stated where S = Bytes n
```

A first draft had `fill (h : ∀ x, drop (drop x) = drop x) s`. That is wrong: it
makes the wrapper's _behaviour_ depend on a proof argument, so two callers with
different witnesses for the same function produce `Normal`s that are only
propositionally equal — the exact shape `[S1]` exists to abolish, and it would let
a caller pass a witness for a `norm` that is not idempotent everywhere. Carrying
`idem` in the structure makes the laws part of the _type_. **This is a second law,
and the design says so plainly**: one law on the arrow (`Iso.law`, untouched), one
law on the normalizer (carried by `Normalizer`). There is no third.

### D3 — The wrapper's real theorem, with its precondition

```lean
def decodeNormal (i : Iso α (Normal S nz)) (s : S) : Option α :=
  i.unapply (fill nz s)
```

`Sound.roundtrip` still holds for the wrapped `Iso` and needs no restatement. But
the theorem a _user of the wrapper_ needs is different, and the first draft omitted
it:

> `norm (encode x) = encode x` (the encoder emits a normal form) **implies**
> `decodeNormal (encode x) = some x`.

Without the hypothesis this is **false**: `norm` applied before `unapply` can
consume input the strict `Iso` would have accepted, so normalising before decoding
can make `decodeNormal (encode x)` _fail_ where `decode (encode x)` succeeds. The
hypothesis is therefore an **obligation on every codec that uses the layer**, not a
free fact, and the spec states it as such. (For `basen`'s hex it is discharged by
"the encoder emits uppercase", which is already a proved canonicality law.)

### D4 — `Unambiguous` does not apply here; do not claim a theorem for a tautology

`Unambiguous`/`Functional` are stated over `Codec α` (`Sound.lean:621`).
`decodeNormal` takes an `Iso α (Normal S norm)` — there is no `Codec` in sight, so
those predicates are **outside** this layer's scope. The claim "folding case does
not break `Unambiguous`" is true, but it is true because the wrapper is not a
`Codec` at all, and because `norm` is a _function_ (total, single-valued) and so
introduces no alternative results. It is _not_ a theorem to prove; the first draft
wrongly listed it as one. The spec records it as a _clarification of domain_ — the
constraint a normalising decoder must respect is the **canonicality of encode**,
not unambiguity. This also corrects `basen-rfc-conformance-theorems` task 7.3's
false attribution.

### D5 — The obligation is "encode emits a normal form", not "`norm` commutes with `concat`"

The first draft (D5 there) worried about `norm (concat s₀ s₁) = concat (norm s₀)
(norm s₁)`. That is the wrong obligation for this layer: the wrapper normalises the
_whole_ input before `unapply`, so no per-component commutation is required, and
demanding it in the structure would exclude legitimate normalizers. The obligation
that actually matters is D3's — `norm (encode x) = encode x` — and it is per
instance.

### D6 — Length-preserving only; whitespace is explicitly out of scope

`Bytes n := Fin n → UInt8`, so `norm : Bytes n → Bytes n` cannot change the byte
count. Case folding fits; **collapsing a whitespace run does not** — three blanks
to one is not a `Bytes n → Bytes n` map. The first draft claimed
`lean-text`'s `skipSpace`/`optSpace`/`sepSpace` would follow; that claim was false
and is withdrawn. Whitespace would need a different carrier (e.g. `List UInt8`),
and the single-substrate rule is not being reopened here. The spec says this
outright so no future reader assumes it is an oversight.

_This is a scope cut, not a loss:_ formatting is presentation, not information — an
AST should not carry whitespace-run length any more than it should carry the case
of a digit. The layer's right scope is exactly the variation that carries no
information _and_ preserves length.

### D7 — `fill` is surjective onto the normal forms

`fill nz f.raw = f` for every `f : Normal S nz` (both sides `raw`-equal, then
`Normal.ext`). This is what makes "the fixed-point subtype faithfully reifies the
quotient" a _lemma_ rather than a slogan, and it closes the review's point that
surjectivity was asserted but not shown.

### D8 — `[D4]` amended, not repealed, and its wording corrected

The conclusion stays (no `ignore`; the law holds unconditionally) and the diagnosis
is sharpened. The first draft said "`ignore` is the `drop` half of an `Iso α
(Normal S drop)`" — that is **wrong**, and the corrected statement is: `ignore ::
α → Iso α ()` is an `Iso` _value_, so it cannot be a lossy `Iso`; what models the
whitespace/formatting loss is `decodeNormal`-shaped, with the normalizer **outside**
an `Iso`. The README amend must use that wording, not the draft's.

## Risks / Trade-offs

- **Downstream forgets D3's hypothesis** → spec requirement "Decoding the encoder's
  own output still succeeds" makes it a conformance obligation, and the downstream
  task names it explicitly.
- **`Normal.ext`/subtype equality leaking `Classical.choice`** → prove `raw`-equality
  lemmas explicitly (`rw`, not `simp at`); gate each new law in the build
  (AGENTS: the `Classical.choice` trap).
- **Scope creep toward a domain leaf** → core ships only the generic type; `[S3]`
  holds.
- **A second carrier sneaks in** → `Normal S norm` is a subtype of the existing
  `S`; D6 explicitly refuses length-changing normalisation rather than widening the
  carrier.
- **`Normal` read as "normalized text"** → the docstring cites the byte-level
  meaning and the rewriting-systems term ("normal forms"); no text vocabulary.
- **Scope-cut regret when whitespace is needed** → recorded in D6 as a carrier
  question with a named prerequisite, so it is a deliberate boundary, not a gap.

## Migration Plan

Additive only: land `Codec/Normal.lean`, re-export from `Codec.lean`, gate the new
laws, amend README `[D4]`. Nothing existing changes, so no downstream repo needs to
change to keep compiling. `../lean-basen` task 7.3 becomes newly possible and is
tracked there.

## Open Questions

None that change the artifacts. The choices that could have — quotient in the object
vs. relaxed law (D1), laws in a structure vs. a proof argument (D2), the wrapper's
precondition (D3), and the whitespace scope cut (D6) — are settled, and the shape is
verified to compile and gate clean (tasks 0.1).
