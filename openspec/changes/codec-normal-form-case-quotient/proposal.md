# Proposal

## Why

`codec` has no way to say "these bytes carry no information". A binary format
often accepts more than one concrete spelling of the same value — RFC 4648 §8
requires a Base16 _decoder_ to accept both `6F` and `6f`, because case carries no
information in hex — but a `Codec` value cannot express that: `hexElem` is a strict
uppercase bijection, so lowercase `6f` is simply rejected.

`../lean-basen` records this as a non-goal (task `7.3` of
`basen-rfc-conformance-theorems`) and attributes it to `Unambiguous`. That
attribution is **false**: `Unambiguous` (`Codec/Sound.lean:621`) quantifies over
one input yielding at most one value, and folding case before decoding does not
change that. The divergence therefore rests on a wrong reason, and the RFC
requirement it waives is a MUST.

The paper (PAPER.md §3.1) says the inverse law may be read _"modulo equivalence
classes"_. `codec` answered with `[D4]`: because `Iso.law` is a field, a lossy
combinator cannot inhabit `Iso`, so a permitted run is captured and re-emitted
verbatim. That answer is right in its conclusion and incomplete in its diagnosis:
the honest object is a bijection with the **quotient of the concrete syntax by the
information-free variation** — a quotient in the _object_, which is where category
theory puts it, not a relaxed law in the _morphism_, which is what `[S1]` exists to
abolish.

**Why now:** a standards MUST is currently waived on a false rationale, and the fix
is a small generic type rather than a relaxation of anything.

## What Changes

- **ADD a `Normal` type to core**: the quotient of a concrete byte string by a
  total idempotent, length-preserving normalizer `norm`, reified as the _subtype of
  fixed points_ with a `Normalizer` structure carrying totality and idempotence —
  not a per-call proof argument. `Iso α (Normal S norm)` is then an **ordinary
  `Iso`**: `law` stays a field, no relaxation, no second law on the arrow.
- **ADD the canonicalising decoder as a named, non-`Iso` wrapper**: `norm`
  composed **outside** an `Iso`. It is a total function applied before `unapply`,
  so it cannot affect `Unambiguous` or `Functional`, and it cannot be mistaken for
  an inverse (it has none).
- **ADD the law that makes the layer useful** — the one a design that only says
  "`drop ∘ fill = id`" forgets:
  `norm (encode x) = encode x → decodeNormal ... = some x`. A downstream codec
  **owes** the hypothesis "the encoder emits a normal form"; without it, `norm`
  applied before `unapply` can make decoding _fail_ on the encoder's own output.
  This is a per-instance obligation, stated as such.
- **MODIFY the "capture verbatim" requirement** to record that capture-and-re-emit
  is the `norm = id` degenerate case of this layer, and that **formatting is not
  semantic**: an AST must not carry presentation (whitespace-run length, leading
  zeros, case), so a codec MAY expose a normalising decoder over a normal form
  instead of preserving the spelling.
- **Not a breaking change**: no existing declaration changes shape. `Iso`, `Codec`,
  `decode`, `encode`, `Rel`, `Unambiguous`, `Functional` and every proved law are
  untouched; `Normal` is additive and used by no existing base.

## Capabilities

### New Capabilities

- `codec/normal-form`: the information-free-variation layer — the `Normal`
  quotient type (fixed points of a total, idempotent, length-preserving
  normalizer), the `Normalizer` structure that carries those laws, `fill` as the
  canonical representative, `drop ∘ fill = id` as a `rfl`, and the discipline that
  a normalising decoder is `norm` composed outside an ordinary `Iso`.

### Modified Capabilities

- `codec`: the requirement "Any run of bytes a codec's predicate permits SHALL be
  captured as part of the decoded value and re-emitted verbatim on encode; no byte
  SHALL be silently discarded" is clarified — capture-verbatim is the identity
  normalizer, not a prohibition on having a normal form, and a codec MAY instead
  expose a normalising decoder provided the lossy step is a total idempotent
  length-preserving `norm` applied outside the `Iso`, and the encoder is proved to
  emit a normal form.

## Impact

- **Code (positive)**: new `Codec/Normal.lean` (the `Normal` type, the `Normalizer`
  structure, `fill`, `Normal.fixed`/`Normal.ext`, `fill_surj`, and the wrapper with
  its law), re-exported from `Codec.lean`. Pure Lean, no C,
  `[propext, Quot.sound]`-only, zero `sorry`. The shape is **already verified to
  compile and gate clean** in a `/tmp` probe against the built library.
- **Code (none)**: no change to `Iso`, `Codec`, `Decode`, `Encode`, `Sound`,
  `Combinators`, `Packed`, `DecodeOne`, or the Layer-2 trust seam. No new `Codec`
  constructor — `Normal` is a _type_, so the `many`-as-constructor impossibility is
  untouched.
- **Scope: length-preserving normalizers only.** `Bytes n := Fin n → UInt8`, so a
  `norm : Bytes n → Bytes n` can fold case but **cannot** collapse a whitespace
  run. Case folding is in scope; **length-changing normalisation is not** and is
  not promised here (see design D6 — it would need a different carrier, and the
  single-substrate rule is not up for grabs in this change).
- **Docs**: `README.md` `[D4]` sharpened (conclusion kept, diagnosis corrected);
  `CHANGELOG.md` entry.
- **Downstream (not in this change)**: `../lean-basen` gains RFC 4648 §8 (Base16
  accepts both cases) as `norm = ASCII fold` over its existing uppercase `Iso`,
  plus the "encoder emits uppercase" obligation. That closes
  `basen-rfc-conformance-theorems` task `7.3` and replaces its false
  `Unambiguous` rationale. Tracked there, not here.
- **No substrate, carrier, or axiom-discipline change**: still pure Lean, still
  `Bytes n`, still `[propext, Quot.sound]`.
