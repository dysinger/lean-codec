# Proposal

## Why

The README says `codec` is **"one description, two directions"** — "a box with
two doors, `apply` and `unapply`." The _type_ delivers that idea (`Codec α`
drives both interpreters), but the `decode` surface went one step too far: it
returns the paper's nondeterministic `List (α × Suffix n)` (every parse), while
`encode` returns a single `Option (Σ n, Bytes n)`. The result is that the clean
law `decode (encode x) = x` is not even _stateable_ — `decode` is not a function
you can compose, so the roundtrip is `(x, []) ∈ decode d s` (an `∈`, over a
list), and the reverse direction (`encode_of_decode`) needs a `Functional d`
side-condition.

The paper's own API (PAPER.md §4.1–4.2) is the right model, and we take it
verbatim:

- `print :: Printer α → α → Maybe String` — encode is a **partial function**,
  `Maybe`, because a printer covers a subset of `α`.
- `parse :: Parser α → String → [α]` — the paper returns a _list_ (the list
  monad) and has **no error reporting** (failure is `[]`).

We keep the paper's `Option` for encode exactly as it is, and we make `decode`
a **single result** (`Option`) with **committed** `|` — matching the paper's own
printer-side `|` (`mplus`, first success), so the two directions are the two
doors of one `Iso`, each returning "a result or nothing." No error positions,
no new error type: this is the paper's API, cleaned up only to make `decode`
single-valued so the inverse law is an honest equality.

There are no real clients yet, so we cut the legacy `List` decoder outright
rather than preserve it.

## What Changes

1. **`decode` returns a single result.** `decode : Codec α → {n : Nat} → Bytes n
→ Option (α × Suffix n)` — committed `|` (first success), no `List`, no
   backtracking union.

2. **`encode` is unchanged.** `encode : Codec α → α → Option (Σ n, Bytes n)` —
   the paper's `print`, already correct.

3. **The inverse laws become equalities.** `roundtrip` is
   `encode d x = some ⟨n, s⟩ → decode d s = some (x, Suffix.empty n)`, and the
   converse `decode d s = some (x, []) → encode d x = some ⟨n, s⟩` is
   **unconditional** (no `Functional`/`Unambiguous`), because a single committed
   result has no ambiguity to gate.

4. **The relational `List` decoder and its band-aids are removed.**
   `Functional`, `Unambiguous`, `relFunctional`, `relUnambiguous` exist only
   because `decode` was a relation; with a single result they are unnecessary and
   are deleted.

5. **Concrete codecs become `Codec` values.** A concrete format is a `Codec …`
   composed from `byte`/`seq`/`iso`/`alt`/`many`, inheriting `encode`/`decode`
   (no per-format `encode`/`decode` with its own shape).

## Capabilities

### New Capabilities

- `codec`: a single-valued `decode` (`Option`), committed `|`, and the inverse
  laws as unconditional equalities.

### Modified Capabilities

- `codec`: "Nondeterministic (backtracking) decoding" becomes "deterministic
  single-result decoding" (committed `|`); the roundtrip/converse laws are
  re-spelled as `Option` equalities with no side-condition.

## Impact

- **API**: `decode` type changes `List` → `Option`; `encode` unchanged.
- **Proofs**: `roundtrip`/`decode_encode`/`encode_of_decode` re-derived as
  `Option` equalities; `Functional`/`Unambiguous` deleted; `[propext,
Quot.sound]`-only, zero `sorry`.
- **Consumers**: `Bench.lean` (codec and basen) switch to the single-result
  `decode`; concrete codecs become `Codec` values.
- **No substrate change**: `Bytes n` stays; no `CodecError`/position type is
  introduced (deferred until a client needs it).
