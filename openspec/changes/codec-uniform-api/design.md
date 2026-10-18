# Design

## Context

See `proposal.md` — Why. `codec` is a description-of-an-isomorphism built from
`Iso α β` (`apply : α → Option β`, `unapply : β → Option α`, inverse `law`).
The client API is the two doors of that iso. The paper (PAPER.md §4) implements
the two doors with _different_ result shapes: parsing is
`Parser (String → [(α, String)])` (a list), printing is
`Printer (α → Maybe String)` (partial). We adopt the paper's shapes, and make one
narrow correction: `decode` returns a **single** `Option` result (committed `|`),
not a list, so that `decode ∘ encode = id` is an honest equality.

There are no real clients yet, so the relational `List` decoder is removed, not
kept as a substrate.

## Goals / Non-Goals

**Goals:**

- `decode : Codec α → {n : Nat} → Bytes n → Option (α × Suffix n)` — single
  result, committed `|` (first success).
- `encode : Codec α → α → Option (Σ n, Bytes n)` — unchanged (paper's `print`).
- The inverse laws as unconditional `Option` equalities.
- Concrete codecs are `Codec` values inheriting the two operations.

**Non-Goals:**

- No error-position/`CodecError` type (deferred; not in the paper's API).
- No `List (α × Suffix n)` anywhere in the public API.
- No `Functional`/`Unambiguous` predicates.
- No substrate change (`Bytes n`), no new axioms, no `sorry`.

## Decisions

### D1 — `decode` returns `Option (α × Suffix n)`

```lean
decode : Codec α → {n : Nat} → Bytes n → Option (α × Suffix n)
```

`decode d s = some (x, t)` when the (single, committed) parse of `s` yields
value `x` with remaining `t : Suffix n`; `none` when no parse exists. This is the
paper's `parse` re-based onto bytes and made single-valued (the paper's own
printing direction already commits `|` via `mplus`, so a single result is already
the de-facto semantics of half the paper).

### D2 — `encode` is unchanged

```lean
encode : Codec α → α → Option (Sigma fun n => Bytes n)
```

Exactly the paper's `print :: Printer α → α → Maybe String`. A partial iso is a
partial function; `none` means "value not in the description's domain." No error
type, no position — the paper's `Maybe` is the whole story.

### D3 — `|` is committed (first success), on both directions

`decode (d₁ | d₂) s = (decode d₁ s).orElse (decode d₂ s)` (first `.some` wins,
`.none` falls through) and `encode (d₁ | d₂) x = (encode d₁ x).orElse (encode d₂
x)`. This matches the paper's printer `|` (`mplus (p s) (q s)`) and drops the
paper's parser `|` (`p s ++ q s`, the list union) — the one deliberate cleanup.
Order matters: `d₁ | d₂` prefers the left alternative.

### D4 — The laws become unconditional `Option` equalities

- `roundtrip : encode d x = some ⟨n, s⟩ → decode d s = some (x, Suffix.empty n)`
  — `decode (encode x) = x`, an equality.
- `decode_of_encode` (converse): `decode d s = some (x, Suffix.empty n) →
encode d x = some ⟨n, s⟩` — now **unconditional** (no `Functional d`), because
  there is no list of alternative parses to disambiguate.
- `encode_injective : encode d x = encode d y → x = y` — now unconditional (no
  `Unambiguous d`).

`Rel` stays as the _denotation_ (`Rel (d₁ | d₂) = Rel d₁ ∨ Rel d₂`), but `decode`
is no longer required to enumerate `Rel`'s union; it returns the committed branch.
The `bidir`/`decode_spec` laws are re-stated over `.some`/`none`.

### D5 — Delete the relational band-aids

`Functional`, `Unambiguous`, `relFunctional`, `relUnambiguous` (`Sound.lean`
~534–622) are removed: they existed solely to recover determinism from the
list-valued `decode`. With `decode : … → Option` they are vacuous. `encode_ne_none`
is absorbed into the unconditional roundtrip/converse.

### D6 — Concrete codecs are `Codec` values

`basen`'s `base16/32/64/…` become `Codec …` values built from
`byte`/`seq`/`iso`/`alt`/`many`, and inherit `encode`/`decode`. A leaf no longer
defines its own `encode`/`decode` shape. (A leaf's "decode rejects bad input" is
still a theorem — `decode base16 badInput = none` — but stated over the _shared_
`decode`, not a bespoke one.)

## Risks / Trade-offs

- **[Committed `|` is order-sensitive]** — `d₁ | d₂` ≠ `d₂ | d₁` on overlapping
  domains. This is the _point_ (first alternative wins), and the roundtrip is
  still unconditional because the same order is used on both encode and decode.
- **[Re-deriving the laws over the committed `|`]** — the current `bidir`/
  `roundtrip` were eased by the list-union-agrees-with-`Rel` property; the
  committed `alt` needs a genuine first-success soundness proof (the chosen
  branch still relates in `Rel`). This is proof work, not a type change, and must
  be done without `sorry`.
- **[No error position yet]** — deferred deliberately (the paper has none); a
  future change can add `Except CodecError` to `decode` without touching `encode`.

## Migration Plan

1. Rewrite `decode` as `Option (α × Suffix n)` with committed `|`; keep `encode`
   unchanged; keep `Rel` as the denotation.
2. Delete `Functional`/`Unambiguous`/`relFunctional`/`relUnambiguous`; re-derive
   `roundtrip`/`decode_of_encode`/`encode_injective`/`bidir` as unconditional
   `Option` equalities.
3. Re-shape `decodeRepeat`/`encodeRepeat`/`decodeFull` and `Combinators` to the
   single-result `Option`/committed-`|` shape.
4. Refactor `basen`'s concrete codecs into `Codec` values; prove their rejection
   and roundtrip through the inherited law.
5. Gate: `lake build` zero `sorry`/warnings, `#print axioms` `[propext,
Quot.sound]`, `nix flake check` green; a working `#eval` roundtrip demo.

## Open Questions

None — resolved: adopt the paper's `Option`/partial shapes, single-valued
`decode`, committed `|`, no error positions for now.
