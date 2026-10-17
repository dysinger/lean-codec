# Spec Delta

## MODIFIED Requirements

### Requirement: Nondeterministic (backtracking) decoding

Decoding SHALL be a relation-valued function over the length-indexed byte
string, returning **all** `(value, remaining-buffer)` pairs the description
admits:

```
decode : Codec α → {n : Nat} → Bytes n → List (α × ({m : Nat} × Bytes m))
```

where the remaining buffer `Bytes m` records the consumed length via `m ≤ n`.
Choice (`|`, the paper's `Alternative`) SHALL be the **backtracking union**:
`decode (d₁ | d₂) s = decode d₁ s ++ decode d₂ s`, matching the denotation
`Rel (d₁ | d₂) = Rel d₁ ∨ Rel d₂` by construction. There is no committed choice,
no cursor, no peeking, and no narrowing to a single result, and `decode d s`
itself is stated over the single `Bytes n` carrier (no `List UInt8`/`Array`/
`ByteArray`/`Buffer` carrier replaces it). A **Layer-2 fast path** (a
distinct-named surface such as `commitRemainder` or `decodeArrayFast`) MAY carry
data on `Array UInt8`/`ByteArray`, provided it is proved (or definitionally)
equal to `Bytes n`, never presented as `decode`/`encode` themselves, and never
conflated with the `Bytes n` spec substrate.

#### Scenario: Choice enumerates every branch

- **WHEN** `decode (d₁ | d₂) s` is evaluated
- **THEN** the result is the concatenation of `decode d₁ s` and `decode d₂ s` —
  every `(value, remainder)` pair from either branch, including duplicate values.

#### Scenario: The remaining buffer is length-indexed

- **WHEN** `decode c (s : Bytes n)` returns a `(value, remainder)` pair
- **THEN** `remainder : Bytes m` for a `m ≤ n` witnessed at the type, and the
  byte string is the single `Bytes` carrier — no separate `List` spec and no
  opaque run-model slab.

#### Scenario: A Layer-2 fast path does not displace the `Bytes n` substrate

- **WHEN** a distinct-named Layer-2 surface (e.g. `commitRemainder`, `decodeArrayFast`) carries data
  on `Array UInt8`/`ByteArray`
- **THEN** it is documented as proved (or definitionally) equal to `Bytes n`, never named
  `decode`/`encode`, and the `Bytes n` spec substrate remains the single denotation carrier; `decode`
  itself is unchanged.
