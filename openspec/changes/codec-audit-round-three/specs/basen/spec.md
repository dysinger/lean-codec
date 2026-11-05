# basen Specification (delta)

## MODIFIED Requirements

### Requirement: The conformance laws are gated like the roundtrip laws

Every new canonical/ rejection/ converse/ injectivity theorem SHALL be provable
with only `propext` and `Quot.sound`, zero `sorry`, no `Classical.choice`, and
SHALL be covered by a bench-lane vector (an `example` or `#eval`) so the gate
exercises them, matching the F* reference's `decode_*_invalid` vector set.

The gate's coverage SHALL be a property of the mechanism, not of a list a
maintainer remembers to update. The package SHALL contain a build-time check over
the compiled environment that fails the build — printing the offending name — when
a public theorem is not gated, and when a pinned name has no matching theorem. A
gate whose population depends on remembering to add a line SHALL NOT be described
as covering the package's laws: it covers exactly the laws someone listed, and one
added theorem makes that claim false without any build failing.

#### Scenario: The gate covers the new laws

- **WHEN** `lake build` and `#print axioms` run on the conformance laws
- **THEN** the build has zero `sorry`/warnings, `#print axioms` reports only
  `[propext, Quot.sound]` for each new theorem, and the bench lane value-checks
  each rejection/canonical vector byte-for-byte.

#### Scenario: A law added without a gate entry fails the build

- **WHEN** a public theorem is added to a `BaseN` module and no corresponding
  footprint check is added
- **THEN** `lake build` fails and prints that theorem's name, so the gate cannot go
  green while a law is unchecked.

#### Scenario: A stale gate entry fails the build

- **WHEN** a pinned name in the gate has no matching theorem in the environment
  (a rename, or a deletion)
- **THEN** `lake build` fails naming it, so the gate cannot rot into a snapshot of a
  past tree.

### Requirement: A decoder rejects malformed input

Each `BaseN` decoder — the whole-input decoder
`Codec.decodeFull {x}Elem {x}ConsumesByte n s` over the base's element
`Codec UInt8` `{x}Elem` (for the fixed-width bases; the whole-input format is the
derived `Run` over that element) or, for base32/64, the
whole-input decoder over the base's **composition** (the full-block `Run` =
derived `many`, followed by the terminal-tail `Codec` `{x}TailElem`, with the
result `iso`-ed to the terminal-tail value type `B32`/`B64`; see the D7 note
— there is **no** single `Codec B32`/`Codec B64` value, because the `Codec` AST
has no repetition node) — SHALL return `none` for **every**
input `s` that is not a valid encoding for that base. There is no bespoke
`decodeB32Strict`/`decodeB64Strict` function: rejection is a theorem over the
uniform `Codec.decode`/`decodeFull` composition, not a per-format decoder. "Not valid" SHALL mean
_any one_ of: (a) a byte outside the base's alphabet (for base16, outside the
**hex alphabet** `0-9a-fA-F` — the `Codec` value is a strict **uppercase**
bijection, and RFC 4648 §8's requirement that a decoder accept both cases is
satisfied by the separate case-insensitive decoder `Base16.decodeHexFold`, which
applies the canonicality-preserving case fold **outside** that `Iso` via
`Codec.Normal`; see the §8 requirement below); (b) for the padded bases (base32/base64), a `=` in an illegal position
— including a `=` in the first/second/third data position of any block, a
lone/partial `=` group, or **any data after the terminal `=`**; (c) a wrong
arity (a whole-input byte count that is not a whole number of that base's code
words); and (d) a value that overflows the reconstructed byte (e.g. a base8/10
digit triple `> 255`). The rejection SHALL be proved (`… = none`),
`[propext, Quot.sound]`-only, as an **inequation over the composition** — the
whole-input decoder is `List.head? ((decodeRepeat {x}Elem …).filterMap (decodeFull
…

A rejection theorem's **scope SHALL match its name and its documentation**. A
theorem stated at one concrete input length SHALL be named and documented as a
witness, not as the general law; where a sibling base proves the general form
(for example an arity rejection quantified over every input whose length is not a
whole number of code words), each base SHALL either prove the general form or
record, at the witness, that the general form is unproved.

#### Scenario: A byte outside the alphabet is rejected

- **WHEN** `Codec.decodeFull {x}Elem {x}ConsumesByte` is applied to a `Bytes n`
  containing a byte that is not in the base's alphabet (e.g. `!` for base64, or
  a non-`0/1` byte for base2)
- **THEN** the result is `none`, and a theorem states exactly that.

#### Scenario: Illegal or non-terminal padding is rejected

- **WHEN** the uniform decoder over the padded-base composition (the full-block
  `Run` + terminal-tail `Codec`, `iso`-ed to `B64`/`B32`) is applied to a `Bytes n`
  where `=` appears in an illegal position — the first position of a block, a lone
  partial pad group, or followed by any non-`=` data (`"Zg==AAAA"`,
  `"MY======AAAAAAAA"` as the terminal-`=`-then-data two-block case)
- **THEN** the result is `none` (the `=` is terminal-only per RFC 4648 §3.2),
  proved as an **inequation** — the full-block run stops at the first `=` (no
  `b64BlockElem`/`b32BlockElem` value contains `=`), the leftover alphabet-only
  bytes cannot decode as a `b64TailElem`/`b32TailElem` (which must contain `=`),
  so `decodeFullB64`/`decodeFullB32 = none`.

#### Scenario: Wrong arity is rejected

- **WHEN** a whole-input decoder is applied to a `Bytes n` whose length is not a
  whole number of code words for that base (e.g. 2 base64 chars, 3 base32 chars)
- **THEN** the result is `none`.

#### Scenario: Rejection is the general law, not a vector set

The rejection requirement is quantified over **every** input, and the shipped
theorems are that quantifier — not a collection of named examples. For each of
`Base64` and `Base32`:

- **WHEN** a byte failing the base's alphabet-or-pad predicate (`b64OrPad`/
  `b32OrPad`) occurs at **any** index `i : Fin n` of a `Bytes n`
- **THEN** `decodeFullB{64,32} s = none`
  (`decodeFullB{64,32}_reject_invalid_at`) — generalising the index-0-only
  `reject_first_invalid` to every position.
- **WHEN** a `=` occurs at code-word slot `0` or `1` (i.e. `i % 4 ∈ {0,1}` for
  base64, `i % 8 ∈ {0,1}` for base32) — the non-terminal-padding class, of which
  `"Zg==Zg=="` / `"MY======MY======"` are instances
- **THEN** `decodeFullB{64,32} s = none`
  (`decodeFullB{64,32}_reject_pad_at_low_slot`). This holds for **all** `s`: the
  full-block region is alphabet-only and code-word aligned, and a terminal-tail
  block pads only at slots `≥ 2` (`Rel_b{64,32}TailElem_pad_pos`).
- **WHEN** the byte count is not a whole number of code words — `n % 4 ≠ 0` for
  base64, `n % 8 ≠ 0` for base32
- **THEN** `decodeFullB{64,32} s = none` (`decodeFullB{64,32}_reject_arity`),
  because a successful decode consumes exactly `4 · (|blocks| + |tails|)` bytes
  (resp. `8 · …`) — see `decodeFullB{64,32}_arity`.
- **AND** each of these is `[propext, Quot.sound]`-only, pinned by the `Axioms.lean`
  gate, with a concrete bench vector.

#### Scenario: An overflowing reconstructed byte is rejected

- **WHEN** a fixed-digit base (base8/base10) decoder is applied to a digit trio
  that exceeds `255` (e.g. octal `377` or decimal `255` is fine; `400`/`256` is
  not)
- **THEN** the result is `none`. (Base2/4/16 cannot overflow a byte by
  construction; no such theorem is needed for them.)

#### Scenario: A single-witness rejection is not presented as the general law

- **WHEN** a base's arity-rejection theorem is stated at one concrete input
- **THEN** its name and docstring present it as a witness, and the general
  quantified form is either proved for that base or recorded as unproved.

#### Scenario: A witness does not stand for a property it does not exercise

- **WHEN** a rejection theorem is named for a property (for example rejecting
  lowercase) but its input is rejected by an independent reason at that input
  (for example odd arity)
- **THEN** the theorem does not carry that name, and the named property is stated
  by a theorem whose input actually exercises it.

### Requirement: Base16 decoding accepts both cases (RFC 4648 §8)

The Base16 decoder SHALL accept hex digits in **either** case, as RFC 4648 §8
requires, and SHALL return the same value for a block and its case-folded form.
The canonical alphabet SHALL remain uppercase and the encoder SHALL emit only it.
Case-insensitivity SHALL be supplied by a fold applied **outside** the strict
`Iso` — never by weakening `Iso.law` — so the `Codec` value stays a strict
uppercase bijection and the widening is confined to decoding.

#### Scenario: Both cases decode to the same value

- **WHEN** a byte string and its uppercase-folded form are decoded
- **THEN** both produce the same value: `decodeHexFold s = decodeHexFold
(foldList s)` for one block (`decodeHexBlockFold_case_insensitive`) and
  `decodeHexFold s = decodeFull hexRun (foldByteBytes s)` at whole-input level.

#### Scenario: The strict decoder still rejects lowercase

- **WHEN** lowercase input is fed to the strict `Codec`-value decoder
  `decodeFull hexElem hexConsumesByte`
- **THEN** it returns `none` at an input where case is the **only** reason for
  rejection (an even-length input asserting the arithmetic is even, so the arity
  gate cannot be the cause), and this is **not** a §8 divergence because the
  conformant surface is the separate `decodeHexFold`. The earlier
  "a case-insensitive alphabet would break `Unambiguous`" rationale is withdrawn:
  the constraint is the canonicality of encode.

#### Scenario: The encoder emits a normal form (the layer's obligation)

- **WHEN** the encoder produces a block (`hexBlockUnapply b = some cs`)
- **THEN** that block is already a **fixed point** of the fold (`foldList cs = cs`,
  `foldList_hexBlockUnapply`) — the per-instance hypothesis the normalising
  decoder requires, without which `norm` applied before `unapply` could make
  decoding fail on the encoder's own output.

#### Scenario: The fold is upward, and idempotent

- **WHEN** the case fold is applied
- **THEN** it maps `a`–`f` **up** to `A`–`F` (so the canonical uppercase encoding
  is a fixed point) and is idempotent (`foldByte_idem`, `foldList_idem`), which is
  the `Normalizer` law that makes the quotient type well-formed. It is
