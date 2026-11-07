# basen Specification

## Purpose

Express the `basen` bases as `Codec` values so decoding base64 and decoding JSON
are the same `Codec.decode` call — only the codec changes.

## Requirements

### Requirement: Format codecs are `Codec` values

Every concrete format (base16/32/64, and later JSON, HTTP, ASTs) SHALL be a
`Codec α` value decoded/encoded by the single `Codec.decode`/`Codec.encode` — the
only thing that differs between formats is the `Codec` value, not the operation
shape.

#### Scenario: Decoding base64 and JSON is the same call

- **WHEN** a consumer decodes base64 and JSON
- **THEN** both are `Codec.decode <codec> <bytes>` with `<codec>` a
  `Codec (List UInt8)` / `Codec JSON` value; there is no per-format
  `decode`/`encode` function.

### Requirement: The `basen` bases are `Codec` values

Each `BaseN` base SHALL be a `codec` `Codec` **element** plus a productive
repetition **run** — **not** a single `Codec (List UInt8)` value and **not** a
bespoke per-format decoder/encoder _triple_. The fixed-width bases (2/4/8/10/16)
have element `{x}Elem : Codec UInt8` (one byte per element); the padded bases
(32/64) are a composition of a full-block element `b32BlockElem`/`b64BlockElem :
Codec (List UInt8)` (a 5-byte / 3-byte block) run through the derived repetition
layer, followed by a terminal-tail element `b32TailElem`/`b64TailElem`, `iso`-ed
to the terminal-tail value type `B32`/`B64`. Each element is composed from
`satisfy`/`count`/`iso` (no `many` constructor exists; the repetition layer is
`relRepeat`/`decodeRepeat`/`encodeRepeat`). The whole-input decoder is
`Codec.decodeFull`/the base's own `decodeFullB{32,64}` over the composition, and
the encoder is `encode{X}`/`encodeB{X}` over the `Bytes n` substrate; `B32`/`B64`
is a proved total bijective relabeling of `List UInt8`.

The padded bases' shape makes illegal "data after `=`" unrepresentable **at the
canonical value type**, and this is a proved equivalence. `B32`/`B64` are block/tail
spines with **terminal** tails (`nil` / `full` / `tail1`…/`tail2`…) and no
constructor continuing after a tail, and they are a proved total bijection with
`List UInt8` (`b{64,32}BytesOf_ofBytes` / `b{64,32}OfBytes_bytesOf`). The
characterization law `decodeFullB{64,32}_char_via_type` shows the decoder's image is
**exactly** the image of `encodeB{64,32} ∘ b{64,32}BytesOf`: a byte string decodes
iff it is the encoding of some canonical `B32`/`B64`. A string carrying data after a
terminal `=` admits no such value, because the type has no inhabitant for the
tail-followed-by-block shape (`b{64,32}BytesOf_tail1_eq` makes terminality
definitional). The rejection laws state the same fact as an inequation over the
decoder composition; the two agree.

"No bespoke `encode`/`decode`" SHALL be read as **no per-format decoder/encoder
triple** (no `parseB64`/`encodeB64Strict`/`decodeB64Strict`): the whole-input
base32/64 composition is legitimately exposed as `decodeFullB{32,64}`/
`encodeB{32,64}` over the `Bytes n` substrate, and those are the value's own
entry points, not a parallel bespoke implementation.

#### Scenario: Base16/32/64 are Codec values

- **WHEN** a consumer uses base16/32/64
- **THEN** each is a `Codec`-based value decoded/encoded by `Codec.decode`/
  `Codec.encode` (base16 an element `Codec UInt8` + its `Run`; base32/64 the
  terminal-tail `B32`/`B64` value type reached via `iso` over the block-run +
  tail composition); there is no `BaseN.Base16.decode`-style per-format function.

#### Scenario: The bases compose from the codec primitives

- **WHEN** a base module is inspected
- **THEN** its element is `Codec.iso <blockIso> (count k (Codec.satisfy <digit>))`
  and its decoder/encoder are `decodeRepeat`/`encodeRepeat` — no hand-written
  per-format `decode`/`encode` triple.

#### Scenario: A decoder rejects malformed input (whole-input)

- **WHEN** `Codec.decodeFull {x}Elem {x}ConsumesByte` (or `decodeFullB{32,64}` over
  the padded composition) is applied to a `Bytes n` that is not a whole number of
  valid code words for that base
- **THEN** the result is `none`. (The full rejection contract — bad alphabet
  byte, illegal padding, wrong arity, trailing data after `=`, overflow — was
  landed by `basen-rfc-conformance-theorems` (archived 2026-10-27) and is already
  part of the live `basen` spec; the requirements below state it.)

#### Scenario: Trailing data after `=` is rejected by proof _and_ by the type

- **WHEN** the padded bases' decoder is applied to input carrying data after a
  terminal `=`
- **THEN** the result is `none`, established two ways that are proved to agree: by
  the rejection laws (an inequation over the composition), and by the type-level
  characterization `decodeFullB{64,32}_char_via_type`, whose right-hand side
  quantifies only over canonical `B32`/`B64` values — and the terminal-tail shape
  of those values has no constructor that can carry trailing data.

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

### Requirement: The encoder is canonical

For each base, the encoder (`Codec.encode {x}Elem`, equivalently `encode{X}`
over `List UInt8` for the fixed-width bases; `Codec.encode` over the base32/64
composition — full-block `Run` + terminal-tail `Codec`, `iso`-ed to `B32`/`B64`) SHALL
be the RFC 4648 (or this package's own spec) **canonical**
form: every output byte is in the base's alphabet, and for the padded bases the
`=` pad characters appear **only** in the terminal tail with exactly the RFC
§4.7/§6.7 pad count for the tail's length. Formally, for base32/base64, a
tail of byte length `k` encodes to exactly the RFC pad run (base32 byte length
→ pad count: 1→6, 2→4, 3→3, 4→1, 5→0; base64: 1→2, 2→1, 3→0) and `=` never
precedes a non-`=` byte in the whole output; for base16/2/4/8/10 (no padding)
every output byte is an alphabet character.

#### Scenario: Encoded output uses only the alphabet

- **WHEN** `encode{X}`/`Codec.encode <baseCodec>` is applied to a value
- **THEN** there is a theorem that every element byte of the result satisfies
  the base's digit predicate (the RFC §4/§6/§8 table, or the hand alphabet for
  base2/4/8/10), with `=` permitted only for the padded bases.

#### Scenario: Padding is terminal and arity-correct

- **WHEN** base32/base64 encode a terminal tail of a given byte length
- **THEN** the output's `=` characters occupy exactly the RFC tail for that
  byte length, stated as **byte length → pad count**: base32 1→6, 2→4, 3→3,
  4→1, 5→0; base64 1→2, 2→1, 3→0 — and appear only at the very end of the
  output, never followed by data — as a theorem, not an observation.

### Requirement: Decode is the unique canonical inverse

For each base, the whole-input decoder SHALL be the **unique** inverse of the
encoder: whenever the decoder (`Codec.decodeFull {x}Elem {x}ConsumesByte n s`
for the fixed-width bases; the whole-input form over the base32/64
composition — full-block `Run` + terminal-tail `Codec`, `iso`-ed to `B64`/`B32`) returns `some v`, the encoder `encode{X} v`/`Codec.encode <codec> v`
reproduces `s` byte-for-byte, and the encoder is injective on its value. Combined with the
existing roundtrip law (`decodeFull (encode bs) = some bs`), this makes the
encoder and decoder a partial isomorphism with a single canonical
representation per value.

#### Scenario: A successful decode re-encodes to the input

- **WHEN** the whole-input decoder (`Codec.decodeFull {x}Elem {x}ConsumesByte n s`,
  or the whole-input form over the base32/64 composition — full-block `Run` +
  terminal-tail `Codec`, `iso`-ed to `B64`/`B32`) returns
  `some v` for some `s, v`
- **THEN** `encode{X} v`/`Codec.encode <codec> v = some ⟨n, s⟩` (a theorem, proved
  `[propext, Quot.sound]`-only).

#### Scenario: Encoding is injective

- **WHEN** `encode{X} v = encode{X} v'` (or `Codec.encode <codec> v = Codec.encode
<codec> v'` for base32/64) for values `v, v'`
- **THEN** `v = v'` (each valid encoding identifies exactly one value).

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

The gate SHALL partition **definitions** as well as theorems: the package's gate
SHALL match the dependency's, so that a public definition named by no theorem is a
build failure unless listed with a reason. A gate that partitions theorems only
leaves a public definition invisible — neither gated nor computed — and a definition
that no theorem and no proof line consumes is then dead surface that the gate cannot
report.

The gate's **prose** SHALL be gated too. Where the gate's module documentation states
counts, those counts SHALL be asserted by a build-time check, or the prose SHALL be
deleted. A header table that is asserted while the paragraph beside it is remembered
is not gated: the paragraph can be falsified by a regeneration that updates the table
and leaves the prose stale, with every check green.

**A count stated in prose SHALL be asserted at the same granularity as the claim it
makes.** Where the gate's prose names two figures that stand in a stated relation — a
number of pinned blocks against a number of pinned names — both figures SHALL be
compared with the environment, not one against a constant that drifted with them. A
sentence that says "N against M" is two claims, and asserting only that `N = M + k`
leaves both free to move together while the sentence goes stale.

**A bench lane's documentation SHALL describe the mechanism that exists.** Where the
package's operating instructions, its derivation, or its module docs state that a
lane must be _run_ for its checks to happen, that statement SHALL match the lane's
entry point: a lane whose `main` performs no work and whose checks all fire at
elaboration SHALL be documented as failing at build time, and a lane that does
perform runtime work SHALL have its execution wired. A claim that marking the lane a
package "without running it would verify nothing" is a claim about the code and
SHALL be true of the code.

Where a bench lane's checks live in a module the gate cannot import, a stated count
of the sanctioned construct SHALL be compared against the source in a way that
accounts for the legal spellings of that construct, so that the count cannot be
evaded by formatting: a trailing comment, an inline `by` form, or two occurrences on
one line SHALL all be counted.

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

#### Scenario: A public definition with no law fails the build

- **WHEN** a public `BaseN` definition is named by no gated theorem's type and is
  absent from the definition-surface allowlist
- **THEN** `lake build` fails naming it, matching the behaviour the `codec`
  dependency already has.

#### Scenario: Gate prose stating counts is asserted, not remembered

- **WHEN** the gate's module documentation states how many theorems are pinned,
  allowlisted, or total
- **THEN** a build-time check compares those figures with the compiled environment,
  or the prose is removed, so a stale paragraph cannot survive a regeneration.

#### Scenario: Both figures in a two-number sentence are asserted

- **WHEN** the gate's prose states one count against another, such as a number of
  pinned blocks against a number of pinned names
- **THEN** both counts are compared with the environment, so the pair cannot drift
  together while the sentence naming them goes stale.

#### Scenario: A gate's consistency branch can actually fire

- **WHEN** a gate check computes a condition intended to catch an inconsistent
  count
- **THEN** the condition is true for at least one input — an identity that is false
  for every pair of counts, such as comparing a sum with itself after subtracting
  and re-adding the same quantity, is not a check and is replaced by the identity
  the table requires.

#### Scenario: The gate's error messages are arithmetically true

- **WHEN** a gate check reports counts in a message
- **THEN** any equation it prints holds of the sets it names, rather than combining
  figures from two different sets into one line.

The gate SHALL also be **reproducible against the tree it is run beside**. Where the
package depends on a sibling repository by pinned revision, the pinned revision SHALL
be the sibling's current default-branch commit at the time the gate is last known
green, or the lag SHALL be recorded in the package's operating instructions together
with its reason. A pin that has drifted silently is a stale dependency: the gate is
honest about this package, but a reader comparing it against the sibling tree will
believe a different revision was validated than the one that was, and no build can
report the difference.

Where a package's documentation states a count of a construct it sanctions but does
not gate — a tactic, a trusted operation, an escape from the axiom discipline — the
count SHALL be asserted by a build-time check on the same principle as the counts in
this requirement. A sanctioned exception whose stated size is remembered rather than
computed will drift as the exception grows, and the drift is invisible because the
gate it escapes is, by construction, not looking.

Where the package's history cites a revision by identifier, that identifier SHALL
resolve in the repository it names, or the entry SHALL describe the change without
the identifier. A historical citation that names no object cannot be checked by any
reader and is the same class of defect as a remembered count: it is prose standing in
for a measurement.

#### Scenario: A silently stale pin is corrected or explained

- **WHEN** the package pins a sibling repository and that pin is not the sibling's
  current default-branch commit
- **THEN** either the pin is bumped and the gate re-run, or the package's operating
  instructions record the revision and the reason for the lag, so a reader cannot
  mistake the validated revision for the sibling tree's current one.

#### Scenario: A sanctioned construct's stated count is asserted

- **WHEN** package documentation states how many uses of a banned-or-sanctioned
  construct exist outside the gate
- **THEN** a build-time check compares that figure with the source, or the prose is
  deleted, so the stated size cannot drift as the exception grows.

#### Scenario: A historical revision citation resolves

- **WHEN** the changelog or another historical entry cites a revision by identifier
- **THEN** that identifier resolves in the repository it names, so the entry records
  something a reader can check rather than a remembered string.

### Requirement: Base16 decoding accepts both cases (RFC 4648 §8)

The Base16 decoder SHALL accept hex digits in **either** case, as RFC 4648 §8
requires, and SHALL return the same value for a block and its case-folded form.
The canonical alphabet SHALL remain uppercase and the encoder SHALL emit only it.
Case-insensitivity SHALL be supplied by a fold applied **outside** the strict
`Iso` — never by weakening `Iso.law` — so the `Codec` value stays a strict
uppercase bijection and the widening is confined to decoding.

**The conforming decoder SHALL carry the roundtrip law that makes it a decoder of
the package's format, not merely a case-folding function.** A requirement that a
decoder accept both cases is met by a decoder that also _inverts the encoder_: it
SHALL be proved that folding is the identity on the encoder's output and that the
folded decoder accepts it, so that `decodeHexFold` is connected to `encodeHex` by a
theorem. A wrapper whose case-folding behaviour is tested but which no theorem ties
to the encoder SHALL NOT be described as satisfying §8 on behalf of the package,
because a reader comparing the RFC against the library would find the conforming
reading and no law about it.

Where a package documents a profile as conforming to a specification and the
package's roundtrip, canonicality, injectivity and converse laws are all stated over
a _different_, stricter decoder, the documentation SHALL say which decoder owns
which laws, so that no row of the conformance table claims a theorem the
corresponding declaration does not own.

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

#### Scenario: The conforming decoder inverts the encoder

- **WHEN** a byte list is encoded by `encodeHex` and the result decoded by the
  RFC-4648-conforming `decodeHexFold`
- **THEN** the decoded value is that byte list — `encodeHex bs = some ⟨n, s⟩ →
decodeHexFold s = some bs` — so the §8-conforming reading is a decoder of this
  package's format and not only a case-folding function, and the roundtrip family
  is not owned exclusively by the stricter decoder.

### Requirement: One package covers all seven bases

The `basen` package SHALL provide base 2, 4, 8, 10, 16, 32, and 64 in a single
package, under one `BaseN` module namespace, each as a `codec` `Codec` value.
The four RFC 4648 encodings (base16, base32, base64) SHALL match RFC 4648,
base8 SHALL be three octal digits per byte, and base2/base4/base10 SHALL be
defined by this package's own spec (bit/quartet digit math, and decimal digit
math respectively).

#### Scenario: All seven bases are present

- **WHEN** a consumer imports `BaseN`
- **THEN** the seven per-base modules are all available (not spread across
  multiple packages or absent), each exposing a `Codec` value and its run triple.

#### Scenario: The RFC 4648 bases match the RFC

- **WHEN** base16, base32, or base64 encode a byte string
- **THEN** the output uses the RFC 4648 alphabet (base16 `0-9A-F`; base32
  `A-Z2-7`; base64 `A-Za-z0-9+/`) with the RFC's padding rules.

### Requirement: Every base satisfies a roundtrip law

For each of the seven bases, the whole-input decoder SHALL invert the encoder:
for every value `bs`, `Codec.decodeFull {x}Elem {x}ConsumesByte` applied to the
substrate produced by `encode{X} bs`/`encodeB{X} bs` returns `some bs`. The
proof SHALL be the inherited `roundtrip` law, `[propext, Quot.sound]`-only.

#### Scenario: Roundtrip holds for every base

- **WHEN** the roundtrip theorem for base `N` is checked (e.g.
  `BaseN.Base8.roundtrip`)
- **THEN** `#print axioms` reports only `[propext, Quot.sound]`, and the
  theorem is the inherited `decodeFull (encode bs) = some bs` for all `bs`.

#### Scenario: Known vectors are byte-exact

- **WHEN** a base's block encoder is `#eval`'d on a known vector (RFC 4648 §10,
  or a hand vector for base2/4/8/10)
- **THEN** the output matches the known-good bytes exactly (byte-for-byte, not
  length-only).

### Requirement: The axioms discipline is inherited from codec

Every law in `basen` SHALL be provable with only `propext` and `Quot.sound`, and
SHALL NOT introduce `Classical.choice` or any `sorry`. No `@[extern]`/Layer-2 C
seam is introduced: this package is pure Lean.

#### Scenario: No C seam and no extra axioms

- **WHEN** `basen` is built and `#print axioms` is run on its laws
- **THEN** the build has zero `sorry`/warnings and the axioms are exactly
  `[propext, Quot.sound]`; there is no per-format C and no Layer-2 trust seam.
