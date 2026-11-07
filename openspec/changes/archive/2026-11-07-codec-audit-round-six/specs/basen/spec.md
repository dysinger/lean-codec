## MODIFIED Requirements

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
