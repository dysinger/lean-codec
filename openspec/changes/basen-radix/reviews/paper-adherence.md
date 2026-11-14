# Review — `basen-radix` (proposal / design / spec delta)

Scope: `/Users/user/_/lean-codec/openspec/changes/basen-radix/{proposal.md, design.md,
specs/basen/spec.md, tasks.md}`, checked against `Codec/Normal.lean`, `Codec/Iso.lean`
and `/Users/user/_/lean-basen/BaseN/*.lean`. Read-only; nothing modified.

## Summary counts

| rank    | n   |
| ------- | --- |
| MUST    | 3   |
| SHOULD  | 6   |
| NITPICK | 4   |

The **core mathematical claim of Q1 survives**: the codomain-in-the-quotient device is
sound, `Iso.law` is a structural field holding for _every_ `Iso` in `Codec/Iso.lean:27-33`,
and `Normal`/`fill`/`fill_surj` are a genuine reification of `S/~` (measured, §Q1). Three
things are **not** sound: the D5 "nothing downstream breaks" claim (M-1), the
"unconditionally" / "all seven radices" scope (M-3), and D4's stated justification, whose
_premise does not establish its conclusion_ (M-2). The empty-sequence sentence you flagged
in Q2 is real and vacuous as written (S-1).

---

## Q1 — Is "a number is isomorphic to its canonical numeral, and lax spellings are names

## for that image" chained correctly? Is there hidden weakening?

**The chain is correct. No hidden weakening in the _law_.** Measured, not relayed.

- `Codec/Iso.lean:27-33` — `structure Iso (α : Type u) (β : Type v) where apply : α → Option β;
unapply : β → Option α; law : ∀ a b, apply a = some b ↔ unapply b = some a`. The law is a
  **field with no hypothesis slot**: there is no place to put "modulo ~". Every `Iso`
  constructed anywhere satisfies it unconditionally as a term.
- `Codec/Normal.lean:133-136` — `structure Normal (S : Type) (norm : S → S) where raw : S;
fixed : norm raw = raw`. The quotient is reified as the fixed-point subtype.
- `Codec/Normal.lean:204-206` — `fill_surj : fill nz f.raw = f`. This is the fact that makes
  the subtype a _bijective copy of the quotient_ rather than a subset, and it is
  `[propext]`-only. Measured:
  ```
  $ printf 'import Codec\n#print axioms Codec.fill_surj\n...' > /tmp/ax.lean
  $ nix develop --command lake env lean /tmp/ax.lean
  'Codec.fill_surj' depends on axioms: [propext]
  'Codec.fill_fixed' does not depend on any axioms
  'Codec.fill_inj' depends on axioms: [propext]
  'Codec.decodeNormal_encode' depends on axioms: [propext]
  'Codec.Normal.ext' depends on axioms: [propext]
  ```
  This refutes the suspicion that `Normal`-based reasoning drags in `Quot.sound` or
  `Classical.choice`: it does not, which is the docstring's stated reason for a subtype over
  `Quotient` and it holds.
- `Iso (List UInt8) (Normal (List UInt8) trim)` therefore _is_ an ordinary `Iso` and every
  `Iso` theorem (`Iso.trans`, `Iso.inverse`, §`S1`'s "the full unconditional-iso list")
  applies. **"The equivalence lives in the codomain, not the law" is faithful (README
  `[S1]`, PAPER §3.1's "modulo equivalence classes" — `README.md:1016-1027` quotes the paper
  correctly).**

**But there is a weakening, one level out — and it is the change's central overclaim.** See
M-3: the law is unconditional _as an `Iso` over the quotient_, but the `Iso`'s `α` side is
`Nat` and its `β` side is `Normal (List UInt8) trim`, i.e. **the total bijection holds only
between `Nat` and _normal forms_.** `trim`, not any `Iso` law, is what says `"007"` is a name
for `"7"`. That is a correct design — and it is _exactly_ the `decodeNormal` shape
`Codec/Normal.lean:224-228` warns "must never be presented as a codec value"— but the spec
sentence reads as a claim about all spellings. The partiality is real and is not where the
documents say it is.

Also note the `Iso`'s `α → Option β` is a _partial_ map even over the quotient:
`appl`y must be `none` for a normal form that is not a valid numeral in that radix (e.g. a
normal form whose first byte is `'9'` in radix 8). `design.md:57` says "`toNat`/`ofNat` are
then **total functions** … not partial relations" — over the _quotient of the syntax_ that is
false for `toNat`: it is `List UInt8 → Option Nat`, and `none` on any non-numeral normal form.
It is `ofNat : Nat → List UInt8` (on the value side) that is total. The sentence conflates the
two directions.

---

## Q2 — D4 and the empty sequence; is the spec sentence self-referential/vacuous?

**Confirmed, and it is the sharpest textual defect in the delta.**

`specs/basen/spec.md:24-26`, verbatim:

> Conversion SHALL be total on valid digit sequences, including the empty sequence, which
> denotes zero only if the radix's own canonical spelling for zero is the empty sequence —
> that decision SHALL be stated once and applied uniformly.

and the parallel rejection clause at `spec.md:56-57`:

> A spelling that names no number — the empty input where the radix has no empty-zero
> convention, a trailing non-digit, a digit outside the alphabet — SHALL be rejected rather
> than normalised.

Both are **conditional on a decision the document does not actually make in normative
text**. `design.md:93` says "**Decision: (2).** `ofNat b 0` yields the single zero digit …
The empty sequence is **not** the canonical spelling of zero **at any radix**" — an
unconditional statement — but (a) the spec sentence is written as `if`, not `because`, and
(b) the `design.md` rationale is a non-sequitur (M-2). So there are now **three** concurrent
statements of the zero convention: `design.md:93` ("single digit, at any radix"), `spec.md:25`
("only if … the empty sequence"), `spec.md:56` ("where the radix has no empty-zero
convention", implying some radix-might). A reader implementing from the spec delta alone
cannot determine `toNat b []`.

What `toNat b []` _should_ be is forced and is fine: the fold `acc := acc*b + d` seeded at
`0` gives `0`, and that is what makes `fill_inj`/`trim` absorb `"007"` into the same class as
`"7"` trivially. The gap is entirely in the prose, not in the mathematics. Fix: delete both
conditional clauses and state the convention once, positively, in the requirement.

---

## Q3 — Is D3's "a leading zero is information-free because the radix is given" sound? Any

## base where a leading zero is not information-free?

**Sound for the layer as scoped, with one incomplete premise and one genuinely missing
alternative.**

The argument (`design.md:80-84`) is: the C-family `017`-is-octal hazard is _radix selection_,
which this layer explicitly refuses to do, so once `b` is a parameter the leading zero cannot
change anything. That is a correct argument **for the conventional positional reading**. It is
_not_ correct as stated, because the conclusion it needs is "changes no value", and the
premise it gives is only "does not change the radix". Two gaps, both fixable in the D3 table:

**(a) It is only true if the digit-_position_ reading is the one intended.** In fixed-width /
MSB-first framed conventions the leading byte is a _region selector_, and there dropping it
does change the meaning: IPv4 dotted-decimal (a leading `0` historically meant octal — the
very `017` hazard, but per-field and still live in `inet_aton`), and the "prefix length is
fixed by the caller" framing used by fixed-width formats. The change is safe here **only
because the `Nat` reading has no framing**, and D3's table has no row saying so. In base 2 the
same question is live: `0b0110` and `110` are the same value, but a leading `0` in an
`n`-bit field is a _bit_, and stripping it is a different operation than stripping a numeral's
leading zero.

**(b) D4 and D3 interact and D3 does not mention it.** After strip-all-leading-zeros as D4
states ("the single zero digit"), `""` (originally all zeros) and `"0"` _both_ normalise to
`"0"` — which is the desired outcome — but `trim` therefore has to **not** be plain
`dropWhile ('0')` at zero, or the canonical form of `0` becomes `""` and D4 is violated by
its own normaliser. Measured that the naive normaliser has exactly this property and that it
is a legal `Normalizer (List UInt8)` (so nothing in `Codec` catches the mistake):

```
$ cat > /tmp/axb.lean   # f := List.dropWhile (· = 0x30); proof of f∘f = f
$ nix develop --command lake env lean /tmp/axb.lean
'_private._stdin.0.nz' depends on axioms: [propext, Classical.choice, Quot.sound]

$ cat > /tmp/axf.lean   # same, leak-free variant
'_private._stdin.0.nz' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Two things this measurement buys: (i) `f [0x30] = []`, i.e. the _natural_ leading-zero
normaliser sends zero to the empty sequence, so D4's decision is **not** a free choice of
`ofNat` alone — it must be an explicit `if ds = [] ∨ ds = "0..." then "0"` special case inside
`trim`, and neither D3, D4 nor task 2.1 says so; and (ii) any such normaliser is `Normalizer`-legal,
so `fill_surj` will happily certify it either way round. This belongs in D4 as a constraint on
`trim`, not as a note on `ofNat`. (The `Classical.choice` in the measurement is my scratch
proof's, not the design's; it is flagged only because `AGENTS.md`'s trap-shape 1 is exactly
this, and task 4.2 asks for the same check.)

---

## Q4 — D5: is "a numeral has no padding" right, and is a padded encoding ever naturally

## read as a numeral?

**The type-split claim is right, measured. The wording is wrong in a way that matters
(M-1), and there is a real counterexample to "no padded numeral" that D5 does not name.**

Measured on the tree:

- `BaseN/Base64.lean:775-779` — `inductive B64 where | nil | full (b0 b1 b2) (rest) |
tail1 (b0) | tail2 (b0 b1)`. The tails encode _byte count modulo 3_, exactly as D5 says.
- `BaseN/Base64.lean:465-471` — `b64TailApply cs := match b64BlockApply cs with | some [b0]
=> some [b0] | some [b0,b1] => some [b0,b1] | _ => none`. **The pad is decoded, not
  discarded**: `Zg==` is accepted (the `=` are inside `b64BlockApply`'s `b64Char`/`b64OrPad`
  alphabet) and `b64TailUnapply` re-emits them by construction.
- `BaseN/Base64.lean:855-862` — `decodeFullB64` filters on `tail.length ≤ 1`
  (note: `tail` here is the _block list_, so `≤ 1` means "one tail block").

So: the `B64` **spine** is a canonical relabelling of the byte list with no padding field
(`BaseN/Base64.lean:798-810`, `b64OfBytes_bytesOf`), and padding is a separate `Iso` at the
tail element. D5's conclusion — "`numeralIso` must not go through `b64BlockIso`/`b64TailIso`"
— is correct. **But "a numeral has no such notion" is false as written**: leading zeros _are_
padding, and D3/D4 make absorbing them the whole point of `trimFor`. What differs is _which
variation_ the padding encodes (zero-padding = information-free; `=` = a length class = the
value's own arity). The distinction D5 needs is "the tail layer is a _length_ encoding, not a
_value-irrelevant_ variation", not "numerals have no padding".

**Counterexample D5 does not name:** a padded encoding _is_ naturally read as a numeral in
base 32/64 whenever you fix `n`. RFC 4648 §10 gives base64url as "the encoding used for the
canonical textual representation of a `Nat` (as a 64-bit integer)" — a fixed-width base64url
numeral (JWT/JOSE `jti`, WebAuthn credential ids, JSON Web Keys' `n`) is exactly
"base-64 digits, MSB-first, of known length". The numeral and the padded encoding coincide
whenever `n` is a multiple of 3 and the leading digit pair is not `A` (`AAAA` = 0, which is a
leading-zero-only spelling of `0` and _is_ absorbed by `trimFor`; `AAAB` = 1 is a **non**-leading-zero
spelling of 1 that `trimFor` does **not** absorb and that `ofNat 64 1` does not produce —
`ofNat 64 1 = "B"`). So the composition `B64 → Nat` exists, is useful, and the three-way gap
between "padded", "minimal", and "fixed-width" is real. D5's third scenario
(`spec.md:108-111`) correctly says "out of scope" — but it says "no theorem claims it does",
which a reader will read as "it cannot be done", when the truth is "it can be done and it
would confuse `numeralIso`". Name the counterexample in D5 and the requirement is honest.

---

## MUST

### M-1 — D5's "Nothing downstream breaks" is refuted; the block-isos are _not_ "special cases" of the generic fold

- **Location:** `design.md:128-137` (D6), `proposal.md:70-79` ("The block `Iso`s are
  re-derived, not deleted"), `proposal.md:100` ("**No existing declaration's statement
  changes**").
- **Claim as written:** "The six power-of-two block isos … are **special cases** of the
  generic fold: a block of `k` radix-`b` digits _is_ `toNat b` on that block, transported to
  the block's own value type. … Nothing downstream breaks, and the duplication stops being
  independent code."
- **Evidence (measured):**
  - `BaseN/Base2.lean:129-175` — `bitBlockApply : List UInt8 → Option UInt8`, `some (UInt8.ofNat n)`.
    `UInt8.ofNat` **truncates mod 256**. `toNat 2` on 8 bits returns `Nat ≤ 255`, so
    "transported to the block's own value type" is a _cast that must be proved lossless_ —
    i.e. the equality is **not** `rfl`-shaped and is not "`toNat` restricted"; there is an
    extra `Nat → UInt8` truncation step that the equality theorem must prove inert.
  - `BaseN/Base32.lean:413-435` — the round-trip `b32BlockDecodeLenient` **checks for the
    pad byte `61`** in its second digit (`b32ToVal (… % 8) * 4 ≠ 61`), i.e. the block's
    numeral reading is _conditioned on the padding convention of the tail layer_.
  - `BaseN/Base64.lean:265-270` — `b64BlockApply` is `b64BlockDecodeLenient` **plus a
    re-encode-and-compare guard** (`if b64BlockUnapply bs = some cs`), so `apply` is
    canonical-only. Restricting `toNat 64` to a 4-digit block gives a value for **every**
    digit string; `b64BlockApply` returns `none` for most of them (`4¹⁶` vs `2²⁴`+pads, and the
    guard trims it further). So `b64BlockApply` is **not** `toNat 64` restricted; it is
    `toNat 64` restricted _and then filtered by canonicity_, which is a different function on
    `none`-inputs.
  - `BaseN/Base10.lean:121-128` — the strongest case for the claim, `digBlockApply`, _also_
    has an extra guard (`if n ≤ 255`) unknown to `toNat 10`, because a 3-digit decimal block
    can denote up to `999`.
- **Verdict:** **OVERCLAIMS.** The claim is true only in a much weaker shape, e.g.
  `∀ cs v, bitBlockApply cs = some v → toNat 2 cs = some (UInt8.toNat v)` — an implication with
  the _premise carrying the canonicity guard_. "Special case" and "restricted to that block"
  are both false descriptions of what must be proved, and task 3.2 ("`bitBlockIso`, …, agree
  with `toNat` restricted to that block") will fail as literally stated for base 64 and for
  base 32.
- **Correction:** rewrite D6/proposal as: "each block `apply` is a **canonicity-filtered
  restriction** of `toNat b`, proved by `toNat b cs = some n → blockApply cs = some
(toBlockVal n)` and, on inputs `blockApply` accepts, `toBlockVal (toNat b cs) = blockApply
cs`; where the block's value type is `UInt8` (`BaseN/Base2.lean:173`,
  `BaseN/Base4.lean`, `BaseN/Base8.lean`, `BaseN/Base16.lean`, `BaseN/Base10.lean`) the
  transport is a truncating `UInt8.ofNat` whose losslessness is part of the theorem." Split
  task 3.2 into 3.2a (fixed-width, cast-losslessness) and 3.2b (b32/b64, canonicity guard),
  and drop "special case".
- **Rank justification (MUST):** as written, task 3.2 is _unprovable_, and the failure will be
  discovered at the change's risk sink (`tasks.md:19-23`, "the first task to do is 3.2 as a
  spike"). A change whose fourth sentence is already false about its own risk sink is a MUST.

### M-2 — D4's stated _justification_ does not establish its conclusion

- **Location:** `design.md:93-97`.
- **Claim as written:** "The empty sequence is **not** the canonical spelling of zero at any
  radix, because (a) `basen-nat-iso` measured the existing encoder producing an empty encoding
  for zero as a _defect_, and (b) an empty canonical numeral makes `""` ambiguous between
  "zero" and "nothing was written"."
- **Evidence:**
  - **(a) is false of _any_ encoder in the tree.** Measured: `BaseN/Base10.lean:130-134`
    — `digBlockUnapply b` always emits exactly three digit bytes (no length branch); there is
    no `List UInt8 → …` whole-number encoder at all (that is the change's own premise,
    `proposal.md:8-12`: "There is no function anywhere in `BaseN/` that folds a list of digit
    bytes into the number they denote"). So there is no existing encoder that emits an empty
    encoding for zero. The parenthetical attributes a measurement to a change whose artifact
    this change **deleted** (`tasks.md:230-232`).
  - **(b) is true of the raw syntax and _false of the quotient_, which is the whole point of
    D2.** Under a normaliser whose class of `0` is `""`, `""` and `"0"` are the _same class_,
    so the "ambiguity" is precisely the ambiguity the quotient exists to absorb — the same
    status `"007"` has. The argument therefore does not distinguish the two candidates; it
    argues against a distinction the design has already discarded.
  - What **actually** decides D4 is not in the document: `""` is ambiguous between zero and
    "no numeral at all" _across formats_, which is why every numeral format in the ecosystem
    forbids an empty integer (JSON has no empty number token, ISO 8601 requires at least one
    digit, YAML 1.1's `!!int` regex is `[-+]?[0-9]+`). That is a _departure-from-nothing_
    argument, and it is the one that should be stated.
- **Verdict:** **MISCHARACTERISES-PAPER / defective rationale.** The conclusion (zero is the
  single digit) is right and I would keep it — but it is currently justified by a false
  precedent and a quotient-ignoring argument.
- **Correction:** replace (a)/(b) with the two real reasons: (i) `""` cannot be a _numeral_ in
  any format with a framing budget (a zero-length numeral is indistinguishable from "field
  absent"), citing the quoted-RFC/external practice; (ii) it is the only choice that makes
  `trim` idempotent and `ofNat` surjective onto minimal forms simultaneously — plus the
  `dropWhile`-sends-zero-to-`""` constraint from Q3(b), which is the _mechanical_ reason the
  decision must be recorded at `trim` and not only at `ofNat`. Note the source change was
  **deleted**, so "(a) measured" is unverifiable: cite a live file or drop it (this is
  exactly the "pointer whose method does not reach its target" defect in `AGENTS.md`).

### M-3 — "unconditionally" and "all seven radices" are true only of the quotient, and only of a _restricted_ `digitVal`

- **Location:** `specs/basen/spec.md:43-46` ("This SHALL be an ordinary `Iso` whose inverse
  law holds **unconditionally**; the equivalence SHALL live in the codomain (the quotient
  type), never as a weakened law"), `tasks.md:172-175` ("the law holds _unconditionally_ with
  no hypothesis about spelling"), `specs/basen/spec.md:10-19` + `tasks.md:120-125` ("**one**
  function, not a dispatch on hand-rolled copies").
- **Evidence:**
  - **(i) "unconditionally" is a claim about the _quotient's_ `Iso`, and is false one level
    out.** The `Iso` is `Nat ↔ Normal (List UInt8) trim`; a _spelling_ reaches a number only
    through `decodeNormal` (`Codec/Normal.lean:238-241`), which `Codec/Normal.lean:224-228`
    says "must never be presented as a codec value or a combinator". So `"007"`'s route to
    `7` is: (a) the `Iso.law` (unconditional), _plus_ (b) `trim "007" = trim "7"`, a separate
    fact about a separate function. The design is right; the _word_ is wrong, and the README's
    `[S1]` ("for every structural `Iso` it holds unconditionally", `README.md:433-436`) is what
    a reader will import. Say: "the inverse law holds unconditionally **on the quotient**; the
    passage from a lax spelling to the quotient is `trim`, whose totality and idempotence are
    a _separate_ obligation (task 2.1), not part of the `Iso`."
  - **(ii) The "one `digitVal` for all seven radices" claim is restricted at radices 2, 4 and
    8, and the restriction is not stated.** Measured: `BaseN/Base2.lean:35-36` —
    `bitVal e := if e = 48 then 0 else if e = 49 then 1 else 2`; `BaseN/Base4.lean`/
    `BaseN/Base8.lean` are the same shape (`quartetVal`, `octToVal`). And measured:
    `BaseN/Base2.lean:49-50` — `valToBit b := if b = 0 then 48 else 49`, with the module's own
    docstring (`:40-48`) saying the two sentinels **deliberately differ** and "That is sound
    only because every _use_ supplies a proof `b ≤ 1`". So `digitVal` may equal `bitVal` on
    the 256 byte values — that is provable — but the _pairwise_ claim "the seven alphabets are
    seven copies of one derivation, each `Nat → Nat` with a radix-bounded validity predicate"
    (`design.md:33-35`) is **false of the encoder direction at 2/4/8**: their fallbacks are
    non-injective (48 and 49 absorb every `b ≠ 0`), which decimal/hex/base32/base64 encoders'
    `valToDig`/`nibbleToHex`/`valToB32`/`valToB64` are not (`BaseN/Base10.lean:49`,
    `BaseN/Base16.lean:66`, `BaseN/Base32.lean:24`, `BaseN/Base64.lean:26` — all valid only on
    their true domain, and `valToDig` is genuinely injective). Task 1.1's "prove it agrees with
    each base's existing alphabet function" is therefore a **decode-only** equality at 2/4/8;
    the encode direction cannot be unified without changing `valToBit`'s fallback, which
    `BaseN/Base2.lean:47-48` explicitly forbids ("Do not 'fix' one sentinel to match the
    other").
  - **A refuted hypothesis to record:** I suspected radix `> 64` was a hole. It is not, and the
    plan's instance list is complete for the package: `ls BaseN/` → `Base2 4 8 10 16 32 64` +
    `Common`. But the spec scopes the _generic_ requirement "`basen` SHALL provide a
    radix-generic conversion … as **one** definition serving all seven radices"
    (`spec.md:10-13`) — a definition-level sentence with no `2 < b ≤ 64` bound anywhere,
    while `numeralIso`'s only stated hypothesis is `2 ≤ b` (`proposal.md:40`,
    `tasks.md:163`). Nothing would fail at `b = 1` or `b = 65`; base 1 is not a positional
    radix and `ofNat 1 n` does not terminate as a _canonical_ finite numeral. State the bound.
- **Verdict:** **OVERCLAIMS** on (i) and (ii); spec-level scope hole on the bound.
- **Correction:** spec §"A number is its canonical numeral": add "(on the quotient)" after
  "unconditionally" and a sentence splitting the obligation into `Iso.law` (unconditional) and
  `trim`'s totality/idempotence (separate). spec §"A numeral denotes a number": replace "the
  seven per-base alphabets SHALL be proved-equal specialisations" with "the seven per-base
  **digit-value** functions (decode direction) SHALL be proved equal to `digitVal` at their
  radix; the encode direction at radices 2/4/8 is **not** unified, because those three carry
  deliberately non-injective `Nat → Nat` fallbacks (`BaseN/Base2.lean:40-50`)". Add
  `2 ≤ b ≤ 64` (or `2 ≤ b`) to the requirement text, not only to `numeralIso`'s signature.

---

## SHOULD

### S-1 — Q2's `toNat []` is stated three contradictory ways; the spec's is a conditional that names no decision

Already given in full in Q2 above. `spec.md:24-26` and `spec.md:55-57` are conditional
("only if …", "where the radix has no empty-zero convention") and `design.md:93` is
unconditional ("at any radix"). Fix: one positive sentence in the requirement —
"`toNat b ds` is `some 0` exactly when the normal form of `ds` is the radix's single zero
digit; the empty sequence normalises to that digit, so `toNat b [] = some 0`" — and delete the
other two.

### S-2 — `design.md:57` says `toNat` is total; it is not

"`toNat`/`ofNat` are then **total functions** on the quotient representative and its value,
not partial relations". `toNat : List UInt8 → Option Nat` is `none` on any normal form that is
not a numeral, and it _is_ an `Option` — that is why it can be `Iso.apply` at all. Only
`ofNat : Nat → List UInt8` is total. Rewrite as: "`ofNat` is total; `toNat` is total on the
numeral subset of the quotient and `none` elsewhere, which is what makes it an `Iso.apply`
rather than a relation."

### S-3 — The spec's rejection clauses and D3's table disagree about trailing whitespace

`design.md:75-76` (table) says trailing whitespace "**no** — not claimed". `spec.md:42-43`
says the information-free variation is "leading zeros and leading whitespace" (agrees), but
`spec.md:55-57`'s rejection list names only "a trailing non-digit, a digit outside the
alphabet" — a _space_ after the numeral is a "trailing non-digit" only if you decide spaces are
not non-digits. Same ambiguity in `tasks.md:156-158` (2.1: "It SHALL NOT absorb trailing
whitespace") versus `tasks.md:178-180` (2.4: "a trailing non-digit … yield `none`"). Say once,
in the requirement: "`7 ` (trailing blank) is rejected; `  7` is accepted."

### S-4 — D5's "a numeral has no such notion" is the wrong sentence, and the padded-as-numeral counterexample is unmentioned

Given in full in Q4. Fix: "padding inside `B64`/`B32` encodes a _length class_, not a
value-irrelevant variation, so it cannot be a `Normal` quotient; a fixed-width base64url
numeral (RFC 4648 §10 JOSE/JWK `n`, WebAuthn ids) **is** a numeral, and it is out of scope
because `numeralIso` is minimal-width, not because padding has no numeral reading."

### S-5 — `proposal.md:74-79` "Nothing downstream breaks" is unqualified

Measured: `BaseN/Base64.lean:421-422` — `b64BlockIso` is consumed by `b64BlockElem`
(`:433`), which is consumed by `decodeFullB64` (`:855-862`); `BaseN/Base16.lean`'s
`hexBlockIsoF` is likewise a surface other work (`basen-uppercase-prepass`) edits. Adding
theorems does not change statements — that part is fine — but D6's own option (1) discussion
and the "proved equal" theorems _do_ create a maintenance coupling: any future change to a
block iso's digit order now fails the new theorem. Say "no _statement_ changes; the block isos
gain a constraining theorem, which is the point" rather than "nothing downstream breaks".

### S-6 — D4's zero-digit spelling breaks the very uniformity claim it makes

`design.md:96-97`: "The requirement states this once rather than per base, so no base can
quietly differ." But the correct answer **is** per-base data: `ofNat b 0` is `[0x30]` for
b ∈ {10,16,32,64} (digits `'0'`), `[0x30]` for b = 8 (`octToVal` reads `'0'`), `[0x30]` for
b = 4 and b = 2 (`bitVal 48 = 0`, `BaseN/Base2.lean:35-36`) — so _today's_ tree happens to
spell zero with `'0'` at every radix, and the decision is "the character that the base's own
`valToX` maps to `0`", which _is_ per-base. State the function (`ofNat b 0 := [toByte
(valToDigit b 0)]`) and note that it is currently `0x30` at all seven — do not claim the
requirement removes the per-base definition.

---

## NITPICK

### N-1 — `design.md:18-21` D0's table cites a `Nat → Nat` "with a radix-bounded validity

## predicate" for `bitVal`/`quartetVal`

`bitVal`/`valToBit` are the _non_-injective pair noted in M-3(ii). It does no harm here
(the row is correct), but the sentence "each `Nat → Nat` with a radix-bounded validity
predicate" is the sentence that hardened into the false uniformity claim.

### N-2 — `tasks.md:147` task 1.3's formulation of the round trip is ambiguous

"`ofNat (toNat radix ds)` returns the canonical form" — `toNat` is `Option`, so the statement
is `toNat radix ds = some n → ofNat radix n = trim ds`. As written it does not typecheck and
it hides the interaction with `trim` that S-1/M-2 are about. State it in the `Option` form.

### N-3 — `design.md:33-35` "`grep -rn 'radix|base : Nat|pow' BaseN/*.lean` → **nothing**"

The pattern is a basic (BRE) alternation inside a single `grep` without `-E`, so it searches
for the _literal_ string `radix|base : Nat|pow`. Measured: `grep -rn 'radix' BaseN/*.lean` and
`grep -rnE 'radix|base : Nat|pow' BaseN/*.lean` both return nothing, so the _conclusion_
survives — but the command as written cannot be reproduced, and `AGENTS.md`'s rule is that a
number (here: a null result) a reader cannot re-derive is a defect. Use `-rEn`.

### N-4 — `proposal.md:8-12`'s measured block is a transcript with no command

`digVal ('7') → 7` etc. are not reproducible as printed (`digVal : Nat → Nat`, so `'7'` is
`55`, not a `Char`). Fine as illustration; either show the `#eval` or say "illustrative".

---

## Refuted / could not confirm

- **"The quotient drags `Quot.sound`/`Classical.choice` into the axiom gate."** Refuted by
  measurement: `fill_surj`, `fill_inj`, `decodeNormal_encode`, `Normal.ext` are all
  `[propext]`-only and `fill_fixed` is axiom-free (`/tmp/ax.lean`, output quoted in Q1).
  `Codec/Normal.lean:59-62`'s reason for a subtype over `Quotient` holds.
- **"`Iso.law` is weakened somewhere."** Refuted: `Codec/Iso.lean:27-33` has no hypothesis
  slot. The weakening is one level _outside_ the `Iso` (M-3(i)), which is a wording defect in
  the spec, not a weakened theorem.
- **"`Iso.prod`/`Iso.trans` do not apply to a `Normal`-valued `Iso`."** Refuted by the type:
  `Normal S norm` is an ordinary `Type`, so `Iso.trans`/`Iso.inverse` apply verbatim; nothing
  in `Codec/Iso.lean` constrains `β`.
- **"The block isos genuinely are `toNat` restricted."** Refuted for base 32/64 (and
  base 10), confirmed _as an implication_ only — see M-1's measurements.
- **"The instance list omits a radix the package has."** Refuted: `ls BaseN/` →
  `Base2 Base10 Base16 Base32 Base4 Base64 Base8 Common`. Seven, as claimed.
- **"The change has no spec delta / collides with another change."** Refuted:
  `openspec/specs/basen/spec.md` has 10 requirements
  (`grep -n 'Requirement:' openspec/specs/basen/spec.md`), the delta adds 3 by name, and none
  of the 3 names collides; `basen-uppercase-prepass`'s "Base16 decoding accepts both cases"
  already exists as a separate live requirement. The `basen-nat-iso` retirement is recorded in
  `tasks.md:230-249`.
- **UNVERIFIED — whether any format in the target ecosystem actually reads a padded base64
  as a `Nat`.** I cited RFC 4648 §10 base64url and JOSE/JWK from general knowledge, not from a
  file in this tree. **Settling measurement:** `grep -rn 'base64url\|Base64' ../lean-basen/BaseN/*.lean
../lean-basen/README.md` for a stated downstream use, or drop the example from S-4 and keep
  only the abstract statement.
- **UNVERIFIED — that `b32BlockDecodeLenient`'s pad-byte check is load-bearing for the
  equality's _direction_.** Measured that the check is _present_ (`BaseN/Base32.lean:421-435`);
  I did not construct the counterexample digit string. **Settling measurement:** in
  `../lean-basen`, state `b32BlockApply [d0, d1, …, d7] = none` for a pair of pad-carrying
  digits and `toNat 32` on the same list `= some n ≠ none`; if it succeeds, M-1's base-32 half
  is proved rather than argued.
