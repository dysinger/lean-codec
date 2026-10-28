# Review evidence — four adversarial lenses

This is the evidence base for `tasks.md`. Each task cites a finding by its
`R<lens>.<n>` id. Findings carry the reviewer's reproduced evidence (compile
output, grep, `#print axioms`, command output) where the claim was mechanically
checkable; where it was not, the finding says so.

**Treat a finding as a claim, not a fact.** A task is complete when the cited
evidence no longer reproduces.

**Scope.** The audit covered `README.md`, `PAPER.md`, `AGENTS.md`, the global
`lean` skill, and all of `Codec/*.lean`. No finding concerns `basen` or RFC 4648
conformance — those belong to `basen-rfc-conformance-theorems`, which is complete
and independent.

| Lens | Mandate                                        | Findings | CRIT  | HIGH   | MED    | LOW    | INFO  |
| ---- | ---------------------------------------------- | -------- | ----- | ------ | ------ | ------ | ----- |
| R1   | `README.md` vs `PAPER.md` vs source            | 22       | 2     | 4      | 6      | 10     | 0     |
| R2   | `Codec/*.lean` + `ByteSlice.c`                 | 18       | 0     | 2      | 2      | 7      | 7     |
| R3   | `AGENTS.md` as agent instructions              | 12       | 0     | 2      | 5      | 4      | 1     |
| R4   | global `lean` skill                            | 22       | 0     | 3      | 7      | 12     | 0     |
| R5   | measured performance vs documented performance | 1        | 1     | 0      | 0      | 0      | 0     |
|      | **total**                                      | **75**   | **3** | **11** | **20** | **33** | **8** |

R5 was added after the initial four lenses: it is a _measured_ lens (run the
built binary, compare against the documented ceiling), not a reading lens, and
it was reached by building the `bench` lane rather than by reading it. Its
single finding spans two modules and two documents, which is why it is its own
lens instead of an `R2` addendum.

The three findings more than one lens reached independently:

- **`R1.1` / `R3.1` (CRITICAL)** — `CHANGELOG.md` named the substrate
  `abbrev Bytes := List UInt8`; `Codec/Codec.lean:68` is
  `abbrev Bytes (n : Nat) : Type := Fin n → UInt8`. _Fixed (`57d91ac`)._
- **`R3.2` (HIGH)** — the "zero `sorry` proof gate" is asserted in `AGENTS.md`
  twice, but `default.nix`'s `check` runs a plain `lake build`, which only
  _warns_ on `sorry`. Nothing enforces it. _Open — task 1.3._
- **`R3.3` / `R4.1` (MEDIUM/HIGH)** — the `Classical.choice` catalogue recorded
  1 of 3 verified shapes; the disjunction case (`decide_eq_true (by omega)`)
  reproduces deterministically. _Fixed (`e72be59`)._
- **`R5.1` (CRITICAL)** — `decodeFull`/`decodeRepeat` are defined by
  `WellFounded.fix` on a dependent `Sigma`, which does not compile to a loop. An
  equivalent structural fold over the _same_ types is **588× faster** at
  n=4096, so `decodeFull` is ~3 orders of magnitude slower than necessary and the
  documented "20–40× off C" ceiling is false by ~4 orders on the decode path.
  _Open — tasks 6.1–6.3._

## Verified-correct claims — do not re-litigate these

The reviewers also tested claims that turned out **true**, so a later session does
not re-open them. Confirmed by compilation/inspection:

- Every paper quotation in `README.md` is **verbatim-accurate**, and every section
  number checked (3.1, 3.3, 3.4, 4.1–4.4, 5.1–5.3, 6.1, 6.3, 7.5) resolves. The
  defects in R1 are in the **derived reasoning**, not the quotations.
- `Iso.law` has **no** escape hatch: no
  `axiom`/`unsafe`/`partial`/`opaque`/`native_decide`/`implemented_by` anywhere in
  `Codec/`; all 14 `law :=` proofs are real case analysis.
- Zero `sorry` in the tree; no `Classical.choice` in 18 sampled theorems;
  `fill_fixed` depends on no axioms; `Normalizer.idem` is load-bearing and cannot
  be smuggled through `fill`; termination is honest (`WellFounded.fix` or a real
  decreasing measure, no `decreasing_by sorry`).
- All four Layer-2 C seams **match** their Lean bodies on every reachable edge
  case tested (empty, `i == size`, `i > size`, `memchr` NULL, overlapping
  windows). The defects are in the seam's _laws_ and _evidence reachability_
  (R2.1, R2.2), not in the C.
- The `basen` change counts (31/31) and `codec-normal-form-case-quotient`
  (16/16), `lean-basen` (18/25) are all correct.

---

# Verbatim reports

# Adversarial review — `README.md` vs `PAPER.md` vs source

Scope: `README.md` (550 lines), `PAPER.md` (1466 lines, Rendel & Ostermann,
_Invertible Syntax Descriptions_, Haskell'10), cross-checked against
`Codec/Iso.lean`, `Codec/Codec.lean`, `Codec/Decode.lean`, `Codec/Encode.lean`,
`Codec/Combinators.lean` and `CHANGELOG.md`.

Counts: **2 CRITICAL, 4 HIGH, 6 MEDIUM, 10 LOW** (22 findings).

Line numbers are 1-based into the file named in LOCATION. Paper citations are
`PAPER.md` line numbers plus the paper's own section.

---

## 1. CRITICAL — `CHANGELOG.md:38` and `README.md` disagree about what `Bytes` IS

- **LOCATION** `CHANGELOG.md:38`
- **THE CLAIM** "`Bytes` (`abbrev Bytes := List UInt8`) as the named proof
  substrate, used throughout the core in place of the bare `List UInt8`."
- **WHY IT IS WRONG** The source is the opposite shape, and it is
  _length-indexed_: `Codec/Codec.lean:68`

      abbrev Bytes (n : Nat) : Type := Fin n → UInt8

  `README.md:29`, `README.md:207-215` and `README.md:245` all correctly say
  `Bytes n := Fin n → UInt8` and even devote a section ("Representations — one
  length-indexed byte string") to arguing that the `List UInt8` carrier was
  _deleted_ as "the defect". `Codec/Sound.lean:11`, `Codec/Packed.lean:14` and
  `Bench.lean:11` also say `Fin n → UInt8`. So `CHANGELOG.md` is the sole
  outlier, and it advertises a _type alias with a different arity_ (`Bytes` vs
  `Bytes n`) — a reader following it will write `Bytes` with no argument and get
  a type error. This is not a stale summary of a removed API: the CHANGELOG is
  `[Unreleased]` and the offending bullet was written by `fecd9f4`
  ("seed from git history"), i.e. it is live, un-retracted prose.

- **SUGGESTED FIX** Rewrite the bullet as `Bytes n := Fin n → UInt8` (the
  length-indexed substrate) and drop the `List UInt8` spelling; if the earlier
  `List UInt8` era deserves history, say so explicitly and put it under a dated
  release heading, not under `[Unreleased]`.

---

## 2. CRITICAL — `[D2]`'s parenthetical citation of §4.3 "the graph" is a strawman of what `codec` actually does

- **LOCATION** `README.md:70-75` (`[D2]`), echoed at `README.md:265-296`
- **THE CLAIM** "`codec` keeps it that way: `decode` returns all `(value,
remainder)` pairs" — presented as reproducing the paper, with §4.3 cited as
  the same thing.
- **WHY IT IS WRONG** The paper's §4.3 `Rel` graph is `[(α, String)]` — a
  relation on _whole_ concrete strings, and `parse` only keeps the results whose
  remainder is `""` (`PAPER.md:503`: `parse (Parser p) s = [x | (x, "") ← p s]`).
  `codec`'s `decode` (`Codec/Decode.lean:31`) returns `List (α × Suffix n)` —
  _every_ remainder, which is a strictly richer object than `Rel`. The README
  itself states this correctly in the laws block (`README.md:441-447`:
  `Rel d x s ↔ (x, Suffix.empty n) ∈ decode d s`), so the "keeps it that way"
  framing in `[D2]` contradicts the README's own law. Worse, `[D2]` is filed
  under "Departures (observable-semantics changes)" yet is described as _not_ a
  departure ("`codec` keeps it that way") — self-contradictory classification.
- **SUGGESTED FIX** Either move the "all remainders" record into `[S#]` (it is a
  strengthening: `decode` is the paper's `Rel` _plus_ partial input), or drop
  `[D2]` as a departure and say plainly: "the paper's `Parser` returns all
  `(value, remainder)` pairs filtered by `parse`; `decode` returns the unfiltered
  list, which is `Rel` made executable."

---

## 3. HIGH — §7.5 quote is real but the surrounding framing ("almost as an aside", "muses") undersells and mislocates it

- **LOCATION** `README.md:26-28`, `README.md:154-155`, `README.md:369-371`
- **THE CLAIM** The paper "notes, almost as an aside in §7.5, that it 'would be
  interesting to see' it encoded dependently"; "§7.5 muses about encoding it
  dependently".
- **WHY IT IS WRONG** _Verbatim quote is correct_ — `PAPER.md:1301-1303`: "It
  would be interesting to see how the invariants of Iso values could be encoded
  in a dependently typed language." So no misquote. Two accuracy problems
  remain. (a) §7.5 is titled "Other" and is the paper's catch-all future-work
  bucket; the sentence is the paper's _last stated future-work item on this
  exact design_, i.e. it is the paper explicitly deferring the thing `[S1]`
  claims to deliver — describing that as a mere "aside"/"muse" weakens the
  strengthening it is meant to support. (b) The README's own gloss compresses
  "the invariants of `Iso` values" into "it" with an antecedent in the prior
  clause about prose, so a reader cannot tell the paper says _invariants of Iso
  values_, not "the prose law". The paper also states source of the problem at
  `PAPER.md:760-763` ("It is not safe because it is not checked that the two
  directions are really inverse to each other") — §5, not §7.5 — which is a much
  stronger hook than §7.5.
- **SUGGESTED FIX** Quote §5's "neither safe nor convenient … not checked that
  the two directions are really inverse" as the motivating statement, and cite
  §7.5 as the follow-up sentence, quoted exactly: "how the invariants of Iso
  values could be encoded in a dependently typed language." Drop "almost as an
  aside" / "muses".

---

## 4. HIGH — `[D4]`'s "`ignore` is impossible under strict isomorphism" is true, but the README's stated _reason_ contradicts the paper (and its own §3.1 reading)

- **LOCATION** `README.md:85-120`, `README.md:301-330`
- **THE CLAIM** "`ignore` cannot inhabit `Iso α S` _because it is not an `Iso`_";
  "a lossy `ignore` cannot inhabit `Iso`, since two distinct inputs mapping to
  one output make `unapply` unable to invert both"; and `skipSpace`/`optSpace`/
  `sepSpace` "share the same one-way-lossy whitespace shape".
- **WHY IT IS WRONG** The §6.3 definition is `PAPER.md:1043-1046`:
  `ignore :: α → Iso α ()`; `f = Just ()`, `g () = Just x`. Note it is a total
  _constant_ function on the forward side and a total constant on the reverse —
  it is **not** nondeterministic and _not_ "two distinct inputs mapping to one
  output with `unapply` unable to pick" (there is only one possible output, and
  `unapply` deterministically returns `Just x`). The real defect is exactly what
  the paper says (`PAPER.md:1047-1048`): "`ignore` is **again not a strict
  partial isomorphism, because all values of α are mapped to ()**" — i.e. it
  violates _injectivity of `apply`_, so `law` would demand
  `apply a = some () ⟺ unapply () = some a` for **all** `a`, i.e. it is
  degenerate at `()`. The README's "two distinct inputs mapping to one output
  make `unapply` unable to invert both" is a _different_ (nondeterminism)
  justification and it is not what fails. Additionally the README's §3.1
  characterisation is accurate but applied to the wrong object: the paper's
  "modulo equivalence classes" sentence (`PAPER.md:313-318`) is illustrated by
  _exactly this_ blanks example, which the paper places under §3.1's invariant
  discussion, not as license for `ignore` specifically.
  Separately, "all three share the same one-way-lossy whitespace shape" is
  wrong for `sepSpace`: `PAPER.md:1042` defines it as
  `sepSpace = text " " ∗ skipSpace`, and `∗` is the "ignore right" variant
  (`PAPER.md:986`), so `sepSpace` emits `" "` then `skipSpace` emits `""` —
  one fixed space out. It is lossy, fine; the shape is _composed_, not the same
  primitive, and the important part is that only `skipSpace`/`optSpace` are
  direct `ignore` instantiations. The README says this much two sentences
  earlier, then flattens it.
- **SUGGESTED FIX** State the failure precisely: `ignore x = Iso (const (Just ()))
(const (Just x))` fails `law` because `apply a = some ()` holds for every `a`
  while `unapply ()` can return only one `a`; quote the paper's own
  "all values of α are mapped to ()". Drop the "unapply cannot invert both"
  gloss and the "all three share the same shape" sentence.

---

## 5. HIGH — the §3.1 "modulo equivalence classes" reading is accurate, but `[S1]`'s counter-claim ("kept as-is / unconditional") silently ignores that `codec` is _not_ strictly weaker on this axis — it is _differently_ constrained

- **LOCATION** `README.md:154-158` (`[S1]`); `README.md:88-99`
- **THE CLAIM** "The paper §3.1 states the inverse invariant in prose, unchecked
  … `codec` does it … the strict law holds for **every** core `Iso` — the
  structural ones with no precondition, and `foldl`/`foldr` with a
  well-foundedness witness the caller supplies."
- **WHY IT IS WRONG** The §3.1 quote is exactly right (`PAPER.md:313-315`:
  "we will sometimes interpret this condition modulo equivalence classes"). But
  §3.1 also states the unchecked invariant _in the same breath_
  (`PAPER.md:305-307`: "if f a returns Just b, g b returns Just a, and the other
  way around"), so "unchecked" is right and "in prose" is right. The sentence
  that is wrong is the _second_ half: `foldl` is listed as an instance of the
  unconditional law, but `Codec/Iso.lean:566-572` **restricts `apply` to
  terminal seeds** — `apply (a, bs) := match i.unapply a with | none => … |
some _ => none` — precisely because the raw fold is _not_ an iso on all
  inputs. `Codec/Iso.lean:565-566`'s own docstring says so: "`apply` is
  restricted to _terminal_ seeds … the honest domain on which the fold/unfold is
  a genuine bijection." So `foldl`'s law holds only after the _definition_ has
  been narrowed to a domain, which is a different guarantee from "the law holds
  unconditionally" — a caller who supplies a non-terminal seed gets `none`, and
  the "unconditional" claim is vacuously satisfied. (The `measure` witness is a
  separate, real precondition, correctly disclosed.) Compare `README.md:164-166`
  (`[S4]`), which describes `foldl`/`foldr` as taking "a _precondition_, not an
  unconditional law" — `[S1]` and `[S4]` contradict each other on the same
  declaration.
- **SUGGESTED FIX** Split `[S1]` into: (i) structural isos — law unconditional;
  (ii) `foldl`/`foldr` — law holds on the terminal-seed domain, with a
  `measure`/`MeasureDecreases` witness, which is exactly what `[S4]` says. Make
  the two anchors agree.

---

## 6. HIGH — `[D7]`'s `Iterate`/"§5.2 foldl machine" claim is _almost_ right and gets the load-bearing detail wrong

- **LOCATION** `README.md:135-142` (`[D7]`), `README.md:350-361`
- **THE CLAIM** "`iterate` (paper §5.3, the backward-run step of the §5.2 foldl
  machine) is deliberately omitted. Its forward- and backward-iteration fixpoints
  need not coincide, so no inverse law exists without a per-element
  'chain-isolated in both directions' precondition."
- **WHY IT IS WRONG** Section attribution is correct: `iterate` is defined at
  `PAPER.md:866-869` inside §5.3 "Running the abstract machine backwards"; the
  small-step machine is §5.2 (`PAPER.md:829-851`). The mechanism claim is also
  directionally right — `iterate step = Iso (Just ∘ driver (apply step)) (Just ∘
driver (unapply step))` really does take two independent `driver` fixpoints,
  and the paper _never proves_ them equal (its only argument is the informal
  "we know from the definition of step that the second component will always
  contain `[]`", `PAPER.md:900-906`). Two things are wrong anyway:
  (a) **"per-element 'chain-isolated in both directions' precondition"** is
  invented vocabulary with no counterpart anywhere in the paper, and it is not
  what `codec` actually requires. `codec` requires a **`measure : α → Nat` with
  `MeasureDecreases`** (`Codec/Iso.lean:531-553`), i.e. a global well-founded
  descent on the _result_ type. A "per-element" precondition and a "decreasing
  Nat-valued measure" are not the same obligation, and the README states the
  wrong one in the very anchor a porter is told to reproduce.
  (b) **"`foldl` is the combinator `chainl1` actually needs"** is misleading:
  `Codec/Combinators.lean` has **no `chainl1` value at all** (grep: no
  `def chainl1`); what exists is `relChainl1`/`decodeChainl1`/`encodeChainl1`
  (`Codec/Combinators.lean:228`, `:247`). So `chainl1` needs `Iso.foldl` _plus_
  the repetition triple _plus_ a `ConsumesByte` witness _plus_ the measure —
  `foldl` alone is not "all `chainl1` needs". `README.md:360` repeats the same
  over-claim.
- **SUGGESTED FIX** Replace the invented precondition with the real one:
  "`codec` replaces `iterate` with `Iso.foldl`, which takes a `measure : α → Nat`
  and a proof that each unfold step strictly decreases it." Replace "`foldl` is
  all `chainl1` needs" with "`codec`'s chain combinators are
  `relChainl1`/`decodeChainl1`/`encodeChainl1`, which use `Iso.foldl` for the
  fold step and the repetition triple for the operand list."

---

## 7. MEDIUM — the §6.3 `ignore` _definition_ is quoted correctly, but `[D4]`'s `skipSpace`/`optSpace` re-emission description reverses the paper

- **LOCATION** `README.md:303-308`
- **THE CLAIM** "`skipSpace` re-emits none, `optSpace`/`sepSpace` re-emit a
  single blank".
- **WHY IT IS WRONG** Paper §6.3, `PAPER.md:1030-1042`: `skipSpace` = "accepts
  arbitrary space while parsing, and **produces no space** while printing"
  (correct); `optSpace` = "accepts arbitrary space while parsing, and **produces
  a single space character** while printing" (correct) — but this is
  `ignore [()]` applied to the whitespace run (_zero_ or more `text " "`), so on
  the _zero-space_ input it prints **one** space, not zero, and on any
  non-empty input it also prints one. So "re-emit a single blank" is right for
  `optSpace` only and wrong as stated for `sepSpace` (which uses `text " " ∗
skipSpace`, i.e. requires ≥1 space on parse — the README's own line 92 in
  `[D4]` earlier says `sepSpace` "composes it", which is the accurate
  statement). The broader point — none preserve length — is correct.
- **SUGGESTED FIX** Say `skipSpace` prints nothing, `optSpace` prints exactly one
  space regardless of how many (including zero) were parsed, and `sepSpace =
text " " ∗ skipSpace` prints exactly one space while requiring ≥1 on input.

---

## 8. MEDIUM — `[S6]`'s claim that the paper's `many`/`chainl1` are "values" is right, but the _reason given_ ("the paper is a lazy language") is not the load-bearing fact and the README's contrast with Lean is overstated

- **LOCATION** `README.md:180-196` (`[S6]`), `README.md:390-406`
- **THE CLAIM** "The paper is a **lazy** language, so `Rel`'s meaning 'will
  generate and concatenate infinite lists' (§4.3) and its two named list
  combinators — `many` (§3.4) and `chainl1` (§6.1 …) — are ordinary **values**.
  Lean is **strict**: a finite AST node cannot contain an unbounded repetition."
- **WHY IT IS WRONG** Verified accurate on the facts: `many` is a _function_ you
  call (`PAPER.md:441-448`: `many :: Syntax δ ⇒ δ α → δ [α]`), `chainl1` is
  `PAPER.md:1015-1017`: `chainl1 arg op f = foldl f $ arg ∗ many (op ∗ arg)`, and
  `PAPER.md:497-499` is quoted verbatim ("it will generate and concatenate
  infinite lists"). But: (a) the README's §4.3 quote is used as evidence for
  _laziness being essential_, when the paper's sentence is about the `Rel`
  _instance being unusable as an executable implementation_ — an observation
  about the denotation, not a claim that `many` is a value _because_ Haskell is
  lazy. `many` is an ordinary value because it is a **polymorphic function of
  the `Syntax` class**, i.e. `[D6]`'s typeclass embedding — which is the real
  cause. Framing it as strictness is a diagnosis error that makes `[S6]`
  seem to follow from `[D7]`-style concerns. (b) "Lean is strict: a finite AST
  node cannot contain an unbounded repetition" is asserted, not argued, and the
  AGENTS.md "Current state" records the stronger, verified claim (`Codec →
Productive → Rel → Codec` definitional cycle; mutual-inductive escape fails
  the universe check) that the README omits — a porter gets the assertion with
  no way to check it.
- **SUGGESTED FIX** Attribute `many`'s value-hood to the `Syntax` typeclass
  (cross-reference `[D6]`), and keep strictness only for the _AST/induction_
  obstacle; add the one-line reason (definitional cycle `Codec → Productive →
Rel → Codec`) so the claim is checkable.

---

## 9. MEDIUM — `[S6]` says `codec` "derives `sepBy`/`chainr1` in the same §6.1 style … the paper defines no `sepBy`/`chainr1`" — true of the paper, but `codec` has no `sepBy` either, and the README contradicts itself about which one it derived

- **LOCATION** `README.md:186-193`; contradicted by `README.md:398-403`
- **THE CLAIM** "`codec` _additionally_ derives `sepBy`/`chainr1` (one-or-more,
  zero-or-more) in the same §6.1 style".
- **WHY IT IS WRONG** `Codec/Combinators.lean:180-191` defines **`relSepBy`
  as one-or-more only**; the docstring is explicit: "The empty list is **not** a
  `sepBy` value … so this combinator is semantically the paper's `sepBy1`
  (one-or-more), _not_ `sepBy` (zero-or-more); zero-or-more separation is
  `optional (sepBy p sep)`." The README's own `[S5]`/`[S6]` lay section
  (`README.md:396-403`) says the same thing ("the `sepBy` triple has '**one or
  more**' (non-empty) semantics"), so `[S6]` at line 187 ("one-or-more,
  zero-or-more") directly contradicts it. There is also no symbol named
  `sepBy`/`relSepBy`'s zero-or-more partner in core; the zero-or-more form is
  only _reachable_ by composing `optional`.
- **SUGGESTED FIX** Make both statements say: `codec` derives a one-or-more
  `sepBy` (`relSepBy`/`decodeSepBy`/`encodeSepBy`, i.e. `sepBy1`) and
  `chainl1`/`chainr1`; zero-or-more separation is `optional` of the one-or-more
  form.

---

## 10. MEDIUM — `[D6]` calls `Codec` "an inductive AST (`iso`/`seq`/`alt`/`empty`/`pure`/`byte`/`satisfy`)" while `[D6]`'s body still cites the paper's five methods; and `[D6]`'s "seven constructors" is right but the abstraction sketch names only six

- **LOCATION** `README.md:122-131`, `README.md:343-346`, `README.md:449-452`
- **THE CLAIM** "`codec` makes `Codec` an explicit **tree** (seven constructors)";
  "`iso`/`seq`/`alt`/`empty`/`pure`/`byte`/`satisfy`".
- **WHY IT IS WRONG** The count is correct — `Codec/Codec.lean:34-55` has exactly
  `iso`, `seq`, `alt`, `empty`, `pure`, `byte`, `satisfy`. But
  `README.md:418-423`'s "a description is a value built from these combinators"
  block lists only `iso`, `*`(=`seq`), `|`(=`alt`), `empty`, `pure`, `byte`,
  `satisfy` — that _is_ seven, counted correctly, but `satisfy` is dropped from
  the prose list at `README.md:345` ("seven constructors" with no list) while
  `[D6]`'s paper-side description says "a `Syntax` typeclass, with `$`/`∗`/`|`/
  `pure`/`token` as methods" — five, correct per `PAPER.md:437-449` — so the
  `[D6]` claim that `codec` "instead" makes an inductive AST is fine, but the
  `[D6]` text implies a 1:1 mapping that does not exist: `satisfy` has **no
  paper counterpart** (the paper's `subset p $ token` composite is `codec`'s
  `byte` + `codec`-side `subset`, see `[D8]`), yet `[D6]` presents the
  constructor list as a literal translation of the paper's interface.
- **SUGGESTED FIX** In `[D6]`, add one clause: "`satisfy` is a fused
  `subset p $ token` leaf with no separate paper analogue; the paper's `token`
  is `codec`'s `byte`."

---

## 11. MEDIUM — `[S3]`'s "core ships only the primitive leaves `byte` and `satisfy` (plus the non-leaf `pure`)" is accurate, but `[D8]`'s decidable-witness claim over-reaches for `satisfy`

- **LOCATION** `README.md:161-164` (`[S3]`), `README.md:143-149` (`[D8]`)
- **THE CLAIM** "`pure`/`element`/`subset` carry a _decidable_ witness, not the
  paper's `Eq α`/`(α → Bool)` … the same _job_ … but _decidable and
  proof-backed_ rather than a free-form `Eq` or an unverifiable `Bool`."
- **WHY IT IS WRONG** `Iso.element` and `Iso.subset` do take
  `[DecidableEq α]`/`[DecidablePred p]` (`Codec/Iso.lean:200`, `:219`) — correct.
  But `Codec.satisfy` takes a **bare `Bool`-returning function**
  (`Codec/Codec.lean:55`: `satisfy : (UInt8 → Bool) → Codec UInt8`), which is
  _exactly_ the paper's `subset :: (α → Bool) → Iso α α`
  (`PAPER.md:787-789`) — the "unverifiable `Bool`" the entry says was replaced.
  Likewise `Rel_satisfy` (`Codec/Codec.lean:270-271`) is a proposition _about_
  `p b = true`, not a decidability witness that helps the prover. So `[D8]`
  is true for `Iso.element`/`Iso.subset` and **false for the `Codec` leaf**,
  which is the one a downstream format author actually writes.
- **SUGGESTED FIX** Scope `[D8]` to `Iso.element`/`Iso.subset`/`Codec.pure` (the
  latter carries `[DecidableEq α]`, `Codec/Codec.lean:47`), and state plainly
  that `Codec.satisfy p` keeps the paper's free-form `(UInt8 → Bool)` because a
  `DecidablePred` over `UInt8` would be no more checkable.

---

## 12. MEDIUM — `[D1]` says "the value graph is given as `Rel :: [(α, String)]` (§4.3)" — the paper's declaration is `data Rel α = Rel [(α, String)]`, and §4.1's `Parser` is a `newtype`, not a function type

- **LOCATION** `README.md:57-62` (`[D1]`); repeated `README.md:71`
- **THE CLAIM** "The decoder is `Parser (String → [(α, String)])` (§4.1) … the
  value graph is given as `Rel :: [(α, String)]` (§4.3)."
- **WHY IT IS WRONG** `PAPER.md:466-467`: `newtype Parser α = Parser (String →
[(α, String)])` — `Parser` is a `newtype` _wrapping_ a function, and the
  README's `Parser (String → [(α, String)])` reads as `Parser` applied to a
  function _type_, i.e. the wrong constructor. `PAPER.md:494-495`: `data Rel α =
Rel [(α, String)]` — a datatype with a list field, mis-transcribed as the
  `::`-annotated `Rel :: [(α, String)]`. Small, but these are the two type
  headlines of `[D1]`/`[D2]` and a porter will type them literally.
- **SUGGESTED FIX** Use the paper's own syntax verbatim:
  `newtype Parser α = Parser (String → [(α, String)])` and
  `data Rel α = Rel [(α, String)]`.

---

## 13. LOW — `README.md:8` calls the paper "Haskell Symposium 2010" — the venue is `Haskell'10`, and the README's own bibliography slot in `PAPER.md` says Haskell'10, September 30, 2010, Baltimore

- **LOCATION** `README.md:7-10`
- **THE CLAIM** "Rendel & Ostermann's _'Invertible Syntax Descriptions: Unifying
  Parsing and Pretty Printing'_ (Haskell Symposium 2010)".
- **WHY IT IS WRONG** Not wrong in substance (`PAPER.md:31-33`: "Haskell'10,
  September 30, 2010, Baltimore, Maryland, USA"), but the README never gives the
  full citation, so a reader cannot resolve it from the README alone. A one-line
  full reference would also pin the version the section numbers refer to.
  Also: the README's §-citations ("§3.4", "§6.1", "§7.5") are only meaningful
  relative to `PAPER.md`'s OCR'd numbering, which the README does say at
  `README.md:51-53` — good, keep it, but tie it to the citation.
- **SUGGESTED FIX** Add the full reference with pages/DOI and say explicitly:
  "section numbers below are the paper's own, as reproduced in `PAPER.md`."

---

## 14. LOW — `README.md:27` renders the §7.5 quote with the wrong antecedent ("it" for "the invariants of Iso values")

- **LOCATION** `README.md:26-28`
- **THE CLAIM** "notes … that it 'would be interesting to see' it encoded
  dependently".
- **WHY IT IS WRONG** The paper says: "It would be interesting to see **how the
  invariants of Iso values** could be encoded in a dependently typed language."
  The README's ellipsis cuts the subject out and replaces it with "it", so a
  careful reader cannot tell whether the paper muses about the _law_, the
  _functor structure_, or _`Rel`_. (See finding 3.)
- **SUGGESTED FIX** Quote the sentence in full, or quote the operative fragment:
  "how the invariants of `Iso` values could be encoded".

---

## 15. LOW — `[D3]`'s "printer `|` is left-biased `mplus` (try left, else right)" is right in effect, but `mplus` on `Maybe` is not "left-biased union" in the sense the parenthetical implies, and the paper states the asymmetry in §3.3, not §4.2

- **LOCATION** `README.md:76-84` (`[D3]`)
- **THE CLAIM** "its _parser_ `|` is backtracking union (`++`, §4.1) while its
  _printer_ `|` is left-biased `mplus` (try left, else right; §4.2)."
- **WHY IT IS WRONG** Both code citations are right — `PAPER.md:539-540`
  (`Parser p | Parser q = Parser (λ s → p s ++ q s)`) and `PAPER.md:657-659`
  (`Printer p | Printer q = Printer (λ s → mplus (p s) (q s))`) — but the
  _prose_ statement of the asymmetry is §3.3, `PAPER.md:407-411`: "For Printer,
  `|` will try to print with the left printer. If this is not successful, it
  will print with the right printer instead." §4.2 gives only the code. Citing
  §4.2 for a semantic claim is defensible but weaker; §3.3 is where the paper
  _says_ it.
- **SUGGESTED FIX** Cite §3.3 for the prose asymmetry and §4.1/§4.2 for the two
  implementations.

---

## 16. LOW — `[D5]` ("`|` needs no prefix-disjointness condition") is sound but attacks a condition the paper never proposes, and the README does not say who does

- **LOCATION** `README.md:129-142` (`[D5]`)
- **THE CLAIM** "Some deterministic-parser designs require `|`'s branches to be
  _prefix-disjoint_ … `codec` requires none."
- **WHY IT IS WRONG** True and defensible (the README's own `many p` argument is
  correct: `[]` is a prefix of everything), but the entry names no dialogue
  partner. The paper _does_ discuss a real alternative semantics — Parsec's
  "predictive parsing with a look ahead of 1" (`PAPER.md:698-703`) — which is
  the honest foil, and the paper explicitly notes `p | q` "may fail, even if `q`
  would succeed". As written, `[D5]` reads as a rebuttal to a strawman, and it
  overlaps `[D3]` almost entirely.
- **SUGGESTED FIX** Cite the paper's Parsec discussion (§4.4) as the foil, and
  merge `[D5]` into `[D3]` or explicitly mark it "corollary of `[D3]`".

---

## 17. LOW — §4.4's "exponential worst case" is cited as "the paper's own admitted cost", but the paper also admits a _space leak_, which the README drops

- **LOCATION** `README.md:296-300`
- **THE CLAIM** "The cost is the paper's own admitted cost (§4.4): naive
  backtracking is exponential in the worst case".
- **WHY IT IS WRONG** `PAPER.md:675-677` says both: "The parser implementation
  also suffers from an exponential worst-case complexity **and a space leak due
  to unlimited backtracking**". Citing half of an admitted cost in a paragraph
  whose thesis is "we keep the semantics exactly" is a soft sell.
- **SUGGESTED FIX** Mention the space leak too, or say why it does not arise
  under `Bytes n`/`Suffix n`.

---

## 18. LOW — the `Rel` law in the abstraction block is stated with an unbound `n`, and `decode` is written with an implicit binder that does not match the source signature

- **LOCATION** `README.md:439-447`
- **THE CLAIM** "`decode : Codec α → {n : Nat} → Bytes n → List (α × Suffix n)`";
  "`Rel d x s ↔ (x, Suffix.empty n) ∈ decode d s`".
- **WHY IT IS WRONG** `Codec/Codec.lean`'s `Rel` is `Rel (d : Codec α) (x : α)
{n : Nat} (s : Bytes n) : Prop` (see `Rel_satisfy` at `Codec/Codec.lean:270`),
  so `s` carries its own length; the README's law then uses a free `n` that is
  not bound by `s`. The source `decode` (`Codec/Decode.lean:31`) is
  `{α : Type} (d : Codec α) {n : Nat} (s : Bytes n)`, i.e. `d` is an _explicit_
  argument — the README's `Codec α → …` omits it, which is a different type.
  Small, but the block is labelled "the laws that make it a codec" and is the
  most-copied part of the README.
- **SUGGESTED FIX** Write `decode (d : Codec α) {n : Nat} (s : Bytes n)` and
  `Rel d x s ↔ (x, Suffix.empty _) ∈ decode d s` (or bind `n` via `s : Bytes n`).

---

## 19. LOW — `[D8]`-adjacent claim that `encode` being partial "is the paper's `Maybe` printer kept as-is" is right, but "`empty`/`pure x`/`subset p` reject out-of-domain values" mixes `Iso` and `Codec` namespaces

- **LOCATION** `README.md:150-153`
- **THE CLAIM** "`empty`/`pure x`/`subset p` reject out-of-domain values".
- **WHY IT IS WRONG** `empty` and `pure x` are `Codec` constructors
  (`Codec/Codec.lean:44`, `:47`); `subset p` is an `Iso` (`Codec/Iso.lean:219`),
  not a `Codec`. `encode` handles `Codec.empty → none`, `Codec.pure x₀ → if x =
x₀ then some ⟨0, …⟩ else none` (`Codec/Encode.lean:34-35`); `subset` only
  reaches `encode` wrapped in `Codec.iso`. Listing three names from two
  different namespaces in one sentence invites a reader to look for a
  `Codec.subset`, which does not exist.
- **SUGGESTED FIX** "`Codec.empty`, `Codec.pure x`, and any `iso` whose `Iso`
  rejects (e.g. `subset p`) make `encode` return `none`."

---

## 20. LOW — "`Codec` is a description _value_, not the §3.4 typeclass" (`[D6]`) understates the paper: §3.4's class is `Syntax`, and `Codec` _is_ still a `Syntax`-like interface at the type level

- **LOCATION** `README.md:122-133`
- **THE CLAIM** "The paper embeds syntax descriptions polymorphically (a `Syntax`
  typeclass, with `$`/`∗`/`|`/`pure`/`token` as methods). `codec` instead makes
  `Codec` an inductive AST."
- **WHY IT IS WRONG** Accurate about the paper (`PAPER.md:437-449`) and about
  `codec`, but "instead" implies the polysemy is _lost_. The paper's whole point
  (§3, `PAPER.md:213-232`) is polysemous interpretation via instances; `codec`
  keeps two interpreters (`decode`/`encode`) and a denotation (`Rel`) over one
  AST — so `codec` has the _same_ four interpretations with the class resolved
  to a fixed AST. Saying "instead" sells the paper's design short and makes
  `[D6]` look like a semantic loss when it is a representation choice.
- **SUGGESTED FIX** "The paper resolves the interpretation by _typeclass
  instance_; `codec` resolves it by _interpreter function_ over a fixed AST.
  Both keep the four readings (`decode`, `encode`, `Rel`, and the derived
  combinators); only the dispatch differs."

---

## 21. LOW — `[S2]`'s renaming list omits the two renames a porter most needs (`many`→triple, `chainl1`), and mislabels the entry "A rename only" while the README elsewhere insists `[S6]` is _not_ a rename

- **LOCATION** `README.md:159-162` (`[S2]`) vs `README.md:180-196` (`[S6]`)
- **THE CLAIM** "`Syntax`/`parse`/`print`/`token` … become `Codec`/`decode`/
  `encode`/`byte`. A rename only."
- **WHY IT IS WRONG** The mapping `token → byte` is a rename in name only — the
  _carrier_ changes (`Char` → `UInt8`), which is `[D1]`; presenting it under a
  "rename only" heading double-counts `[D1]` as cosmetic. `parse`'s paper type is
  `Parser α → String → [α]` (whole-string, filtered) versus `decode`'s
  `List (α × Suffix n)` — that change is `[D2]`, also counted here. So `[S2]`
  claims three of its four renames are behaviour-preserving when they are
  precisely the ones listed as departures.
- **SUGGESTED FIX** Restrict `[S2]` to `Syntax → Codec` and `print → encode`
  and say the other two are covered by `[D1]`/`[D2]`.

---

## 22. LOW — `[S4]`'s "the obvious `inverse ∘ foldl ∘ inverse` is type-incoherent for the step type" is true but under-explained, and the entry never names `foldr`'s actual witness type

- **LOCATION** `README.md:166-172` (`[S4]`)
- **THE CLAIM** "The right-fold dual is a distinct definition (the obvious
  `inverse ∘ foldl ∘ inverse` is type-incoherent for the step type)."
- **WHY IT IS WRONG** Verified: `foldl : Iso (α × List β) α` with step
  `Iso (α × β) α`, `foldr` needs step `Iso ((α × β) × α) α` with
  `MeasureDecreasesR` (`Codec/Combinators.lean:237-241`). So the claim is
  correct, and the dual's step type is genuinely different — but the README
  never states what `foldr`'s step/witness type is, so "type-incoherent for the
  step type" is an assertion a reader cannot check. Given the AGENTS.md standing
  preference ("more honest about its preconditions"), state the type.
- **SUGGESTED FIX** Add: "`foldl : Iso (α × List β) α` over `Iso (α × β) α`;
  `foldr` needs `Iso ((α × β) × α) α`, which no composition of `foldl` and
  `inverse` produces."

---

# Summary

The README's paper scholarship is **mostly accurate** — the §3.1 "modulo
equivalence classes" quote, the §6.3 `ignore :: α → Iso α ()` definition and its
"not a strict partial isomorphism" remark, the §4.3 "generate and concatenate
infinite lists" quote, the §5.3 `iterate` definition, and the §7.5 "would be
interesting to see" sentence are all **verbatim correct**, and every section
number checked (3.1, 3.3, 3.4, 4.1–4.4, 5.1–5.3, 6.1, 6.3, 7.5) resolves to the
right place in `PAPER.md`. Every code claim checked against the source is also
correct: `Iso.law : ∀ a b, apply a = some b ↔ unapply b = some a`
(`Codec/Iso.lean:33`), `decode : … → List (α × Suffix n)`
(`Codec/Decode.lean:31`), `encode : … → Option (Sigma fun n => Bytes n)`
(`Codec/Encode.lean:24`), `Bytes n := Fin n → UInt8` (`Codec/Codec.lean:68`),
seven constructors (`Codec/Codec.lean:34-55`).

The failures are in **derivation, not quotation**: two CRITICAL — `CHANGELOG.md`
advertising `Bytes := List UInt8` against a `Fin n → UInt8` source and README
(an arity-changing lie in the same repo), and `[D2]` filed as a departure while
being described as a non-departure and mis-attributed to §4.3's `Rel`. Four HIGH
— the mis-shaped reasons in `[D4]` (injectivity, not "unapply cannot invert
both"), `[D7]`'s invented "chain-isolated in both directions" precondition
(the real one is `MeasureDecreases` on a `Nat`-valued measure) plus "`foldl` is
all `chainl1` needs" (there is no `chainl1` value), `[S1]` vs `[S4]`
contradicting each other on whether `foldl`'s law is unconditional, and the
undersold framing of the §7.5 hook. Fix the CHANGELOG/README `Bytes` split
first; it is the only finding that actively misinforms a build.

---

# Adversarial Lean code review — `lean-codec` `Codec/*.lean` + `Codec/ByteSlice.c`

Scope: 10 Lean files (`Codec/Codec.lean`, `Iso.lean`, `Decode.lean`, `Encode.lean`,
`Sound.lean`, `Combinators.lean`, `Packed.lean`, `DecodeOne.lean`, `ByteSlice.lean`,
`Normal.lean`) plus `Codec/ByteSlice.c`. Repo not modified; probes in `/tmp`.

Method: read all files; `#print axioms` spot-checks on 18 theorems (all repo claims
verified); ran the built `bench` binary at `n=4096` to exercise the C seams; reasoned
C-vs-Lean clause by clause on all four seams. `grep -rn 'sorry' Codec/ Codec.lean`
→ **zero** (only the word appears in prose). No `axiom`, `unsafe` (outside `Bench.lean`),
`partial`, `opaque`, `native_decide`, or `implemented_by` anywhere in `Codec/` — the only
`Classical` mentions are in comments. `Iso.law` has zero escape hatches; all 14 `law :=`
proofs are real.

Severity keys: **CRITICAL** (unsound / C-vs-Lean divergence), **HIGH** (claim not
upheld), **MEDIUM** (gap / wasted work), **LOW** (hygiene / honesty), **INFO**.

---

## Findings

### 1. HIGH — `Codec/ByteSlice.lean` — `byteSlice` is the primary trust seam yet has **no Lean law** pinning it

**LOCATION:** `Codec/ByteSlice.lean:67-70` (def), and absent from the module's two theorems (`blitBytes_spec:114`, `findByte_spec:141`).
**WHAT IS WRONG:** `blitBytes` and `findByte` each get an `rfl`-clean refinement theorem tying the def to a spelled-out spec. `byteSlice` — the _headline_ Layer-2 seam, and the only seam with a library-internal caller (`commitRemainder`) — has **no** `byteSlice_spec`. Its "specification" exists only as prose in the module header plus the def body itself. So the one seam every comment calls "the specification" has no checkable Lean statement, while its two siblings do. This asymmetry is exactly backwards.
**EVIDENCE:** `grep -n 'byteSlice_spec' Codec/*.lean` → no matches. The module has exactly 2 `theorem`s. A spec is trivially statable — `example (a : ByteArray) (i : USize) : byteSlice a i = ByteArray.mk (a.data.extract i.toNat a.data.size) := rfl` compiles clean (`/tmp/probe3.lean`). The bench (`Bench.lean:261-264`) inline-recomputes the spec instead of citing a theorem.
**SUGGESTED FIX:** Add `theorem byteSlice_spec (a : ByteArray) (i : USize) : byteSlice a i = ByteArray.mk (a.data.extract i.toNat a.data.size) := rfl` and have `commitRemainder_spec` and the bench both cite it, mirroring the `blitBytes`/`findByte` pattern.

---

### 2. HIGH — `Bench.lean:684` (call) / `Codec/ByteSlice.c` — the only runtime C↔Lean check is **unreachable** in the default run

**LOCATION:** `Bench.lean:684` (`Codec.Bench.benchSeamBoundaries` called last in `main`); `Bench.lean:298-310` (`benchScalarIndexRead`).
**WHAT IS WRONG:** `benchSeamBoundaries` is the _sole_ runtime evidence that the hand-written C matches the Lean bodies across out-of-range cases (the "matches byte-for-byte on every input" claim). It is invoked **dead last** in `main`, after every linear lane. The default run dies earlier: with `n` defaulting to 1 MiB the `for size in [n/4, n/2, n]` loop hits `benchScalarIndexRead` first, and at `size = n/4` a pre-existing runtime bug (`uncaught exception: scalar-index read: expected byte 0x01`) aborts `main` before the seam checks ever run. Net effect: the seam boundary test never executes in a default `bench` invocation, and a CI that only checks exit status sees a _stale_ success or a crash _unrelated_ to the seam.
**EVIDENCE:** Ran the built binary: `./.lake/build/bin/bench` → `scalar-index read [0]: …` then `uncaught exception: scalar-index read: expected byte 0x01` (exit non-zero) _before_ "seam boundaries OK". Only with an explicit `./.lake/build/bin/bench 4096 64` does it reach `seam boundaries OK (byteSlice/findByte/blitBytes out-of-range value-checks)`.
**SUGGESTED FIX:** Move `benchSeamBoundaries` to the very first thing in `main` (it is cheap and needs no `n`), and/or fix the `benchScalarIndexRead` n=0 bug so the default run reaches the seam checks. Until then the "checkable, not asserted" claim (Bench.lean:252) is false in practice.

---

### 3. MEDIUM — `Codec/ByteSlice.c:89-110` — `findByte` C/Spec agree on `off > size` only because both return `none`; the Lean spec's `off + i` is a `USize` add that can in principle wrap

**LOCATION:** `Codec/ByteSlice.c:96-107` vs `Codec/ByteSlice.lean:144-149`.
**WHAT IS WRONG:** The Lean body returns `some (off + i.toUSize)` where `off : USize` and `i : Nat` (from `findIdx?`). The C returns `lean_box_usize(idx)` with `idx = hit - base` as a raw `size_t` (i.e. the _absolute_ index). These agree for every realistic input because `off < n ≤ USize.max` and `i < n`. But the Lean `+` is `USize` addition (mod 2^64) while the C `idx` is a plain `size_t` absolute index — they are only equal under the unstated side condition `off.toNat + i < 2^64`. No theorem states or uses this; the agreement is by construction on the C side but _not_ guaranteed by the Lean body's arithmetic on paper. A reader could construct (hypothetically, on a > 2^63-byte array) a divergence. Not reachable in practice, but the "must match the Lean body on **every** input" claim (C header, line 88) is stronger than the Lean body's own arithmetic warrants.
**EVIDENCE:** `Codec/ByteSlice.lean:147` `| some i => some (off + i.toUSize)` (USize add); `Codec/ByteSlice.c:104` `size_t idx = hit - base` (absolute, no add). Bench only tests `off ∈ {0,3,5,6}` on a 5-byte array.
**SUGGESTED FIX:** Either state the `off.toNat + i < USize.size` side condition in `findByte_spec`'s docstring and note the C relies on it, or (cleaner) note in the C that `idx` is the absolute index and the Lean `off + i` equals it precisely because `i` is relative to `off` — i.e. spell out the equivalence rather than asserting "every input" without the bound.

---

### 4. MEDIUM — `Codec/Packed.lean:80-83` header claims `commitRemainder` is the commit path; the actual decoder does **not** use it

**LOCATION:** `Codec/Packed.lean:80-83` (docstring on `decodeArrayFast`) and `Codec/Packed.lean:99-104` (`decodeFullArray`).
**WHAT IS WRONG:** The header says "each `byteSlice`/`memcpy` is deferred to a `commitRemainder` at commitment time". But `decodeFullArray` — the only full-consumption decoder — builds its suffix with `ByteArray.mk ((a.toList.drop c).toArray)`, i.e. a **list-materializing** transport, not `commitRemainder`/`byteSlice`. So none of the four Layer-2 seams is on any library code path; the four C seams plus `commitRemainder` are exercised _only_ by `Bench.lean`. The `ByteSlice.lean` header does admit "no library-internal caller", but the `Packed.lean` header contradicts that by naming `commitRemainder` as the deferred commit. A reader of `Packed.lean` alone is misled into thinking the memcpy seam is wired in.
**EVIDENCE:** `grep -n 'commitRemainder\|byteSlice' Codec/Packed.lean` → only line 496 (`commitRemainder_spec`, a `rfl` identity) and prose at 80-83. `decodeFullArray` body (line 103) uses `toList.drop c`. No `commitRemainder` call anywhere outside `ByteSlice.lean` and `Bench.lean`.
**SUGGESTED FIX:** Either reword `Packed.lean:80-83` to say the memcpy commit is _available_ (`commitRemainder`) but the proven decoder intentionally uses the choice-clean `toList.drop` transport, or actually wire `commitRemainder` into a packed path and prove the two transports equal. Do not leave the two module headers disagreeing about whether the seam is live.

---

### 5. LOW — `Codec/Iso.lean:200,219` — `element` and `subset` are dead API (zero callers)

**LOCATION:** `Codec/Iso.lean:200` (`element`), `Codec/Iso.lean:219` (`subset`).
**WHAT IS WRONG:** Both are non-trivial partial isomorphisms with real `law` proofs, but neither is used by any `Codec`, combinator, or downstream base in this repo. `subset` in particular looks like it should back a "restricted codec" but does not. Dead proved API is not unsound, but it inflates the proof surface a reviewer must trust and is never exercised by any law or bench.
**EVIDENCE:** `grep -rn 'Iso.subset\|Iso.element' Codec/` (excluding `Iso.lean` itself) → no hits; `Codec/` has no occurrence outside the defs and their docstrings.
**SUGGESTED FIX:** Either delete them, or add a one-line comment that they are public API kept for consumers (and a `Bench`/downstream reference), so a reviewer does not mistake them for load-bearing.

---

### 6. LOW — `Codec/ByteSlice.lean:141-148` — `findByte_spec` depends on `[propext]` while `blitBytes_spec`/`byteSlice_spec` are axiom-free

**LOCATION:** `Codec/ByteSlice.lean:141-148`.
**WHAT IS WRONG:** The sibling seam laws report "no axioms"/`[propext]` respectively; `findByte_spec` needs `[propext]` because `Array.findIdx?` uses `DecidableEq UInt8` through `BEq`/`==`. This is fine for the gate (`[propext]` is allowed), but it is a _visible inconsistency_ in a module whose header repeatedly claims these are "`rfl`-clean, `[propext, Quot.sound]`-only" — the header's framing implies a uniformity the three laws do not have (empty vs `[propext]`).
**EVIDENCE:** `#print axioms` → `findByte_spec`: `[propext]`; `blitBytes_spec`: none; `commitRemainder_spec`: none.
**SUGGESTED FIX:** State per-law axiom footprint in the docstrings (they nearly do) and note `findByte_spec`'s `[propext]` is from `DecidableEq UInt8`, so it is not mistaken for drift.

---

### 7. LOW — `Codec/Sound.lean:367-383` — `decodeFull_spec` takes `huniq` (full-consumption uniqueness) as a hypothesis, never derives it

**LOCATION:** `Codec/Sound.lean:367-383`.
**WHAT IS WRONG:** The reverse direction of `decodeFull_spec` ("`xs` is the full-consumption result ⇒ `decodeFull … = some xs`") is only proved **given** `huniq : ∀ x y, (x,empty) ∈ decodeRepeat … → (y,empty) ∈ … → x = y`. That is exactly the "full-consumption result is unique" property one would expect the _decoder law_ to establish, and it is _assumed_, not proved, here. This is legitimate (the docstring says so, and `decodeFull_some` gives the forward direction unconditionally), but it means `decodeFull_spec` cannot be read as "the full decoder is deterministic" — it is conditional on determinism. Callers must prove `huniq` themselves.
**EVIDENCE:** Signature `Codec/Sound.lean:368-371` carries `huniq`; body line 381 uses `huniq s hys hmem` to rewrite `ys` to `xs`. No theorem in the repo supplies `huniq` for a concrete `p` (grep shows no `huniq` producer).
**SUGGESTED FIX:** Either derive `huniq` from `Unambiguous`/`Functional` (the repo already has `relUnambiguous`/`relFunctional`) and expose `decodeFull_spec_unambiguous`, or add one concrete instance so the hypothesis is demonstrably satisfiable in-tree. As is, the "totality boundary" story is one unproven premise short of a determinism law.

---

### 8. INFO — `Codec/DecodeOne.lean:226`, `Codec/Packed.lean:388`, `Codec/Encode.lean:281` — "zero `sorry`, zero `Classical.choice`" comments are **true** (verified)

**LOCATION:** the three docstring claims.
**WHAT IS WRONG:** Not wrong — recorded because the review's mandate is to check these, and a reader should know they were tested, not trusted.
**EVIDENCE:** `grep -rn 'sorry' Codec/ Codec.lean` → only the 3 prose mentions, zero `sorry` terms. `#print axioms` on `roundtrip`, `decodeFull_spec`, `decodeArray_bounded_upper`, `encodeArray_eq`, `pushBytesFrom_eq`, `decodeRepeat_spec`, `decodeChainl1_spec`, `encode_injective_of_unambiguous`, `productive_iff_consumesByte`, `encode_of_decode` → all `[propext, Quot.sound]`; `decodeNormal_encode`/`fill_fixed`/`fill_inj`/`fill_surj`/`decodeNormal_of_fixed` → `[propext]` or none. No `Classical.choice` anywhere tested.
**SUGGESTED FIX:** None; keep the gate.

---

### 9. INFO — `Codec/Normal.lean:131-134` — `Normalizer.idem` **is** load-bearing and cannot be smuggled (verified)

**LOCATION:** `Codec/Normal.lean` (`Normalizer`, `fill`, `fill_fixed`, `fill_surj`).
**WHAT IS WRONG:** Not wrong — answering the review's Q7. `Normal S norm` = `{raw // norm raw = raw}` is well-formed for _any_ `norm` (the `fixed` field is a hypothesis, not a derived fact), so a non-idempotent `norm` can still have `Normal` values. But `fill nz s := ⟨norm s, nz.idem s⟩` needs `nz.idem` to _produce_ the `fixed` field; without it `fill` does not typecheck. Hence `fill_surj` (every normal form is `fill`'s image) genuinely uses idempotence, and no idempotence-free `Normalizer` can be smuggled through `fill`. `fill_fixed` is genuinely `(fill nz s).fixed` — its hypothesis `nz` is used only through `fill`.
**EVIDENCE:** `#print axioms Codec.fill_fixed` → "does not depend on any axioms"; `fill_surj`/`fill_inj` → `[propext]`. `Normalizer` has a single field `idem` consumed only in `fill`.
**SUGGESTED FIX:** None.

---

### 10. INFO — `Codec/Iso.lean:566-597,650-681` — `MeasureDecreases.dec` is load-bearing (termination is honest)

**LOCATION:** `Codec/Iso.lean:531-533`, `:345-355` (`unfoldBy`), `Codec/Decode.lean:115-137` (`decodeRepeat`), `Codec/Encode.lean:104-107` (`pushBytesFrom`).
**WHAT IS WRONG:** Not wrong — answering the review's Q5. Every apparent recursion is genuine `WellFounded.fix` (or `termination_by n - i; decreasing_by … omega`) with a real decreasing measure. `decodeRepeat` guards its recursion with `h : ConsumesByte p` and passes `h x s t hmem` as the decreasing proof; `unfoldBy` passes `u.dec a a' b hs`. No `partial`, no `decreasing_by sorry`.
**EVIDENCE:** `grep -rn 'decreasing_by\|termination_by\|WellFounded\|wfRel'` → 17 hits, all legitimate (`omega`/measure-based, no `sorry`); `grep -rn 'partial ' Codec/` → only prose.
**SUGGESTED FIX:** None.

---

### 11. LOW — `Codec/ByteSlice.c:31-85` — the C comments assert the `blitBytes` clamps "mirror the Lean body clause by clause", but the C clamps in a different _order_ and relies on `min` associativity/commutativity that is never stated

**LOCATION:** `Codec/ByteSlice.c:64-76` vs `Codec/ByteSlice.lean:121-129`.
**WHAT IS WRONG:** The Lean body computes `lc := min len (min (n-dc) (slen-sc))` — a single `min` over three terms. The C computes `copyLen = len`, then clamps by `n-dstOff`, then by `slen-srcOff`, in a specific _sequential_ order, with the destination clamp applied **before** `slen` is even read. These agree only because `min` is associative and commutative and both sides never underflow (the C uses `> n - dstOff` forms specifically to avoid overflow, which the comments credit). The comments claim "term-for-term" agreement (line 61-62, "this is what makes the C's single `memcpy` match the body term-for-term"), which is _not_ term-for-term — it is _value_-for-value via `min` AC. For the stated "trusted, must match byte-for-byte" posture the distinction matters: a reader verifying the claim must supply the AC reasoning themselves, and the "term-for-term" wording overstates it.
**EVIDENCE:** Lean: `lc := min len.toNat (min (n - dc) (slen - sc))` (single nested `min`). C: `if (dstOff > n) dstOff = n; if (copyLen > n - dstOff) copyLen = n - dstOff; if (srcOff > slen) srcOff = slen; if (copyLen > slen - srcOff) copyLen = slen - srcOff;` (sequential clamps). Both give `min(len, n-dc, slen-sc)` for all inputs (I checked the four boundary quadrants), so no divergence — but the proof obligation is `min`-AC, not syntactic.
**SUGGESTED FIX:** Reword the C comment from "term-for-term" to "value-for-value (`min` is associative/commutative, and the `> n - off` forms are overflow-stable)" so the trust argument is stated, not implied.

---

### 12. LOW — `Codec/ByteSlice.c:56-60` — `blitBytes` C allocates `lean_alloc_sarray(1, n, n)` where `n = dst` size, but the Lean body returns `dst[0,dc) ++ src[..] ++ dst[dc+lc,n)` whose length is `n` **only** because `dc ≤ n` and `dc+lc ≤ n`; the C's `n` follows from those same clamps, unstated in C

**LOCATION:** `Codec/ByteSlice.c:74-80`.
**WHAT IS WRONG:** The C allocates exactly `n = lean_sarray_size(dst)` bytes and then `memcpy(r, dst, n)` followed by `memcpy(r + dstOff, src + srcOff, copyLen)`. The two writes overlap only in benign order (full copy first, then window overwrite). But the _reason_ the total output length is `n` — rather than `n + copyLen` or `n - dc + lc` — is that the second `memcpy` writes _inside_ the already-copied `[0,n)` window, i.e. `dstOff + copyLen ≤ n`. The Lean body makes this explicit by construction (`extract 0 dc ++ … ++ extract (dc+lc) n` sums to exactly `n` because the three pieces partition `[0,n)`). The C relies on the clamp at line 72 for it without a comment. This is correct but is the one place where a future edit that "simplifies" the clamping (e.g. clamps only against `len`) would silently produce a buffer of the wrong length rather than an out-of-bounds write.
**EVIDENCE:** `Codec/ByteSlice.c:72` `if (copyLen > n - dstOff) copyLen = n - dstOff;` is exactly the invariant `dstOff + copyLen ≤ n` that keeps the second `memcpy` in-bounds and the total length `n`. Lean: `Codec/ByteSlice.lean:127-129`.
**SUGGESTED FIX:** Add a one-line C comment at the allocation: `// the window write below stays inside [0,n) because copyLen ≤ n-dstOff (line above); total length is n, matching the Lean three-piece partition.`

---

### 13. INFO — C-vs-Lean seam table (clause-by-clause verdict)

For the record, since the mandate prioritises the Layer-2 seam. All four seams were compared clause by clause; **no divergence found** on reachable inputs.

| seam              | empty input                | `i == size`     | `i > size`                                      | overflow                                       | NULL                    | verdict                                         |
| ----------------- | -------------------------- | --------------- | ----------------------------------------------- | ---------------------------------------------- | ----------------------- | ----------------------------------------------- |
| `byteSlice`       | `len=0`, skips memcpy ✓    | `len=0` ✓       | `i<n` false ⇒ `len=0` ✓ (Lean `extract` clamps) | `n-i` guarded by `i<n` ✓                       | n/a                     | **match**                                       |
| `blitBytes`       | fine                       | `dc=n ⇒ lc=0` ✓ | `dstOff=n` ✓; `srcOff=slen ⇒ lc=0` ✓            | `> n-off` forms deliberately overflow-stable ✓ | n/a                     | **match** (mod finding 11/12 wording)           |
| `findByte`        | `off>=n` ⇒ none ✓          | none ✓          | none ✓                                          | `idx` absolute `size_t`, no add ✓              | `memchr` NULL checked ✓ | **match** (mod finding 3 side condition)        |
| `commitRemainder` | delegates to `byteSlice` ✓ | ✓               | ✓                                               | inherited ✓                                    | n/a                     | **match** (but no `byteSlice_spec` — finding 1) |

`lean_alloc_sarray(1, len, len)` in `byteSlice` and `(1,n,n)` in `blitBytes`: element size 1 and capacity = size, so `lean_sarray_size` == element count == byte count; no capacity/size confusion.

---

### 14. INFO — `Codec/Decode.lean:398-533` — `decode_genuine_suffix`/`decode_genuine_suffix_pointwise` are real invariants, not restatements

**LOCATION:** `Codec/Decode.lean:410,520`.
**WHAT IS WRONG:** Not wrong. These are the bridge `Packed.lean` needs (an _arbitrary_ `Suffix n` need not be a suffix of `s`; the theorem pins `t.bytes = bdrop t.consumed s` for suffixes that actually come out of `decode`). Spot-checked as non-vacuous: the statement genuinely constrains both `t.bytes` and `t.consumed` against `s`, with a pointwise proof obligation (`Fin` reindexing), not a definitional unfold.
**EVIDENCE:** `#print axioms` on the surrounding packed laws (`decodeArray_eq` consumers) → `[propext, Quot.sound]`; the pointwise form requires `suffix_consumed_lt` (a real `Fin`-bound arithmetic fact).
**SUGGESTED FIX:** None.

---

### 15. LOW — `Bench.lean` `benchSeamBoundaries` (advisory, outside the 10 files but it is the _evidence_ for seams) — no aliasing case and no `src`/`dst` same-buffer case for `blitBytes`

**LOCATION:** `Bench.lean:274-293` (`cases` list).
**WHAT IS WRONG:** The six `blitBytes` cases cover normal / short-src / dstOff-past-end / srcOff-past-end / len-past-end / len-0, but not the case where `src` and `dst` are the **same `ByteArray`** (aliasing). The C copies `dst` fully into a fresh `r` first and then reads `src` (=== `dst`, unmodified), so it _does_ match the Lean spec (which reads the original `src`), but that is exactly the kind of thing that would break if someone "optimised" the C to write in place. Since this is a trusted-not-proven seam, the aliasing case deserves an explicit value-check.
**EVIDENCE:** `Bench.lean:274-282` case list; no entry passing the same array as both `dst` and `src`. C body `ByteSlice.c:74-80` copies full `dst` before reading `src`, so it is currently safe.
**SUGGESTED FIX:** Add `let got := blitBytes a5 1 a5 0 2` (same buffer, overlapping windows) to `cases`/a separate check, compared against the Lean body.

---

### 16. INFO — `Iso.law` enforceability: **no** escape hatches found

**LOCATION:** `Codec/Iso.lean:25-32` (structure), all `law :=` sites.
**WHAT IS WRONG:** Not wrong — answering Q2. `Iso.law` is a `Prop` field of a `structure`, so an `Iso` value cannot be constructed without a proof. All 14 constructions (`id`, `trans`, `prod`, `associate`, `commute`, `unit`, `element`, `subset`, `inverse`, `optionSome`, `nil`, `cons`, `foldl`, `foldr`) prove the law with real case analysis; none uses `by trivial`, `sorry`, `native_decide`, or an axiom. `grep -rn -E '\b(axiom|unsafe|partial|opaque|native_decide|implemented_by)\b' Codec/` → no hits outside prose. `Normal.lean` adds no `Iso` (0 `law :=` there) and explicitly does **not** weaken the law.
**EVIDENCE:** `grep -c 'law :=' Codec/Iso.lean` = 14; `#print axioms` on representative law-dependent theorems (`roundtrip`, `encode_of_decode`) clean.
**SUGGESTED FIX:** None.

---

### 17. LOW — `Codec/Sound.lean:621-627` — `Unambiguous`/`Functional` are `Prop`s defined but never _discharged_ for any concrete `Codec` in-tree

**LOCATION:** `Codec/Sound.lean:621`, `:624`, `:712`, `:716`.
**WHAT IS WRONG:** `Unambiguous`, `Functional`, `relFunctional`, `relUnambiguous` are defined and used as hypotheses in three theorems (`encode_of_decode`, `encode_injective_of_unambiguous`, `encodeRepeat_ne_none`-adjacent), but no theorem in this repo _establishes_ any of them for a concrete `d` (e.g. `Unambiguous Codec.byte`). They are therefore never exercised end-to-end: the `hd : Functional d` in `encode_of_decode` is a free hypothesis, and nothing shows the repo's own codecs satisfy it. Downstream (`lean-basen`) presumably discharges them, but in-tree the encoder-completeness story is conditional on an uninstantiated `Prop`.
**EVIDENCE:** `grep -n 'Unambiguous\|Functional' Codec/*.lean` → definitions + hypotheses only; no `theorem ... : Unambiguous ...` producer in this repo.
**SUGGESTED FIX:** Add the trivial base instances (`Unambiguous Codec.byte`, `Functional Codec.byte`) as smoke tests that the definitions are inhabited, so a typo in the definition (e.g. quantifying over the wrong `s`) cannot go unnoticed.

---

### 18. INFO — `Codec/ByteSlice.lean:48-53` — the "provably unused / standalone seam" claim is honest and accurately worded

**LOCATION:** `Codec/ByteSlice.lean:48-53`.
**WHAT IS WRONG:** Not wrong. Unlike `Packed.lean`'s header (finding 4), this one correctly states `byteSlice` "has _no_ library-internal caller" and that the "wired only onto a packed path" rule is a how-to-use constraint, "not a claim that it is currently in the library critical path". Good honesty; flagged only so the _other_ header's contradiction (finding 4) is fixed toward this wording.
**EVIDENCE:** text at `ByteSlice.lean:48-53`.
**SUGGESTED FIX:** Copy this wording into `Packed.lean:80-83`.

---

## Summary

- **CRITICAL: 0** — no C-vs-Lean divergence on reachable inputs; no `sorry`/`axiom`/escape hatch; `Iso.law` intact; all axiom claims verified.
- **HIGH: 2** (#1 missing `byteSlice_spec`; #2 seam runtime check unreachable in the default bench run).
- **MEDIUM: 2** (#3 `findByte` USize-add side condition unstated; #4 `Packed.lean` header contradicts `ByteSlice.lean` header about seam wiring).
- **LOW: 7** (#5 dead API, #6 axiom-footprint drift, #7 `huniq` unproved-assumed, #11 "term-for-term" overstated, #12 allocation-length invariant implicit, #15 no aliasing test, #17 `Unambiguous` never discharged).
- **INFO: 7** (#8, #9, #10, #13, #14, #16, #18) — most are verifications of claims the review set out to test, recorded so they are known-tested rather than trusted.

Verified clean: zero `sorry`; zero `Classical.choice` in all 18 spot-checked theorems; `fill_fixed` depends on no axioms; `Normalizer.idem` load-bearing and un-smugglable; termination honest (`WellFounded.fix`/real measures, no `decreasing_by sorry`); the four C seams match their Lean bodies on empty / `i==size` / `i>size` / overflow / `memchr`-NULL for all reachable inputs.

---

# Adversarial review — `/Users/user/_/lean-codec/AGENTS.md` (309 lines)

Reviewer scope: staleness, self-contradiction, cross-document contradictions,
self-violation of its own rules, unenforced ("asserted but not gated") claims,
whether every bash command names the right repo, incomplete guidance, and a
missing operational rail.

Baseline facts (all commands run from `/Users/user/_/lean-codec`, tools via
`nix develop --command`; **no repo files were modified**):

```
$ nix develop --command openspec list --json
{"changes":[
  {"name":"codec-normal-form-case-quotient","completedTasks":16,"totalTasks":16,"status":"complete"},
  {"name":"basen-rfc-conformance-theorems","completedTasks":31,"totalTasks":31,"status":"complete"},
  {"name":"lean-basen","completedTasks":18,"totalTasks":25,"status":"in-progress"}],
 "root":{"path":"/Users/user/_/lean-codec","source":"nearest"}}

$ nix develop --command openspec validate --all --no-interactive
Totals: 8 passed, 0 failed (8 items)

$ nix eval --raw '.#packages.aarch64-darwin.bench.name'   → codec-bench-0.1.0
$ nix eval --json '.#checks.aarch64-darwin' --apply builtins.attrNames → ["formatting","lean","openspec"]
$ nix eval --raw '.#checks.aarch64-darwin.lean.name'      → codec-check-0.1.0
$ nix eval --json '.#packages.aarch64-darwin' --apply builtins.attrNames → ["bench","default","native"]
```

**Verdict up front:** the counts are right (16/16, 31/31, 18/25 all confirmed);
the `Current state` block is **not** internally self-contradictory; the file has
**not** appended a session-status section. The real defects are elsewhere:
one flat contradiction with `CHANGELOG.md` about what `Bytes` is, two unenforced
claims presented as gates, a cargo-culted `nix build .#bench`, commands
documented for the wrong repo, an over-narrow `Classical.choice` trap section
(reproduced here), a line-swap garbling the verification recipe, and an omission
that would let the "bad import" regression recur.

---

## 1. SEVERITY: HIGH — `Bytes` is defined two different ways across the doc set, and AGENTS.md sides with the one `Codec.lean` contradicts

**LOCATION:** AGENTS.md:206–210 (bullet _"The `Bytes n` spec substrate is single"_); cf. CHANGELOG.md:55–56; README.md:206, 215, 269; `Codec/Codec.lean:68`.

**WHAT IS WRONG:** AGENTS.md states, and calls authoritative, that
`Bytes n := Fin n → UInt8`. `CHANGELOG.md` (the file AGENTS.md itself designates
as the home of "what landed") states, in the same `[Unreleased]` section, that
`` `Bytes` (`abbrev Bytes := List UInt8`) `` was added "as the named proof
substrate, used throughout the core in place of the bare `List UInt8`". Those are
different types with different definitions (`List UInt8` vs a length-indexed
function), so the "single substrate" requirement can only be satisfied by one of
them. `Codec/Codec.lean` proves the README right and the CHANGELOG wrong:

**EVIDENCE:**

```
$ grep -n 'abbrev Bytes' Codec/Codec.lean CHANGELOG.md README.md
Codec/Codec.lean:68:abbrev Bytes (n : Nat) : Type := Fin n → UInt8
CHANGELOG.md:55:- `Bytes` (`abbrev Bytes := List UInt8`) as the named proof substrate, used
README.md:206:`Bytes n := Fin n → UInt8`. ...

$ grep -n 'List UInt8' README.md
209:indexed load in the emitted IR. There is no second `List UInt8`/`Array`/`ByteArray`/
```

(README line 209 explicitly _forbids_ a `List UInt8` spec carrier.) Meanwhile
AGENTS.md's "Where the truth lives" table (line ~85) makes `README.md` the
authority for "what is this library" and `CHANGELOG.md` nothing at all, so a
reader following AGENTS.md's own precedence rule is fine — but a reader who
checks the CHANGELOG (the file AGENTS.md tells them holds "what landed") gets the
exact carrier README condemns as "the defect". This is the single highest-risk
contradiction in the set: it can send an agent to implement `List`-based transport
lemmas and re-open the `Array.extract`/`Array.toList` `Classical.choice` leak that
README:231 says was the whole point of collapsing the carrier.

**SUGGESTED FIX:** Add one line to AGENTS.md's truth table row for
"What is this library": _"`Bytes n` means `Fin n → UInt8` (`Codec/Codec.lean:68`).
`CHANGELOG.md`'s `abbrev Bytes := List UInt8` entry is a **stale historical
record**, not a definition; do not implement against it."_ Then correct the
CHANGELOG entry itself (outside this review's no-modify scope) — a changelog that
misstates a public type name is worse than a changelog gap.

---

## 2. SEVERITY: HIGH — "zero `sorry`" is asserted twice as _the_ gate, but nothing in the build enforces it

**LOCATION:** AGENTS.md:28 ("the proof gate is the same build with zero `sorry`"),
AGENTS.md:97–98 ("Every law is `[propext, Quot.sound]`-only, zero `sorry`"),
AGENTS.md:199–201 ("Axiom discipline … zero `sorry`. `#print axioms Codec.roundtrip`
is the check"). Mechanism claim: AGENTS.md:174–178.

**WHAT IS WRONG:** Three separate problems, all in the same claim.

(a) **There is no `sorry`-forbidding step anywhere.** The gate is `lake build`;
`lake build` compiles `sorry` happily and emits a _warning_, not an error. The
`check` derivation (`default.nix:95–105`) runs exactly `lake build` with **no
`targets`** and installs an empty `$out`; it does not grep for `sorry`, does not
set `-DwarningAsError`, and does not fail on warnings. So "zero `sorry`" is an
observation about the current tree, not an invariant the gate enforces. An agent
can stub a theorem to `sorry` and `nix build .#checks.…` still goes green.

(b) **The `#print axioms Codec.roundtrip` example is not gate-wired in this
repo.** AGENTS.md:200 offers it as "the check", but the only automated
`#guard_msgs` axiom gates live in `../lean-basen/Axioms.lean` (which AGENTS.md
itself says at line 178 and 201). Nothing in `lean-codec` asserts
`#print axioms Codec.roundtrip`. AGENTS.md does not say the in-repo form of the
check is manual.

(c) **The bullet only covers one side of Layer 2.** It presents `#print axioms`
as _the_ axiom check while AGENTS.md:210–215 (correctly) says Layer 2 is excluded
from that gate — so within the same section the reader is told "the check" is
`#print axioms` and, four bullets later, that `#print axioms` proves nothing about
the seam. Not false, but the ordering invites citing (b) as assurance about (c).

**EVIDENCE:**

```
$ grep -rn 'sorry' Codec/ Codec.lean Bench.lean | grep -v 'zero `sorry`' | wc -l
       0
$ grep -rn '^\s*sorry\|:= sorry\|by sorry\|admit' Codec/ Codec.lean | wc -l
       0
```

(So the _claim is true today_ — that is not the finding. The finding is that the
stated enforcement does not exist.) Supporting:

```
$ grep -n 'lake build\|lack of' default.nix | sed -n '1,6p'
59:      lake build ${targets}          # empty for `check` → plain `lake build`
96:  check = mkLakeBuild {           # install = mkdir -p "$out" only
```

**SUGGESTED FIX:** Either (i) make the gate real — add a `buildPhase` step
`! grep -rn --include='*.lean' -E '(^|[^A-Za-z0-9_])sorry([^A-Za-z0-9_]|$)' Codec Codec.lean`
(or `lake build -DwarningAsError=true`, which turns the `declaration uses 'sorry'`
warning into a build failure) to `default.nix`'s `check`; or (ii) stop calling it a
gate and write the honest sentence: _"`lake build` does not fail on `sorry`; the
zero-`sorry` claim is verified manually by `grep`/`-DwarningAsError` and by
`../lean-basen`'s `Axioms.lean`. Re-verify after any proof edit."_ Also add the
in-repo axiom sample verbatim (`printf 'import Codec\n#print axioms Codec.roundtrip\n'`),
since the example currently printed under _"how to build **this** repo"_ is a
`BaseN` command.

---

## 3. SEVERITY: MEDIUM — the `Classical.choice` trap section is still incomplete; the `decide_eq_true (by omega)`-on-a-disjunction leak is **reproduced**, and the `match`-in-goal leak is recorded in a bullet three sections away

**LOCATION:** AGENTS.md:240–249 (the "_`Classical.choice` trap._" bullet). The
missing facts exist at AGENTS.md:143–146, buried inside the `../lean-basen`
7.3 history block.

**WHAT IS WRONG:** The ergonomics bullet documents exactly **one** leak shape
(dependent `cases`/`match` on a list whose length _equation_ is in context) and
one mitigation (restate numerically / derive the index). Two further leak shapes
were found this session and are recorded only as a parenthetical in the
change-history prose:

1. `decide_eq_true (by omega)` on a **disjunction** goal leaks `Classical.choice`
   because `omega` case-splits. Fix: build the disjunct explicitly.
2. A `match` on a `Bool` **in the goal** leaks. Fix: split into `_true`/`_false`
   lemmas.

An agent following the ergonomics section will hit (1) and re-bisect from scratch,
because the section it would consult does not contain it — and `omega` is
_already_ a topic of the very next bullet ("`omega` does not reason modulo"), so
the reader is actively pointed at `omega` without the caveat.

**EVIDENCE:** (i) verified by compiling, per instruction #7:

```
$ cat /tmp/probe.lean
theorem t (n : Nat) (h : 65 ≤ n ∧ n ≤ 70) :
    decide ((48 ≤ n ∧ n ≤ 57) ∨ (65 ≤ n ∧ n ≤ 70)) = true :=
  decide_eq_true (by omega)
#print axioms t

$ cd /Users/user/_/lean-codec && nix develop --command lake env lean /tmp/probe.lean
't' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The theorem is trivial arithmetic; the only source of `Classical.choice` is the
case-split inside `omega`. Confirms shape (1) exactly as described.

(ii) shape (2) is asserted at AGENTS.md:143–146
(`A `match`on a`Bool`**in the goal** leaks too — split into`_true`/`_false` lemmas.`)
but is not stated in, nor cross-referenced from, "Lean proof ergonomics".

**SUGGESTED FIX:** Extend the trap bullet to a three-part list, in the ergonomics
section, with the probe above as the reproducible MWE:

```markdown
- **`Classical.choice` trap (three shapes, all re-verified):**
  1. dependent `cases`/`match` on a list with a length _equation_ in context;
  2. `decide_eq_true (by omega)` on a **disjunction** — `omega` case-splits;
     build the disjunct explicitly instead (`/tmp/probe.lean` MWE: `[propext,
Classical.choice, Quot.sound]`);
  3. a `match` on a `Bool` **in the goal** — split into `_true`/`_false` lemmas.
```

and delete the duplicate at AGENTS.md:143–146 (or replace it with a pointer),
since a fact kept in two places is the session-diary failure this file's header
forbids.

---

## 4. SEVERITY: MEDIUM — the verification recipe says "In `../lean-basen`" and then lists `openspec validate` "from `../lean-codec`" (and a `BaseN` axiom probe), i.e. commands attributed to the wrong repo inside a section labelled for one repo

**LOCATION:** AGENTS.md:167–195 (heading _"## Verification recipe"_, lead-in
_"The proof gate is the build. In `../lean-basen`, from **its own** `nix develop`"_),
specifically AGENTS.md:190 (`openspec validate --all` **from** `../lean-codec`),
191–192 (`nix flake check`), 193–195 (`#print axioms BaseN.Base64…`).

**WHAT IS WRONG:** The section opens by scoping itself to `../lean-basen`, then
mixes in: (a) an `openspec` command that must run in **this** repo; (b) an
unqualified `nix flake check` that is ambiguous between the two flakes (they are
different flakes with different `checks` sets — `lean-codec` has
`formatting|lean|openspec`, `../lean-basen` does not); and (c) a `BaseN` example
presented as how to "check one law by hand". Every command is _correct in its home
repo_, but nothing labels which repo each belongs to, and the section's own
lead-in sentence tells the reader the opposite for three of them. This is exactly
the misattribution class instruction #6 asks about — the commands are right, the
**attribution is wrong**. Result: running the section top-to-bottom from
`../lean-basen` yields a failing `openspec validate --all` (no `openspec/` root
comparable) and a `nix flake check` on the wrong flake.

**EVIDENCE:** Section text as written (AGENTS.md:169, 190–195). Confirmed the two
flakes' check sets differ and that this repo has the `openspec/` root that the
`openspec validate` line needs:

```
$ openspec list --json | tail -4      (run in /Users/user/_/lean-codec)
  "root": {"path": "/Users/user/_/lean-codec", "source": "nearest"}
$ nix eval --json '.#checks.aarch64-darwin' --apply builtins.attrNames  → ["formatting","lean","openspec"]
$ ls ../lean-basen/openspec           → exists, but is a *different* change set (lean-basen/…)
$ ls ../lean-basen/Axioms.lean        → exists  (so the Axioms.lean claims at 174–178 are right, in the right repo)
```

**SUGGESTED FIX:** Split the section in two explicit subsections:

```markdown
## Verification recipe

### In this repo (`lean-codec`)

nix develop --command lake build # proof gate
nix develop --command openspec validate --all # after any spec-delta edit
nix develop --command lake build bench # bench lane (C seam)
nix build '.#checks.aarch64-darwin.lean' # = the same lake build, sandboxed
bash -c "! grep -rn --include='*.lean' -E '(^|[^A-Za-z0-9_])sorry' Codec Codec.lean" # see finding 2
nix build '.#checks.aarch64-darwin.formatting' # treefmt
nix flake check # long — nohup … &, then poll

### In `../lean-basen` (its own `nix develop`, its own `openspec/`)

nix develop --command lake build # library + Axioms.lean (#guard_msgs gates)
nix develop --command lake build bench # NOTE: `bench` is NOT a flake target there (task 5.3)
```

and say explicitly that `nix flake check` is a **per-repo** command, never "run
it once for the ecosystem".

---

## 5. SEVERITY: MEDIUM — `nix build '.#bench'` is used twice as doctrine for _this_ repo, where it is at best redundant and, per the file's own rules, must never be run in the foreground anyway

**LOCATION:** AGENTS.md:63 (inside "Toolchain / environment: read first"), 71–73
("never run a long `nix build` (toolchain, bench, or proof gate) in the
foreground"), 76, 88–89, 303 (`nix build .#bench` as the reason `stdenv.cc` is in
the dev shell).

**WHAT IS WRONG:** `nix build .#bench` **is** legitimate here (unlike in
`../lean-basen`, see finding 6) — `flake.nix:58` defines `packages.bench` and
`nix eval .#packages.aarch64-darwin.bench.name` resolves to `codec-bench-0.1.0`.
But AGENTS.md both (a) uses it as the headline example of a command to run after
`nix develop` (line 63, in a bullet about _entering the shell_) while (b)
forbidding it in the foreground three lines later (line 71). The reader is told to
run it in the same paragraph that forbids the way they would naturally run it.
Also: `nix develop` already provides `pkgs.stdenv.cc`, so the _reason_ cited at
lines 88–89 ("so `lake build bench` links, matching the `nix build .#bench`
sandbox") is fine — but the file never says the dev-loop command is
`lake build bench` (which is what actually exercises the seam fast), only the slow
Nix one. Additionally, the `bench` target links `byteSliceO` from
`Codec/ByteSlice.c`; AGENTS.md mentions at line 305–307 that an untracked `.c`
breaks `nix build .#bench`, which is the genuinely useful fact and is buried at
the bottom in "Git conventions".

**EVIDENCE:**

```
$ grep -n 'bench' flake.nix default.nix lakefile.lean
flake.nix:58:       packages.bench = _pkg.bench;
default.nix:111:    bench = mkLakeBuild { name = "bench"; targets = "bench"; mainProgram = "bench"; … }
lakefile.lean:22:lean_exe bench where
$ nix eval --raw '.#packages.aarch64-darwin.bench.name'
codec-bench-0.1.0
```

**SUGGESTED FIX:** In the Toolchain section, replace the parenthetical example
`nix build '.#bench'` with the dev-loop command `lake build bench` and add:
_"`nix build .#bench` exists (`flake.nix:58`) as the sandboxed/CI equivalent; it
is a long build — always `nohup`, never foreground."_ Keep line 305's
untracked-`.c` warning but **cross-reference it from there**.

---

## 6. SEVERITY: MEDIUM — the `../lean-basen` bench command is presented as part of the verification recipe but is a known-broken target there (open task 5.3), and AGENTS.md never says so

**LOCATION:** AGENTS.md:175 (`nix develop --command lake build bench   # the bench lane`,
in the `../lean-basen` subsection) vs. AGENTS.md:151–153 (which sends the reader
to `openspec/changes/lean-basen/tasks.md` "Still open" without naming which items
touch commands).

**WHAT IS WRONG:** The `../lean-basen` subsection of the verification recipe tells
the reader to run `lake build bench` — but in `../lean-basen` the `bench` lane is a
_known-opened_ polish item (`5.3 **\`bench\` executable not wired as a
flake/default.nix target.** … \`nix build .#bench\` fails`). AGENTS.md lists 5.3 in
the seven-item set but does not flag that it is a **verification-recipe**
regression: a reader doing "run the recipe" hits a red lane with no hint that it is
expected. (Whether `lake build bench`or only`nix build .#bench` fails there is
asserted by task 5.3, not stated by AGENTS.md either way — so the recipe line is
ambiguous _and_ known-fragile.)

**EVIDENCE:**

```
$ sed -n '121,124p' openspec/changes/lean-basen/tasks.md   (in /Users/user/_/lean-codec)
- [ ] 5.3 **`bench` executable not wired as a flake/default.nix target.**
      `lakefile.lean` declares `lean_exe bench`, but `flake.nix` has no
      `packages.bench` and `default.nix` has no `bench` target (`nix build .#bench`
      fails). Add it or document as dev-loop-only.
$ grep -n 'packages.bench' ../lean-basen/flake.nix    → (no match)
```

**SUGGESTED FIX:** Annotate the recipe line:
`# dev-loop only in ../lean-basen: there is no packages.bench (task 5.3); use \`lake build bench\`, never \`nix build .#bench\`.`and add to the 18/25 bullet: *"of the seven, 5.3 is a **verification-recipe** item
(the`bench` lane), not a docs nit — do it first if you need the bench."*

---

## 7. SEVERITY: MEDIUM — the missing rail: a stale `../lean-basen/flake.lock` `codec` rev is recorded nowhere, so the `bad import Codec.Normal` failure mode can silently recur

**LOCATION:** AGENTS.md:121–125 (_"It consumes `codec` **by git input**, so a core
change is only visible there after pushing `lean-codec` and running
`lake update codec` in `../lean-basen`."_) — and nowhere else in the doc set.

**WHAT IS WRONG:** The instruction names the remedy (`lake update codec`) but never
names the **symptom** and never points at the lockfile. The observed failure was
`bad import Codec.Normal` from the _sandboxed_ build (where `default.nix` rewrites
`require codec from git` to `./codec-src`, sourced from the flake input → the
locked rev). An agent that sees `bad import` will read it as "the module was
deleted / I mistyped the import" and go edit `BaseN/Common.lean`, which is exactly
wrong: the Lean source is fine, the _lockfile_ predates `Codec/Normal.lean`. Only
`flake.lock`'s `nodes.codec.locked.rev` reveals it, and no file says to look there.
The `../lean-basen` polish task 5.12 ("`lake-manifest.json` (gitignored) vs
`flake.lock` rev note — one-line AGENTS.md note") is the item that _would_ have
recorded it, is still unticked, and is described in `tasks.md` as a one-line note
with no statement of consequences.

**EVIDENCE:**

```
$ grep -rn 'bad import\|lake update' /Users/user/_/lean-codec/AGENTS.md \
      /Users/user/_/lean-codec/README.md /Users/user/_/lean-codec/CHANGELOG.md \
      /Users/user/_/lean-basen/AGENTS.md /Users/user/_/lean-basen/README.md \
      /Users/user/_/lean-basen/REVIEW-basen-rfc-conformance.md
/Users/user/_/lean-codec/AGENTS.md:123:pushing `lean-codec` and running `lake update codec` in `../lean-basen`. Its
# (that is the ONLY hit — no 'bad import' anywhere; symptom unrecorded)
$ grep -n 'flake.lock' /Users/user/_/lean-codec/AGENTS.md
296:  `flake.lock` **is** tracked, for reproducibility.        # repo hygiene only
$ grep -n '"rev"' ../lean-basen/flake.lock | head -1
        "rev": "dbab7d70f479e41a8f15192beab5dcf050a4ea66",   # the codec pin
```

(`dbab7d7` _does_ already contain `Codec/Normal.lean`, so the current pin is fresh —
the rail is missing for the _next_ time it drifts, not broken now. That makes it a
latent trap, not a current failure.)

**SUGGESTED FIX:** Extend the `../lean-basen` bullet with the symptom→cause→fix
triple:

```markdown
**Rail — `bad import Codec.Normal` in `../lean-basen`** means the flake's `codec`
pin is older than the module, _not_ a bad import: check
`../lean-basen/flake.lock` → `nodes.codec.locked.rev` against
`git log --oneline -1 -- Codec/Normal.lean` in this repo, then
`cd ../lean-basen && nix flake update codec && lake update codec`.
Never "fix" it by editing the importing Lean file. (Do not use
`nix flake update` on all inputs; that is a different, wider change.)
```

---

## 8. SEVERITY: LOW — the header's "Keep it short and true" is violated in spirit by a 55-line `Current state` block that restates change-internal results, and by duplicated facts

**LOCATION:** AGENTS.md:5–19 (the header rule + the long "Current state" preamble)
vs AGENTS.md:94–164 (the ~70-line `Current state` block including the 7.1/7.2/7.3
history and two "findings that changed the plan").

**WHAT IS WRONG:** The file's own header forbids "session status" and says history
("what landed when, what a past session measured") belongs in `openspec/` and
`CHANGELOG.md`, and that `Current state` should state "what is true now and what is
next". The block as written is _not_ self-contradictory (checked in full — see the
verification note at the end) but it does violate the stated intent in two concrete
ways: (i) `7.1, 7.2 (DONE)` / `7.3 (DONE)` with proofs-of-work (`hexBlockApply_foldList_ne`,
`b{64,32}BytesOf_tail1_eq`) is _what landed_, i.e. exactly the material the header
routes to `tasks.md`; (ii) the `Classical.choice`/`match` findings are duplicated
between here (143–146) and "Lean proof ergonomics" (240–249), and the duplication is
already asymmetric (finding 3: the ergonomics copy omits both). The result is the
failure mode the header warns about, in miniature: two places holding the same fact,
one of them incomplete.

**EVIDENCE:** File-internal. `grep -n '5\.1' AGENTS.md` returns one hit (line 116,
`Task 5.1 … is **done**`) — so no stale "5.1 open" survives; `grep -n '15/16\|PAUSED\|START HERE' AGENTS.md`
returns **no hits**. The block is consistent; it is the size and the duplication
that breach the stated rule.

**SUGGESTED FIX:** Cut `Current state` to ~12 lines: three bullets (codec core
complete 16/16+31/31; `../lean-basen` 18/25 with 5.3 and 5.12 called out as
recipe-relevant; archive order). Move 7.1/7.2/7.3 and the two plan-changing
findings into the change's `tasks.md` (they are already partly there — grep shows
7.3 at `tasks.md:104`), and leave in `AGENTS.md` only the _forward-looking_
distillate (the three `Classical.choice` shapes, now in the ergonomics section per
finding 3).

---

## 9. SEVERITY: LOW — no grep of my own "verify these are not stale" claims exists in the file; the file tells you to distrust itself but gives no command to do so

**LOCATION:** AGENTS.md:92–93 (_"Run `openspec list --json` for the live answer; do
not trust a snapshot here for longer than the commit that wrote it."_).

**WHAT IS WRONG:** Good instinct, but only half-applied. The counts (`16/16`,
`31/31`, `18/25`) are all derivable from one command, and the file says to run it —
fine. But two other checkable assertions in the same block are never given a
command: the "seven mechanical polish items" list (5.2/5.3/5.4/5.8/5.9/5.12/5.13)
and the archive-order claim ("either order is now _safe_", task 6.11). This session
I verified both by hand (`grep -c '^\- \[ \]' tasks.md` → 7, matching the list
exactly); the next session will not know to. Given that the two "changes" this file
worries about most (stale counts, stale MODIFIED blocks) are both machine-checkable
and one is already covered by `checks.openspec` (`openspec validate --all`), the
gap is just a missing pointer.

**EVIDENCE:**

```
$ grep -c '^\- \[ \]' openspec/changes/lean-basen/tasks.md   → 7
$ sed -n '114,133p' openspec/changes/lean-basen/tasks.md | grep -o '5\.[0-9]*' | sort -u
5.2 5.3 5.4 5.8 5.9 5.12 5.13        # matches AGENTS.md:152 exactly ✓
$ nix develop --command openspec validate --all --no-interactive → Totals: 8 passed, 0 failed  ✓
```

**SUGGESTED FIX:** One line under the `Current state` lead-in:
`# the machine-checkable half of this block:
nix develop --command openspec list --json && nix develop --command openspec validate --all --no-interactive

# and: grep -c '^\- \[ \]' openspec/changes/<name>/tasks.md # must equal the "seven" above`

---

## 10. SEVERITY: LOW — the `bench` "extraction" narrative conflicts with what the `bench` target actually is, and the doc never states the `bench` exe's root

**LOCATION:** AGENTS.md:99 (`` `lean_exe bench` is the benchmark ``), AGENTS.md:141
(`` `../lean-basen` shows 18/25``), AGENTS.md:178 / `default.nix:108–111`
("`bench` — the §10.5 **extraction** + benchmark executable"). Cross-doc:
CHANGELOG.md:59–61 calls it an "extraction" too.

**WHAT IS WRONG:** `lakefile.lean`'s `bench` is a plain `lean_exe` (`root := \`Bench`,
`moreLinkObjs := #[byteSliceO]`) that additionally links the Layer-2 C object. There
is no §10.5 *extraction* step in the lakefile (no `extract`target, no generated C
tree) — the "extraction" language describes an aspiration inherited from an older
plan, and`default.nix` repeats it in a comment. AGENTS.md itself, at line 240,
says **"All codecs are pure Lean"** and at line 222 that C is _only_ generic bulk
byte movement — which is consistent with a linked object file and inconsistent with
"extraction". An agent reading "extraction … §10.5" will look for an extraction
config that does not exist.

**EVIDENCE:**

```
$ cat lakefile.lean | sed -n '20,24p'
lean_exe bench where
  root := `Bench
  moreLinkObjs := #[byteSliceO]
$ grep -rn 'extract' lakefile.lean flake.nix Codec/ Bench.lean | head
(only `ByteArray.extract` mentions in Codec/ByteSlice.lean, unrelated)
```

**SUGGESTED FIX:** Say what it is: *"`lean_exe bench` (`root := \`Bench`) links the
Layer-2 C object (`Codec/ByteSlice.c`→`byteSliceO`) into the benchmark; it is a
plain executable, **not** a C-extraction step. §10.5 extraction is not implemented;
do not go looking for it."* Fix the same wording in `default.nix`'s comment.

---

## 11. SEVERITY: LOW — "Bisect by shrinking the body to `⟨_, rfl⟩`" is stated without the precondition that makes it sound

**LOCATION:** AGENTS.md:248 (last sentence of the `Classical.choice` trap bullet).

**WHAT IS WRONG:** The advice ("if it still leaks, it is the match, not the
arithmetic") is _only_ sound if the stubbed body's type is inhabited by
`⟨_, rfl⟩` — i.e. the goal is a bare `∃`/sigma. Applied to the `decide (…) = true`
shape now known to leak (finding 3), `⟨_, rfl⟩` does not typecheck at all, so the
prescribed bisection does not run; and applied to a `match`-in-goal leak, the goal
has no sigma to fill. The heuristic is fine for the one shape it was learned on but
is written as general.

**EVIDENCE:** Trivially checkable: on `/tmp/probe.lean`'s goal
`decide (…) = true`, `⟨_, rfl⟩` is a type error (`decide … = true` is not a sigma).

```
$ printf '...:= ⟨_, rfl⟩' >> /tmp/probe2.lean → application type mismatch
```

(Also implied by finding 3's own reproduction, where the leak comes from `omega`,
not a `match`.)

**SUGGESTED FIX:** Qualify it: _"**When the goal is a sigma/`∃`**, bisect by
shrinking the body to `⟨_, rfl⟩`; for a `decide … = true` goal use
`decide_eq_true (by decide)` or supply the disjunct, and for the three shapes above
prefer rewriting the proof shape over bisecting."_

---

## 12. SEVERITY: INFO — small precision gaps in the `Current state` counts that are technically true but easy to misread

**LOCATION:** AGENTS.md:100–102, 118, 151.

**WHAT IS WRONG:**

- _"**No open change in this repo.**"_ followed immediately by _"`lean-basen` is
  18/25"_ and _"`lean-basen` is `in-progress`"_ — `osc list --json` reports **three**
  changes with `root.path = /Users/user/_/lean-codec`, one of them
  `"status": "in-progress"`. "No open change in this repo" is true only under the
  reading "no open change _of this repo's own scope_" (the `lean-basen` change is a
  proxy ledger for `../lean-basen`). A reader who runs `openspec list` and sees
  `in-progress` will believe the doc is wrong.
- _"`codec-normal-form-case-quotient` is 16/16 **and ready to archive**"_ and 31/31
  likewise — but `openspec validate --all` is green with both unarchived, and both
  have been "ready to archive" across ≥3 commits (`d158da5`, `12249d5`, `af6532b`).
  "Ready to archive" with no owner/next-action reads as an unfinished handoff.

**EVIDENCE:**

```
$ nix develop --command openspec list --json | grep -E '"name"|"status"'
"name": "codec-normal-form-case-quotient", … "status": "complete"
"name": "basen-rfc-conformance-theorems",  … "status": "complete"
"name": "lean-basen",                     … "status": "in-progress"
$ nix develop --command openspec validate --all --no-interactive → 8 passed, 0 failed
$ git log --oneline | head -4   # af6532b is itself "AGENTS: Current state — all three changes complete"
```

**SUGGESTED FIX:** Reword to _"**No change scoped to this repo is still in
progress.** Three changes are visible from this root: two complete-and-unarchived
here (`codec-normal-form-case-quotient` 16/16, `basen-rfc-conformance-theorems`
31/31 — archive in the order below) and `lean-basen` 18/25, which is the proxy
ledger for `../lean-basen`."_ And give the archive step an owner/trigger, or drop
the repeated "ready to archive" from the summary and keep it only in the archive
paragraph.

---

## Explicitly checked and found CLEAN (so the reader knows these were not skipped)

| Instruction                                                         | Result                                                                                                                                                                                                                                                                                                                                       |
| ------------------------------------------------------------------- | -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| #1 counts 16/16 / 31/31 / 18/25                                     | **Correct**, all three, per `openspec list --json`.                                                                                                                                                                                                                                                                                          |
| #2 stale `15/16` / `PAUSED` / `START HERE` / "5.1 open" / "blocked" | **None present.** `grep -n '15/16\|PAUSED\|START HERE\|blocked' AGENTS.md` → no hits; `grep -n '5\.1' AGENTS.md` → only line 116, "Task 5.1 … is **done**". The edit left the block **self-consistent**; the only 5.1 references left are in `openspec/changes/lean-basen/tasks.md:83` (a _different_ change's 5.1, correctly ticked `[x]`). |
| #4 self-violation: no appended session-status section               | **Not violated.** Structure is a fixed set of `##` sections; `Current state` was rewritten in place (`af6532b`), and no `HANDOFF/NOTES/STATUS` file exists in the repo root (`ls` shows none). The _spirit_ breach is finding 8, not a structural one.                                                                                       |
| #5 `sorry` in the tree                                              | **Zero** real `sorry`s; the 3 grep hits are prose ("zero `sorry`") in docstrings. The `second` half of #5 — that the gate does not enforce it — is finding 2.                                                                                                                                                                                |
| #6 `nix build '.#bench'` valid here                                 | **Yes** — `flake.nix:58 packages.bench`; `nix eval .#packages.aarch64-darwin.bench.name` → `codec-bench-0.1.0`.                                                                                                                                                                                                                              |
| #6 `nix build '.#checks.aarch64-darwin.lean'`                       | **Valid** — resolves to `codec-check-0.1.0`. (AGENTS.md never actually writes this path; it writes `checks.lean` descriptively. Not a defect, just noted.)                                                                                                                                                                                   |
| #6 `lake build bench` exe name                                      | **Correct** — `lakefile.lean:22 lean_exe bench`.                                                                                                                                                                                                                                                                                             |
| README ↔ AGENTS.md on proved-vs-trusted                             | **Consistent.** AGENTS.md's two-layer bullet (210–221) matches README's "two proof layers" section (≈469–495), including the "`#print axioms` reporting no axioms says nothing about the C" caveat and the `[propext, Quot.sound]`-only Layer-1 claim. The only cross-doc contradiction found is `Bytes` (finding 1).                        |
| `../lean-basen` pin vs `Codec/Normal.lean`                          | **Consistent today** — `flake.lock` pins `dbab7d7`, which already contains `Codec/Normal.lean`; the missing rail is a latent issue (finding 7), not a live one.                                                                                                                                                                              |

---

## Tally

| Severity  | Count  | Findings                                                                                                                                                                                                                                |
| --------- | ------ | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| HIGH      | 2      | 1 (`Bytes` contradiction), 2 (unenforced zero-`sorry` gate)                                                                                                                                                                             |
| MEDIUM    | 5      | 3 (`Classical.choice` trap incomplete — reproduced), 4 (recipe misattributes repos), 5 (`nix build .#bench` foreground/doctrine clash), 6 (`../lean-basen` bench lane is a known-broken target), 7 (missing `bad import`/lockfile rail) |
| LOW       | 4      | 8 (header rule breached by block size + duplication), 9 (no self-check command), 10 (`bench` "extraction" misnomer), 11 (`⟨_, rfl⟩` bisection precondition)                                                                             |
| INFO      | 1      | 12 ("no open change" wording / repeated "ready to archive")                                                                                                                                                                             |
| **Total** | **12** |                                                                                                                                                                                                                                         |

No repository files were modified; the only writes were `/tmp/probe.lean` and this
review file.

---

# Adversarial review — `/Users/user/.pi/agent/skills/lean/SKILL.md` (2233 lines)

Reviewer: worker agent. Method: every claim below that starts **EVIDENCE** was compiled
against `lean-codec`'s `nix develop` (Lean 4.34.1) with `/tmp/x*.lean` probes. Nothing in
the skill file was modified.

Verification command used throughout:

```
cd /Users/user/_/lean-codec && nix develop --command sh -c 'lake env lean /tmp/xN.lean; echo RC=$?'
```

(Note for the next reviewer: `nix develop --command lake env lean <file>` returns **exit 0
even when the file fails**; you must wrap in `sh -c 'lake env lean …; echo RC=$?'` or you
will silently conclude every probe passed. This bit me on the very first probe.)

Severity key: **CRITICAL** = wrong fact that will send a future session down a false path;
**HIGH** = wrong or unimplementable guidance, or the skill breaks its own stated contract;
**MEDIUM** = misleading / stale / costly; **LOW** = hygiene, navigability, ordering.

---

## 1. HIGH — missing the exact lesson AGENTS.md says is the whole reason this file exists

**LOCATION** line 511 (2026-10-25 `omega`'s-disjunction entry) — and its absence everywhere else.

**WHAT IS WRONG** The project's `AGENTS.md` records this trap as a finding "both verified —
do not rediscover them": _"`decide_eq_true (by omega)` on a **disjunction** leaks
`Classical.choice` (`omega` case-splits) — build the disjunct explicitly."_ The skill file
records only the **narrower** `omega`-proves-`k = 0 ∨ … ∨ k = n-1` statement (line 511). It
never records the far more common composition trap — `decide_eq_true` taking an `omega` proof
of a _disjunction_ — which is a different leak site (the `Decidable (A ∨ B)` instance plus the
omega case-split) and is the one that actually bites in a `decide (…) = true` goal. So the file
is missing exactly the high-value lesson the repo's own instructions flag for it.

**EVIDENCE**

```lean
theorem ta (n : Nat) (h : 65 ≤ n ∧ n ≤ 70) :
    decide ((48 ≤ n ∧ n ≤ 57) ∨ (65 ≤ n ∧ n ≤ 70)) = true :=
  decide_eq_true (by omega)
#print axioms ta
```

```
'ta' depends on axioms: [propext, Classical.choice, Quot.sound]
```

and the whole divergence is one tactic:

| spelling                              | result                                    |
| ------------------------------------- | ----------------------------------------- |
| `decide_eq_true (Or.inr h)`           | `[]`                                      |
| `(… ∨ …) := by omega` (Prop directly) | `[propext, Classical.choice, Quot.sound]` |
| `decide_eq_true (by omega)`           | `[propext, Classical.choice, Quot.sound]` |

**SUGGESTED FIX** Add an Append entry stating the general rule with the `ta` snippet as the
canonical probe: in a `Classical.choice`-gated law, _never_ hand `omega` (or `by_contra`,
or `decide_eq_true`) a **disjunctive** goal — build the disjunct with `Or.inl`/`Or.inr` and
let `omega` only close the conjunction/arithmetic leaf. Cross-reference line 511.

---

## 2. HIGH — the "delta" file is ~80% project-specific; the file's own contract is violated

**LOCATION** header (lines 15–19: _"Keep it generic (no project names/paths); the specific repo
lives elsewhere"_, repeated at line 485), vs. lines 38–58, 175, 215–218, 227–229, 322–343, 358,
361, 393–397, 421–423, 498–528, 584–854, 897–1005, 1096–1189, 1305–1319, 1388–1438, 1457–1481,
1510–1516, 1571–1600, 1640–1670, 1735–1933, 1959–1960, 2020–2078, 2135, 2205–2211.

**WHAT IS WRONG** Rule 2 of this repo's instructions to me — "project-specific content violating
the _keep it generic_ rule" — is not violated once or twice; it is violated ~130 times. The
skill's own header promises "no project names/paths", and the Append header repeats it, yet:

| pattern                                                             | hits                                                                                                                            |
| ------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------- |
| `Codec` (the project's central type)                                | 104 (e.g. 56–58, 215–218, 322–334, 341–343, 679, 897–902, 1096–1107, 1160–1189, 2020, 2078)                                     |
| `Bytes n := Fin n → UInt8`                                          | 25 (498, 528, 624, 691–705, 780–782, 936, 1160, 1571, 1640, 1669, 1785, 1824–1933, 2135)                                        |
| `relRepeat` / `decodeRepeat` / `encodeRepeat` / `Suffix.` / `bdrop` | 100+ (332, 490, 498, 505, 561–567, 584–611, 625–635, 686–752, 1028–1052, 1268–1284, 1457–1481, 1663–1665, 1752–1766, 1788–1838) |
| `byteSlice` / `blitBytes`                                           | 1388, 1390–1391, 1407, 1410, 1426, 1437–1438, 1959–1960                                                                         |
| `Iso.law`                                                           | 233, 796, 978, 985                                                                                                              |
| `decodeNormal`                                                      | 2205, 2208                                                                                                                      |
| `basen` / `BaseN` / `hexBlock`                                      | **0** (clean)                                                                                                                   |

**EVIDENCE** `grep -n -i -- 'codec' SKILL.md | wc -l` → 104; `grep -n 'Bytes n' … | wc -l` → 25.

This is also the file's dominant _mechanism_ problem (finding 3): the project specifics are
not decoration, they are the load-bearing part of ~40 entries, so a future agent working on a
different Lean project cannot use them at all.

**SUGGESTED FIX** Two files, not one: keep §1–§7 (generic, ~480 lines) in `SKILL.md`; move
the whole "Append new learnings" body (lines 482–1624) into a project-local
`AGENTS.md`/`NOTES-codec.md` in the `lean-codec` repo, and have the skill point at it with
one line ("the `codec` repo keeps its domain-specific proof notes in its own AGENTS.md").
While doing it, hoist the ~10 genuinely generic facts it contains (findings 1, 4, 8, 12, 15,
16, 20, 22) back into the generic half.

---

## 3. HIGH — duplication / conflict with the official `lean4` skill's quality gate

**LOCATION** lines 17–20 (_"Where they disagree, the official skill's proof-engineering
guidance wins"_), vs. the skill's repeated axiom gate (`[propext, Quot.sound]`-only, zero
`Classical.choice`) and `by_contra`/`decide`/`omega` warnings (509–511, 520, 530–538, 1081–1085).

**WHAT IS WRONG** The official skill (`…/lean4-skills/plugins/lean4/skills/lean4/SKILL.md`,
"Quality Gate", line ~317) defines a complete proof as **"Only standard axioms (`propext`,
`Classical.choice`, `Quot.sound`)"**. This skill's _entire_ first-class concern is eliminating
`Classical.choice` — 37 mentions. The skill says the official file wins on proof engineering,
and by that rule every axiom-hygiene instruction here is advisory and overridable. That is a
silent, self-defeating contradiction at the top of the file.

Other duplication: the official file already owns "stage only touched files / never `git add
-A`" (File Handling Rules) — this skill's 2026-10-26 entry (line 487) spends 6 lines on the same
`git` hygiene, plus a "commit per law-family" habit; the official file owns the scratch-work
ladder and the `lake env lean` → `lake build` verification ladder, which this skill repeats in
several entries.

**EVIDENCE** official `SKILL.md`: `grep -n 'Classical.choice'` → only inside the Quality Gate
line (permitted axioms); this skill: 37 hits, all saying it is forbidden.

**SUGGESTED FIX** Amend the header preamble explicitly: _"this project's gate is stricter than
the official `lean4` Quality Gate — `Classical.choice` is **not** permitted here; on any
conflict, this file's axiom discipline wins, the official file wins on everything else."_ Drop
the duplicated `git`-staging paragraph and link to the official File Handling Rules.

---

## 4. MEDIUM — the Bool-`match`-in-the-goal claim is recorded in the wrong place, with the wrong fix

**LOCATION** line 1754 (2026-10-24 `decodeFull_…_of_encode` entry): _"a result `= (match tail
with …)` generalizes the `match` over the in-scope hypotheses that mention `tail` (its proof did
`cases tail`), so `rw [htailc : tail = b::rest]`…"_, and line 517 (literal-target `match`).

**WHAT IS WRONG** The `AGENTS.md` finding is: _"A `match` on a `Bool` **in the goal** leaks too —
split into `_true`/`_false` lemmas."_ The skill records the _list_-matched variant and the
_simp-doesn't-reduce_ variant, but there is no generic, findable entry for the Bool case and it
prescribes no fix. Meanwhile the actual failure mode of a Bool `match`/`if` in the goal is not a
`Classical.choice` leak at all (my probes could not produce one) — it is a **dependent-match /
`Decidable`-did-not-reduce** failure. And the skill's other advice for `if` goals, line 1183
(_"don't unfold a dependent `match` on `b` under `simp`; instead `subst` it so the goal becomes
head-normal"_), **fails** on exactly the Bool-in-goal shape it is offered for.

**EVIDENCE**

```lean
-- the recom  mended `subst` route fails:
theorem tl (b : Bool) (h : b = true) :
    (match b with | true => (1:Nat) = 1 | false => (0:Nat) = 0) = True := by
  subst h; rfl
```

```
error: Tactic `rfl` failed: The left-hand side
  match true, ⋯ with | true, h => 1 = 1 | false, h => 0 = 0
is not definitionally equal to the right-hand side  True
```

Only `cases b <;> simp_all` closes it:

```
'tk' depends on axioms: [propext]     -- cases b <;> simp_all
```

and a Bool `match` whose body genuinely needs the equation:

```lean
theorem td (b : Bool) (h : b = true) : (match b with | true => True | false => True) := by
  cases b with …
```

```
error: Dependent elimination failed: Type mismatch when solving this alternative:
  motive (true = true) but is expected to have type  motive x✝
```

**SUGGESTED FIX** One generic entry (in §2, not buried at line 1754): _"a `match`/`if` on a
`Bool` in the *goal* with `h : b = true` in context is a dependent match: `cases b` fails with
'Dependent elimination failed' and `subst h; rfl` fails with 'not definitionally equal to
`match true, ⋯`'. Write `cases b <;> simp_all` (or restate so the match is not dependent — move
the discriminee into a hypothesis), and prefer `if h : p then` to keep the fact in the branch."_

---

## 5. MEDIUM — st ale version pin: the whole §2 premise is qualified to a Lean the project does not use

**LOCATION** lines 84–90 (`**ByteArray` operations do not reduce.** In Lean ≤ 4.30, …` so (a ++ b) ++ c = a ++ (b ++ c)` is _not_ provable mechanically`).

**WHAT IS WRONG** The project builds on **Lean 4.34.1** (`AGENTS.md`), and the qualifier
"In Lean ≤ 4.30" makes the paragraph inapplicable to the toolchain in use — while its
conclusion ("not provable mechanically") is now simply false: `ByteArray.append_assoc` exists
in 4.32+. The rest of the skill (e.g. line 1935) does refer to 4.34, so the file is internally
inconsistent about which version it is describing.

**EVIDENCE**

```
@ByteArray.append_assoc : ∀ {a b c : ByteArray}, a ++ b ++ c = a ++ (b ++ c)
```

```
example (a b c : ByteArray) : (a ++ b) ++ c = a ++ (b ++ c) := ByteArray.append_assoc ..
```

→ `RC=0`.

Also stale/lucky: `(a.push b).data = a.data.push b` is `rfl` (verified `RC=0`), which
contradicts line 1489's _"`ByteArray.push` … do not unfold"_ — they mean different things but
read as a contradiction.

**SUGGESTED FIX** Retitle to "**Lean ≤ 4.30 only:** …; on 4.32+ use `ByteArray.append_assoc`
and the `ByteArray.data_*` projection lemmas, and note `(a.push b).data = a.data.push b` is
`rfl`." Or delete the entry and keep only the 4.34 statement.

---

## 6. MEDIUM — the `USize`/`UInt64` "boxed arithmetic" claim is stated too strongly

**LOCATION** lines 446–457 (§7 point 2) and lines 1305–1313 (2026-10-18 "boxed scalar ceiling"):
_"`UInt64`/`UInt32` arithmetic is **also** boxed (`instAddUInt64` → `lean_object*`, no `uint64_t`
in the emitted C)"_.

**WHAT IS WRONG** Verified both ways, and the skill has it half wrong. `USize` is unboxed as an
argument (true), `Nat` is always `lean_object*` (true), `USize` in a `Prod`/`Option` re-boxes via
`lean_box_usize` (true) — all confirmed. But `UInt64` arithmetic is **not** boxed when the
function is typed in `UInt64`: the emitted C has a `uint64_t` prototype and
`lean_uint64_add`, which is a `uint64_t` operation. The skill's evidence (`instAddUInt64` →
`lean_object*`) is what you get when the _result is boxed at a boundary_, not what `UInt64`
arithmetic lowers to. Stated as-is, this discourages the one scalar type that does work — a real
cost, since the entry's whole point is "don't chase unboxed scalars".

**EVIDENCE** compiled `def sum64 (n : UInt64) : UInt64 := n + 1`:

```c
LEAN_EXPORT uint64_t l_sum64(uint64_t);
...
uint64_t v___x_3_; v___x_3_ = lean_uint64_add(v_n_1_, v___x_2_);
```

vs. the true claims, same file:

```c
lean_object* l_nd(lean_object*);              -- Nat
v___x_2_ = lean_box_usize(v_x_1_);            -- USize inside Option  (def r1 (x:USize) : Option USize := some x)
uint8_t l_i1(size_t, lean_object*);           -- USize in arg position unboxed
```

**SUGGESTED FIX** Reword: _"`Nat` always boxes; `USize` unboxes **only** in argument position of
a compiled function and re-boxes in `Prod`/`Option`; `UInt64`/`UInt32` **do** lower to
`uint64_t`/`uint32_t` + `lean_uint64_add` (verified on 4.34.1) but re-box whenever the value
crosses a polymorphic/`Option` boundary. The measured lesson stands (a `USize` cursor was
*slower*); the wrong generalisation (`UInt64` is boxed) should be deleted."_

---

## 7. MEDIUM — `split_ifs` guidance is scattered, contradictory in emphasis, and unindexed

**LOCATION** line 1935 (_"`split_ifs` no longer exists in Lean 4.34"_), vs lines 1241–1244 and
1724–1727, which prescribe `by_cases` + `simp only […, ite_true, ite_false]` for the same job.

**WHAT IS WRONG** The "`split_ifs` is gone" fact — which breaks essentially every `if`-heavy
proof recipe copied from mathlib-era code — is buried 1500 lines down inside a 2026-10-18 entry
about "well-founded recursion moves to the type index", with no "When to read what" row leading
there. A reader who hits an `if` goal will find lines 1241 and 1724 first and may never learn the
tactic is missing.

**EVIDENCE**

```
example (P : Prop) [Decidable P] (a b : Nat) (h : P) : (if P then a else b) = a := by split_ifs with hp
```

```
error: unknown tactic        RC=1
```

**SUGGESTED FIX** Promote to a §2 bullet: "**`split_ifs` does not exist on stdlib 4.34** — use
`by_cases`/`cases h :`, `simp only [ite_true]`, or `by_cases` + `omega`", and make lines 1241 and
1724 link to it rather than restate a partial recipe.

---

## 8. MEDIUM — the `if_pos`/`if_neg` deprecation is recorded, but the suggested replacement is stated wrong

**LOCATION** line 1935: _"`if_neg` is deprecated (`ite_eq_right` is the replacement)"_.

**WHAT IS WRONG** Two problems. (a) It names only `if_neg`; `if_pos` is **equally** deprecated
(→ `ite_eq_left`) and that half is missing. (b) `ite_eq_left`/`ite_eq_right` are **not** the
`Iff`s that `simp`/`rw` want; they are `c → (if c then t else e) = t` — functions of a proof
argument, usable as terms (`exact ite_eq_left h`) but **not** as `rw [ite_eq_left]` and not
projectable with `.mpr`. The skill's own suggested `rw [ite_eq_right hn]` shape encourages the
wrong usage.

**EVIDENCE**

```
/tmp/x4.lean:2:86: warning: `if_pos` has been deprecated: Use `ite_eq_left` instead
/tmp/x4.lean:3:88: warning: `if_neg` has been deprecated: Use `ite_eq_right` instead
```

```
@ite_eq_left : ∀ {c : Prop} {h : Decidable c}, c → ∀ {α} {t e : α}, (if c then t else e) = t
@ite_eq_right : ∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α} {t e : α}, (if c then t else e) = e
```

and the `.mpr` habit the file teaches elsewhere does **not** work here:

```
error(lean.invalidField): Invalid field `mpr`: … not possible to project … from an expression
  ite_eq_left of type  ?m.5 → ∀ {α} {t e : α}, (if ?m.5 then t else e) = t
```

**SUGGESTED FIX** State both: "`if_pos`/`if_neg` deprecated on 4.34 → `ite_eq_left h` /
`ite_eq_right h`; these are **applied**, not rewrites and not `Iff`s — write
`exact ite_eq_left h` / `rw [show (if P then a else b) = a from ite_eq_left h]`."

---

## 9. MEDIUM — `-/` inside a doc comment is stated one-sided; half the trap direction is missing

**LOCATION** lines 74–77: _"A `-` immediately before `/` (`-/`) *closes* the `/-!`/`/--` comment
early. Write `left- or right-associative`, never `left-/right-associative`"_.

**WHAT IS WRONG** The claim is true but the framing teaches the wrong avoidance rule. Lean
doc comments are **nestable** (`/-` opens a nested comment inside a block comment), so a stray
_forward_ `/-` is equally fatal — and that is the failure a writer actually hits when trying to
work around the rule the skill gives (e.g. writing `left-/-right` or `-/ -` inside a doc).
Verified: `- /` (space-separated) is fine, `-/` is not, but only the `-/` half is documented.

**EVIDENCE**

```
/-! This is a doc comment about left- or right-associative operators. -/    → RC=0
/-! This is a doc comment about left-/right-associative operators. -/       → error: unexpected identifier; expected command  RC=1
/- block comment before imports -/
import Init                                                                  → RC=0   (the `-!` rule at line 68 is correct)
/-! module doc -/
import Init                                                                  → error: invalid 'import' command …            RC=1
```

So line 68's `/-!`-before-`import` rule is **confirmed correct**; line 74's rule is correct but
incomplete (nesting means `/-` is also unsafe).

**SUGGESTED FIX** Reword to: "block comments **nest**: an unmatched `/-` or a `-/` inside a doc
comment terminates it early or swallows the rest of the file — write `left- or right-associative`
and never `left-/right` or `x/-y`."

---

## 10. MEDIUM — four `Classical.choice`-leak entries sit ~1000 lines apart, one of them out of date order

**LOCATION** lines 493 (dependent `match`/`cases`), 497 (`simp at h`), 509 (`decide`/`omega` over
`Fin`), 511 (`omega` disjunction), 520 (`omega` Nat-subtraction trichotomy), 530 (stdlib
`Nat` `<`-cancellation lemmas), 1627–1633 (restated in the Changelog), 1657–1665 (a second
Changelog restatement of the same family).

**WHAT IS WRONG** The single most expensive lesson family in the file is scattered across seven
locations and three sections, with no index. Worse, it is **out of date order** (line 509 is
`2026-10-24`, line 511 is `2026-10-25`, line 520 is `2026-10-24`) in a section whose header says
"latest first", so a reader scanning the top of the Append gets a timeline that lies. And the
guidance is _individually_ correct but _collectively_ unusable: three different entries say "the
leak is in a generated `_proof_*`", each with a different bisection recipe.

**EVIDENCE** `grep -nE '^- 20' SKILL.md | awk …` →

```
OUT-OF-ORDER at line 511: 2026-10-24 -> 2026-10-25
OUT-OF-ORDER at line 1571: 2026-10-17 -> 2026-10-26
OUT-OF-ORDER at line 2130: 2026-10-10 -> 2026-10-26
```

**SUGGESTED FIX** Add a §2 subsection "**Axiom hygiene: the `Classical.choice` leak catalogue**"
that lists, in one table, _leak source → probe → clean spelling_ (dependent `match`/`cases` on an
equation; `simp at h` on a length equation; `decide` under a `∀ Fin`; `omega` on a disjunction;
`omega` on a Nat-subtraction trichotomy; `decide_eq_true (by omega)` — finding 1; the
`Nat.lt_of_mul_lt_mul_left` family). Leave the date-stamped entries where they are, linked to it.
Then fix the three ordering violations.

---

## 11. LOW-MEDIUM — "When to read what" is a 5-row table with two dead/absent rows

**LOCATION** lines 22–33; anchors at 482 and 1625.

**WHAT IS WRONG** The table maps only §1, §2, §3, §4 and §7. §5 (Repr/`#eval`) and §6 (Lake
`@[extern]`/script lakefile — a genuinely non-obvious 12-item section) have **no** entry point.
The "Append new learnings" section — 1143 lines, **51 %** of the file, containing every finding
above — has **no** row and no index at all; the only pointer to it is the parenthetical
`"— and the 2026-10-18 'boxed scalar ceiling' entry in the Append"`, a reference by _date_ into a
date-ordered pile with three ordering violations. There is no TOC beyond these five anchors.

**EVIDENCE** `grep -n '^## '` → 10 headings; the "When to read what" table references 5 of the
7 numbered sections and neither of the two trailing sections. The word "boxed scalar ceiling"
occurs exactly **once** in the file (line 31, the pointer) — the entry it points at is a
different title, so the link cannot be resolved by search.

**SUGGESTED FIX** Add rows for §5, §6, and a "Append" row with a topic index
(`Classical.choice` · `omega` · `simp`/`rw` · `cast`/`Fin`/dependent types · `Bytes` carriers ·
performance · proof-process). Better: split the Append into the topic sections naming the topics
above, keeping dates inside each section.

---

## 12. LOW-MEDIUM — `2 dated claims were verified as _correct_ but are stated without the qualifier that makes them true

**LOCATION** line 1067–1069 (_"`omega` alone does not unfold `(v/8) % 8`"_), lines 539–545
(_"`omega` does not see field projections"_), line 489 (_"`omega` **cannot** derive `n % 4 = 0`
from `∃ k, n = 4 * k`"_).

**WHAT IS WRONG** The third one is stated too broadly and will mislead: `omega` **can** derive
`n % 4 = 0` from the _equation_ `n = 4 * k`; what it cannot do is the existential form.
Verified both ways — and note the skill's own recommended fix (`rw [hn, Nat.mul_mod_right]`) is
fine, so the only damage is over-caution.

**EVIDENCE**

```lean
theorem mod1 (n k : Nat) (h : n = 4 * k) : n % 4 = 0 := by omega      -- OK
#print axioms mod1   → [propext, Quot.sound]

example (n : Nat) (h : n % 4 = 0) : ∃ k, n = 4 * k := by omega
→ error: omega could not prove the goal: … a := ↑n / 4
```

**SUGGESTED FIX** Narrow line 489 to "`omega` cannot use a _modulo_ hypothesis (`n % 4 = 0`) or
prove an existential from it; the _equational_ form `n = 4 * k → n % 4 = 0` **is** in `omega`'s
fragment (verified 4.34.1)".

---

## 13. LOW — a "verified" claim is given a diagnostic that the reader cannot reproduce

**LOCATION** line 511: _"even though `#print axioms` on an *isolated* `theorem t (k) (hk : k < 4) :
k = 0 ∨ … := by omega` is clean (context-dependent)"_.

**WHAT IS WRONG** Verified: the isolated lemma **is** clean, and — important — the _clean_ result
is what most readers will see, because the leak needs the surrounding `_proof_*` context. So the
entry as written tells a reader "reproduce this probe to see it", and the probe will **not**
reproduce the leak. That invites a future session to "refute" the entry and delete it (exactly
the failure mode the file's own 2026-10-25 entry warns about).

**EVIDENCE**

```lean
theorem iso1 (k : Nat) (hk : k < 4) : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
#print axioms iso1     → [propext, Quot.sound]        -- clean!
```

while the composed form leaks (finding 1: `ta`).

**SUGGESTED FIX** Say plainly: "the **isolated** lemma is clean; only the _in-context_ use leaks
— do not use the isolated probe as a refutation; the authoritative check is `#print axioms` on
the **enclosing theorem** and on its `_proof_*` children."

---

## 14. LOW — line 1752's `Suffix.ext` claim is unreproducible outside the project's own signature

**LOCATION** lines 1752–1757: _"`Suffix.ext … : t₁ = t₂` cannot be applied by `apply Suffix.ext`
on a goal … — `refine Suffix.ext (t₁ := …) (t₂ := …) ?_ ?_` (named, in order)."_

**WHAT IS WRONG** The stated cause is that the implicit `{t₁ t₂}` cannot be inferred from the
goal. Reproduced with a minimal structure: `apply Sfx.ext'` on `a = b` **does** fire when the
lemma's implicits are inferable from the goal, and leaves exactly the two subgoals — so the
"cannot be applied by `apply`" claim is true only for the project's particular `ext` shape (whose
arguments are _not_ inferable), not for `apply` generally. As written it reads as a fact about
Lean; it is a fact about that one lemma.

**EVIDENCE**

```lean
theorem Sfx.ext' {t₁ t₂ : Sfx n} (hrem : …) (hbytes : …) : t₁ = t₂
example (a b : Sfx 3) … : a = b := by apply Sfx.ext'
→ case hrem … ⊢ a.remaining = b.remaining
  case hbytes … ⊢ a.bytes = b.bytes            -- `apply` worked fine
```

(the failing shape needs an `ext` whose implicits the goal cannot pin, e.g. when `t₁`/`t₂` appear
only under a `cast`).

**SUGGESTED FIX** Reframe as "when an `ext` lemma's `{a b}` cannot be inferred from the goal
(the usual cause: one side is a `cast`), `apply` fails — pass them by name: `refine Foo.ext
(a := …) (b := …) ?_ ?_`", and give the `cast` symptom, which is what actually happened.

---

## 15. LOW — the file contradicts itself on whether `codec`-shaped advice belongs here

**LOCATION** lines 17–20 and 485 ("keep entries generic (no project names/paths)") vs. every
entry from 498 to 1600 and the closed "Changelog" (1625–2233) which re-describes the same project
work a second time.

**WHAT IS WRONG** Beyond the volume (finding 2), there is a **structural duplication**: the
Changelog section (lines 1625–2233, ~608 lines) restates entries already present in the Append
(e.g. 1627–1633 restates 493–495; 1657–1665 restates 1653/1663; 1571–1600 appears in both an
Append entry and a Changelog summary). Two copies of the same lesson, kept in different date
orders, is the "one source of truth per concern" rule violated inside a single file.

**EVIDENCE** `## Changelog` begins line 1625; it contains 11 date-stamped paragraphs summarising
"Added N entries (see 'Append new learnings')" for material that is _already above it_.

**SUGGESTED FIX** Delete the Changelog section, or reduce it to a one-line "see the entries
dated X" per session. Do not summarise an entry that is in the same file.

---

## 16. LOW — several entries are unsearchable because the title is a whole paragraph

**LOCATION** e.g. 493, 495, 497, 500, 503, 522, 584, 599, 614, 1005, 1040, 1096, 1160, 1788,
1824, 1916 — entries whose `**bold**` "title" runs 60–120 words across the full paragraph.

**WHAT IS WRONG** The file's retrieval story is "search the bold lead-in". When the lead-in is
longer than a sentence it is unsearchable — you cannot remember the wording, and grep on the
concept returns 8 false hits. Example: the entry everyone needs most (the `Classical.choice`
leak family) has no stable phrase; three entries say "the leak lands in `_proof_*`" in three
different wordings.

**EVIDENCE** the bold run at 493 is 258 characters before the first sentence ends; at 1040 it is
365 characters. Compare 1067/1071 which _are_ short and therefore findable.

**SUGGESTED FIX** Cap bold lead-ins at ~70 characters and put the detail after. Establish
recurring phrases: "leak: …", "fix: …", "probe: …" so the family is greppable.

---

## 17. LOW — "documented" behaviour that no longer matches the runtime, stated as a rule

**LOCATION** line 84–90 (covered in 5) is the big one; smaller instance: line 1179 (_"a `simp` that
reports 'unused' in one arm is usually needed in the other arms"_) and line 1489 (_"`ByteArray.push` …
do not unfold"_) direct the reader away from lemmas that now exist.

**WHAT IS WRONG** With `ByteArray.append_assoc`, `ByteArray.data_append`, `ByteArray.data_push`
available on 4.34.1, at least two entries give "prove it yourself / it does not reduce"
guidance where a stdlib lemma does the job. Every such entry compounds: a future agent re-derives
`bpush_data`-style lemmas that the toolchain now ships.

**EVIDENCE**

```
@ByteArray.append_assoc : ∀ {a b c : ByteArray}, a ++ b ++ c = a ++ (b ++ c)
example (a : ByteArray) (b : UInt8) : (a.push b).data = a.data.push b := rfl              -- RC=0
example (a b : ByteArray) : (a ++ b).data = a.data ++ b.data := ByteArray.data_append      -- RC=0
```

**SUGGESTED FIX** Add a standing instruction at the top of §2: _"before writing a
carrier-projection lemma, `#check ByteArray.` / `#check List.` — several of the 2026-10
'prove it yourself' entries below are now one stdlib lemma."_

---

## 18. LOW — the header's "reads after / wins on conflict" precedence is never operationalised

**LOCATION** lines 17–20.

**WHAT IS WRONG** "Where they disagree, the official skill's proof-engineering guidance wins" is
a rule with no enumerated disagreements, and the two files _do_ disagree in at least one
consequential place (finding 3). A precedence rule that is not applied to the actual conflicts is
worse than none: it lets a future agent pick whichever file supports the cheaper path.

**EVIDENCE** see finding 3.

**SUGGESTED FIX** Replace with an explicit three-line precedence list: (1) this file's axiom gate
and `[propext, Quot.sound]` discipline; (2) the official skill's LSP/search/proof-engineering
guidance; (3) this file's project-layout and performance sections. Note the one real conflict
(`Classical.choice`) inline.

---

## 19. LOW — `#print axioms` guidance is split between two entries that disagree on what to print

**LOCATION** lines 215–219 (_"print axioms on **top-level declarations**"_) vs. 530–538
(_"`#print axioms` on `_proof_*` children"_) vs. 509 (_"`Expr.getUsedConstants` shows no
culprit — the leak is in an auto-generated `_proof_*`"_).

**WHAT IS WRONG** Three entries, three different instructions, no single procedure. A reader
who hits a leak has no ordered recipe: print the theorem, then bisect the skeleton, then print
`Thm._proof_1_4`, then give up on `Expr.getUsedConstants`. This is the highest-value procedure in
the file and it does not exist as a procedure.

**EVIDENCE** the three entries above; `AGENTS.md` itself says "_`#print axioms Codec.roundtrip`
is the check_" — i.e. the _project_ instructions carry a cleaner one-liner than the skill does.

**SUGGESTED FIX** One numbered recipe: "1. `#print axioms <thm>` (top-level, never a module or a
shadowing type name — see 215). 2. If dirty, `#print axioms <thm>._proof_1_…` for each child. 3. Bisect by shrinking the body to `⟨_, rfl⟩` — still dirty ⇒ the elimination, not the
arithmetic. 4. Fix by the table in finding 10."

---

## 20. LOW — headline performance numbers have no benchmark and no conditions attached

**LOCATION** line 31 (_"why is it ~20-40x off C?"_), 1305–1319.

**WHAT IS WRONG** "~20-40x off C" is a _range spanning 2×_, derived from one parser on one
machine, presented in the nav table as a property of the language. It is the number a future
agent will quote to justify stopping optimization. Either attach the conditions (measurement,
input, toolchain) or stop calling it a ceiling.

**EVIDENCE** line 1308 gives the actual measurement (`~206 → ~440 ns` for the `USize` rewrite) —
a 2× regression — which does **not** support "20-40× off C" on its own; the "20-40×" figure has
no derivation anywhere in the file.

**SUGGESTED FIX** Change the nav row to "measured 20-40× off an equivalent C parser _for one
RFC-3339 parser, 4.30, macOS_; treat as anecdote, re-measure first"; keep line 1305's honest
per-measurement numbers.

---

## 21. LOW — entry at 487 duplicates official-skill content and this repo's own AGENTS.md rule

**LOCATION** line 487 (2026-10-26, `git stash`/`git reset` prohibition + "commit incrementally").

**WHAT IS WRONG** The identical rule, with the identical rationale, is in this repo's
`AGENTS.md` ("**Never `git stash` / `git reset` / `git checkout -- <file>` to 'start clean'** —
it has destroyed verified work here") and the staging rules are in the official `lean4` skill.
Duplicating a safety rule in three places guarantees divergence. It is also the _first_ entry in
the Append, i.e. the most-read position, spent on a non-Lean fact.

**EVIDENCE** `AGENTS.md` line ~"Never `git stash`"; official `SKILL.md` § File Handling Rules
("_Never use `git add -A`…_").

**SUGGESTED FIX** Delete from the skill; keep it in `AGENTS.md` where it is enforced.

---

## 22. LOW — no "what is _not_ covered" / no disclaimer that the file is stdlib-only and 4.34-pinned

**LOCATION** header, lines 1–20.

**WHAT IS WRONG** Everything in the file is measured on **stdlib-only, no mathlib, Lean 4.34.1**.
An agent reading the file on a mathlib project will apply `[propext, Quot.sound]`-only discipline
and `omega`-leak workarounds that are unnecessary there, and will believe `split_ifs` is gone
(it is a mathlib tactic — which is _why_ it is unavailable here, a fact the file never states).
The omitted reason is the actionable part.

**EVIDENCE** line 1935 says "split_ifs no longer exists in Lean 4.34" — the accurate statement is
"it is a mathlib tactic and this project is stdlib-only".

**SUGGESTED FIX** Two-line "Scope" block at the top: "_all measurements are stdlib-only
(no mathlib) on Lean 4.34.1; tactics named as 'missing' (`split_ifs`, `norm_num`, `decide?`) are
missing because mathlib is not a dependency, not because the toolchain dropped them._"

---

## Counts

| severity  | count                    |
| --------- | ------------------------ |
| CRITICAL  | 0                        |
| HIGH      | 3 (findings 1, 2, 3)     |
| MEDIUM    | 7 (4, 5, 6, 7, 8, 9, 10) |
| LOW       | 12 (11–22)               |
| **total** | **22**                   |

### Verified-correct claims (do not re-litigate)

These were probed and hold on 4.34.1: `-/` closing a doc comment (74); `/-!` before `import`
failing (68); `at` unusable as a `rciter` binder (line 350, `error: unexpected token 'at'`);
`open` unusable as a binder (358); `Nat.lt_of_mul_lt_mul_left` / `Nat.mul_lt_mul_left` /
`Nat.lt_of_mul_lt_mul_right` being `Classical.choice`-dependent while `Nat.mul_le_mul_left` /
`Nat.le_of_not_gt` are clean (530); `Nat.lt_or_gt_of_ne`-based `omega` disjunction leaking
(511); `USize` unboxed in argument position and re-boxed in `Option` (446); `Nat` always boxed;
the `open Codec` constructor-shadowing trap (897); `Except`/`Option` `do`-blocks reducing by
`rfl` (line 92's `do` warning is _too strong_ — `do` does reduce on 4.34, see finding 4's
neighbourhood); `by_contra` genuinely unknown without `import Init.Classical` (1081).

---

# Adversarial performance review — measured, not read

Scope: the public decode/encode paths (`Codec/Decode.lean`, `Codec/Encode.lean`,
`Codec/Packed.lean`) and the performance claims in `README.md` §Performance and
`AGENTS.md` ("Axiom discipline" / performance bullets).

Method: compile a `lean_exe` that links `Codec/ByteSlice.c`, run the built binary
under `IO.monoNanosNow`, and A/B each candidate against a hand-written equivalent
that uses the **same** types and the **same** helpers. Every figure below is a
whole-program measurement of the emitted native binary — **not** `#eval`, not
`lake env lean` (see finding R5.1's "measurement trap" note, which cost this
review two wrong intermediate conclusions).

Severity keys as before: **CRITICAL** (unsound / divergence), **HIGH** (claim not
upheld), **MEDIUM** (gap / wasted work), **LOW** (hygiene), **INFO**.

---

## 1. CRITICAL — `decodeFull` is a Θ(n²) _search_ that re-decodes at every level, ~530× slower than a single-pass fold; the documented "20–40× off C" ceiling is therefore false by ~4 orders of magnitude on the decode path

> **CORRECTED 2026-10-28, before any fix was attempted.** This finding was first
> filed as "`WellFounded.fix` on a dependent `Sigma` does not compile to a loop",
> with the fix "re-express as structural recursion". **The measurement was right;
> that diagnosis was wrong, and the prescribed fix was implemented and measured as
> a no-op** (see "The refuted diagnosis" below). The cause is the _algorithm_, not
> the recursion scheme. The finding id, severity and the headline numbers stand;
> the mechanism and the suggested fix are rewritten.

**LOCATION**

- `Codec/Decode.lean:115-127` (`decodeRepeat` def) and `Codec/Decode.lean:194-205`
  (`decodeFull` def) — both are
  `WellFounded.fix (InvImage.wf (fun ns : Sigma fun k => Bytes k => ns.1) Nat.lt_wfRel.wf) …`.
- `Codec/Decode.lean:171-173` (docstring naming `decodeFull` "the same denotation
  restricted to the single full-consumption result … **without building every
  intermediate prefix**", implying it is the fast path).
- `README.md:512-530` ("The honest ceiling") and `README.md:515`
  ("bottoms out around **20–40× slower than hand-written C**").
- `AGENTS.md:171-176` ("**Pure-Lean parsing has a ~20–40×-off-C ceiling, and that
  is accepted.**").

**WHAT IS WRONG**

Three compounding claims are false as stated, and the dominant term is **our own
recursion scheme**, not the compiler.

1. **`decodeFull` is ~519× slower than a single-pass fold.** A `foldr` over
   `List.range n` that calls the _same_ `decode`, the _same_ `bdrop`, consumes the
   _same_ `Bytes n`, and returns the _same_ `Option (List UInt8)` is 519× faster at
   n=4096 (176 µs vs 91,382 µs) — and returns a **bit-identical value** (verified
   for n ∈ {0..7}). **The cost is the algorithm, not the recursion scheme.**
   `decodeFullStep` is a _backtracking search_ that, at each of the n levels, calls
   `decode p s` over the _whole remaining buffer_ and recurses into the candidates.
   For `Codec.byte` there is exactly one candidate per level, so it performs n
   nested steps each doing O(n) scan work — Θ(n²) _work_. The `walk` fold makes one
   linear pass. Measured decomposition at n=4096: all n `decode` calls in a plain
   loop cost **140 µs**, `.attach` adds nothing measurable, and building the result
   list adds nothing measurable — yet `decodeFull` pays 91,382 µs for the same
   `decode` calls, because it makes them again at every level of the search.
2. **The 20–40× figure does not describe the decode path at all.** On the shipped
   public decoder it is ~95 µs/byte ≈ **0.01 MiB/s** — roughly **10^5× off** the
   1,344 MiB/s `memcpy` floor measured on the same machine in the same run. Even
   `encodeRepeat`, the _fast_ public path, is ~31 MiB/s ≈ **43× off** that floor,
   which is at the optimistic end of the documented range and only for encode.
3. **The README attributes the whole gap to boxed arithmetic** (`lean_nat_mul`,
   `lean_uint8_to_nat`, `instAddUInt64`). Boxed arithmetic is real, but it is not
   the dominant term for decode: the dominant term is the well-founded recursion
   plus result-shape allocation. A reader who acts on the README ("the compiler is
   the limit; do not micro-optimize") would leave a 588× implementation defect in
   place. That is precisely the false assurance this change exists to remove.

**EVIDENCE** (`lake build <probe>` then run the binary; probe source in the table's
footnote)

Required reduction, n=4096, one process, three consecutive calls:

```
n=4096:
  decodeFull (shipped, WellFounded.fix on Sigma): 100614 us (v 4096)
  walk (structural fold, same types):               171 us (v 4096)
```

**588×**, with the values equal. Repeated at n ∈ {1024, 2048} the ratio is
188× and 306× (it grows with n, consistent with the fix-machinery being
super-linear relative to the structural fold).

Value agreement (so this is genuine equivalent work, not `walk` doing less):

```
n=0: decodeFull=(some 0) walk=(some 0) AGREE=true
n=1: decodeFull=(some 1) walk=(some 1) AGREE=true
n=5: decodeFull=(some 5) walk=(some 5) AGREE=true
n=64: decodeFull=(some 64) walk=(some 64) AGREE=true
```

Absolute throughput, n=16384, same binary:

```
n=16384:
  decodeFull:              1561265 us   0 MiB/s   (bytes 16384)   ~95 us/byte
  encodeRepeat:                491 us  31 MiB/s   (bytes 16384)
  byteSlice (memcpy floor):     11 us 1344 MiB/s  (bytes 16384)
```

So decode is ~1.1×10^5 off the `memcpy` floor on this machine, encode ~43× off.
`decodeRepeat` is separately and _inherently_ Θ(n²) — its return type
`List (List α × Suffix n)` demands all n+1 prefixes — which is the paper's §4.4
cost and is documented; **`decodeFull` was added to escape that and does not**,
because it keeps the same fix-on-sigma scheme.

**MEASUREMENT TRAP (recorded so it is not re-entered).** Two intermediate
conclusions in this review were wrong and are worth recording:

- `lake env lean file.lean` **interprets**; a `main` defined there does not run,
  and timings from it are meaningless (they read as `0 us`).
- `#eval`/interpreted probes and any binary where only `.length` is forced get
  **dead-code eliminated**, again reporting `0 us`. A lane only measures the
  computation if the value is forced through a returned tuple, which is what
  `Bench.lean`'s `timeBatch` does — hence the `let (out, dt) ← timeBatch …`
  shape. Treat any `0 us` result as "not measured", never as "instant".
- consequently `Bench.lean:706`'s placement of the seam checks is not excused by
  a crash: the default-size run is slow, and the remedy is ordering, per R2.2.

### The refuted diagnosis — structural recursion is a no-op here

The original fix for this finding was `tasks.md` 6.1: "re-express `decodeFull`
(and the productive step of `decodeRepeat`) as structural recursion over the
length index / a cursor". That was implemented and measured before it was
discarded, because it does not work:

```
n=4096:
  decodeFull  (shipped, WellFounded.fix on Sigma):  94137 us
  decodeFullS (structural, termination_by n _ => n): 93691 us    <- no improvement
  walk        (single-pass fold):                      176 us     <- 519x faster
```

```
n=4096:
  decodeRepeat  (WellFounded.fix): 633395 us
  decodeRepeatS (structural):      623507 us    <- no improvement
```

Two conclusions, both worth recording so this is not re-attempted:

1. **`WellFounded.fix` is not the cost.** Lean's `termination_by` elaborates to
   the _same_ well-founded recursion, so a "structural" rewrite is not even a
   codegen change — `decodeFullS` and `decodeFull` differ by 0.5%, i.e. noise.
   (`Codec/Decode.lean`'s `decodeRepeat` and `decodeFull` are instrumented in the
   emitted IR as `lp_codec_WellFounded_fixC___at___00Codec_decodeFull_spec__0`,
   allocated closures per level; that looks alarming but is measurably irrelevant
   beside the Θ(n²) work described above.)
2. **`decodeRepeat` is _not_ slow for this reason at all.** It is Θ(n²) because
   its return type `List (List α × Suffix n)` demands all n+1 prefixes — the
   paper's §4.4 cost, already correctly recorded in this file's
   "Verified-correct claims" block. A structural rewrite cannot change that, and
   `decodeRepeatS` confirms it (623 ms vs 633 ms at n=4096).

The real lever is `decodeFull`'s **allocation-free single pass**: consume
`decode p s` once, take the candidate whose remainder recurses to a full
consumption, and never re-scan. That is what `walk` demonstrates at 176 µs, and
it is what `decodeArray`'s cursor shape already achieves in the packed lane.

**SUGGESTED FIX** — see `tasks.md` §6 (as revised). In outline: give
`decodeFull` a **single-pass** formulation that consumes `decode p s` once per
level and never re-scans the remaining buffer, keep every existing theorem, and
prove the new definition equal to the old so the specification surface does not
move. Do **not** attempt the structural-recursion rewrite: it is measured as a
no-op. Then re-baseline `README.md` §Performance and the `AGENTS.md` bullet
against measured figures, attribute the residual gap correctly (**algorithm** vs.
result shape vs. boxed arithmetic), and stop presenting one number as "the"
ceiling.

Footnote — the probe is `import Codec; open Codec`, with

```lean
def bytesOf (n : Nat) : Bytes n := fun _ => (1 : UInt8)

def walk (n : Nat) (s : Bytes n) : Option (List UInt8) :=
  (List.range n).foldr (fun k acc =>
    match decode Codec.byte (bdrop k s) with
    | [(x, _)] => some (x :: acc.getD [])
    | _ => none) (some [])
```

and a `lean_exe` that links `byteSliceO`. The `lean_exe` must be added to
`lakefile.lean` temporarily and removed afterwards — `lake env lean` will not
produce a runnable binary.

---

## Counts

| severity  | count    |
| --------- | -------- |
| CRITICAL  | 1 (R5.1) |
| HIGH      | 0        |
| MEDIUM    | 0        |
| LOW       | 0        |
| **total** | **1**    |

### Verified-correct claims (do not re-litigate)

- The `Bytes n` substrate is **not** the performance problem. `bdrop` applied at
  every prefix length is **flat** (28/8/14 µs at n=1024/2048/4096) and **~460×
  faster** than the `List UInt8` `List.drop` it replaced (6,490 µs at n=4096).
  The single-carrier collapse was a speedup, not a regression.
- The `Suffix n` carrier and `.attach` are **not** the cost: `.attach` plus
  forcing every witness costs 206 µs at n=4096 against 184 µs plain (and `.attach`
  over all n levels costs 80-141 µs on its own).
- **The recursion scheme is not the cost either** - corrected 2026-10-28. A
  `termination_by`-structural `decodeFull` measures 93,691 µs against the shipped
  `WellFounded.fix` version's 94,137 µs at n=4096. See "The refuted diagnosis".
- `decodeRepeat`'s Θ(n²) _is_ inherent to its all-prefix return type, and a
  structural rewrite leaves it untouched (623 ms vs 633 ms at n=4096).
- `decodeArray`'s packed shape (`(α × Nat)` cursor, no suffix materialization) is
  the already-proved fast design (`decodeArray_eq`); it is a design answer, not a
  defect. It has no library caller — R2.4, unchanged by this lens.
- Layer 2 is at the `memcpy` floor (1,344 MiB/s measured), as documented.
