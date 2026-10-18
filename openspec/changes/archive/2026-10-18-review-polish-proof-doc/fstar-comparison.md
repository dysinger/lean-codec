# F\* `codec` vs the paper vs the Lean port — comparative audit

Companion to task 4.1 of `review-polish-proof-doc`. This tabulates, for each of the
paper's core objects and each of the Lean port's stated departures/strengthenings
(`README.md` anchors `[D1]`–`[D8]` / `[S1]`–`[S6]`), how the F\* library
(`../fstar-codec`, its `AUDIT.md`/`README.md`/`src/Data.Codec.*.fst`) lines up.
The finding confirmed below is the one the task predicted: **the F\* `codec` is far
more deviant than the Lean port** — it is a _binary serialization_ library that
cites the paper for motivation, not an implementation of the paper's
_partial-isomorphism / relation_ design.

## 1. The paper's central objects, three ways

| Paper (§)                                                                                                    | Lean port                                                                                                               | F\* `codec`                                                                                                                                                                                                                           |
| ------------------------------------------------------------------------------------------------------------ | ----------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `Iso α β = (α → Maybe β) × (β → Maybe α)`, inverse invariant in prose (§3.1, §5.1), composed as a category   | `Iso.lean`: strict partial isomorphisms, `Iso.law` a **field**, holds unconditionally. The core `codec` is built on it. | **No `Iso` at all.** A single flat `codec a` record (8 fields: `enc`/`dec`/`wfcv`/`wfcv_prop`/`rest_cond`/`roundtrip`/`dec_err_bound`/`dec_consumed_bound`). Invertibility is a per-combinator `roundtrip` lemma, not a composed law. |
| Syntax descriptions as **one value**, interpreted both ways (parser + printer), `$`/`*`/`                    | `/`empty`/`pure`/`token` (§3.4)                                                                                         | `Codec.lean`: inductive AST `iso`/`seq`/`alt`/`empty`/`pure`/`byte`; `decode`/`encode` are two interpreters of it.                                                                                                                    | Functions are primary (`enc`/`dec` total); the "one description" is a record of two functions plus guards, not an AST. |
| Denotational **relation** `Rel` (§4.3): a description _is_ a graph; decode = "find a member of the relation" | `Rel` in `Codec.lean`, preserved as the specification; `decode` returns the full backtracking union.                    | **No `Rel`.** The relation is implicit, reconstructed only by the solver-discharged `roundtrip` lemma + `wfcv`/`rest_cond` guards.                                                                                                    |

## 2. Lean departures `[D1]`–`[D8]`: does F\* share them, or over-shoot?

| Anchor                                            | Lean treatment                                                                     | F\* treatment                                                                                                                                                                                                                                              |
| ------------------------------------------------- | ---------------------------------------------------------------------------------- | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `[D1]` `String`→bytes (binary base)               | Re-bases to `UInt8`/`Bytes n`; text rebuilt downstream, not core.                  | Also byte-oriented (`byte_seq = Seq.seq byte`, `uint8`/`word16/32 be/le`/`varint`), **but** keeps an ASCII-only `text` (`string_to_bytes` with `% 256`, `string_is_ascii < 128` guard) — a lossy text primitive the Lean core deliberately omits (`[S3]`). |
| `[D2]` nondeterministic list decoder              | Keeps it: `decode` returns all `(value, remainder)` pairs.                         | **Total single-result** `dec : byte_seq → either error (value × nat)` — no backtracking union, no list of results.                                                                                                                                         |
| `[D3]` `                                          | ` = backtracking union                                                             | `decode (d₁                                                                                                                                                                                                                                                | d₂) = decode d₁ ++ decode d₂`.                                                                         | `alt`'s disjointness is a `wfcv` guard; errors carry an `ExpectedSumTag` code — a committed, error-coded ` | `, not a union. |
| `[D4]` lossless capture (no destructive `ignore`) | Strict `Iso.law` ⇒ `ignore` impossible; repetition captures runs verbatim.         | No `ignore`; but also no `Iso`/law to be strict about — lossiness is deferred to `wfcv` guards rather than excluded by construction.                                                                                                                       |
| `[D5]` no prefix-disjointness gate                | None needed; `                                                                     | ` is union.                                                                                                                                                                                                                                                | `alt` carries disjointness _in_ `alt_wfcv` (a value-level guard, not a proof of the paper's relation). |
| `[D6]` `Codec` is a value (AST), not a typeclass  | Inductive AST, structurally recursed.                                              | Neither the paper's typeclass nor an AST — a fat record of functions (no structural recursion over a description).                                                                                                                                         |
| `[D7]` `iterate` omitted                          | Omitted (fixpoint asymmetry); `foldl`/`foldr` provided with termination witnesses. | Has `satisfy_many0/1`, `count`, `take_until`, `one_of` — a _different_ vocabulary; no `iterate` either.                                                                                                                                                    |
| `[D8]` `pure`/`subset` carry a decidable witness  | `[DecidableEq α]`/`[DecidablePred p]`.                                             | `pure`/`satisfy` use `wfcv : a → bool` (a bare runtime `bool`, not a decidable/`Decidable` proof), plus the proof-only `wfcv_prop`.                                                                                                                        |

## 3. Lean strengthenings `[S1]`–`[S6]`: does F\* reach them?

| Anchor                                        | Lean                                                                                | F\*                                                                                                                                                                                          |
| --------------------------------------------- | ----------------------------------------------------------------------------------- | -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `[S1]` `Iso.law` a field, unconditional       | Yes.                                                                                | **Inverted:** the invariant is `roundtrip` + `dec_*_bound`, discharged by Z3 (`--z3rlimit` 40–2000, `SMTPat` triggers, a hand-maintained `lemma_varint_*` arithmetic block), not structural. |
| `[S2]` format-agnostic naming                 | `Codec`/`decode`/`encode`/`byte`.                                                   | Keeps the binary vocabulary (`byte`, `uint8`, `varint`) as primitives — the domain-specific leaves `[S3]` keeps out of Lean core are, in F\*, the _core_ itself.                             |
| `[S3]` zero domain-specific leaves in core    | `byte` + `pure` only.                                                               | 13 leaves incl. `uint8`/`word16be/le`/`word32be/le`/`varint`/`digits_to_int`/`text` — machine/format specifics baked in.                                                                     |
| `[S4]` `foldl`/`foldr` fresh well-founded     | Yes (measure witness).                                                              | `count`/`satisfy_many*` are the closest analogue, with no inverse-law framing.                                                                                                               |
| `[S5]` least-fixpoint `relRepeat` _proved_    | `relRepeat` + induction principle.                                                  | `satisfy_many0/1` have per-instantiation lemmas, but no least-fixpoint relation is stated.                                                                                                   |
| `[S6]` unbounded `many` semantic (strictness) | Repetition is three artifacts (denotation/decoder/encoder), because Lean is strict. | F\*'s `Seq`/totality has the same strictness concern, handled via `wfcv`/`take_until` rather than a separated relation.                                                                      |

## 4. Additions that have **no paper analogue** (all in F\*, none in Lean core)

- `dec_err_bound` / `dec_consumed_bound` — error-position and consumed-byte bound lemmas (binary-serialization bookkeeping; the paper has no notion of "remaining input to frame").
- `rest_cond : a → byte_seq → prop` — suffix framing condition.
- `wfcv`/`wfcv_prop` — the twice-encoded "in-domain / printable" guard (the paper's `Maybe` partiality, split into a runtime `bool` and a proof-only `prop`).
- The **Pulse layer** (`Data.Codec.Pulse`, C11 extraction via Custard) — a third design (separation-logic byte-buffer codec, 8 leaf types) under the same name, with its own hand-inlined, separately-verified varint roundtrip.

## 5. Bottom line

The F\* `codec` is a **good binary serialization library** (22 combinators, 0-admit,
118+10 tests) that cites Rendel & Ostermann for lineage. Its _architecture_ is the
inverse of the paper's: a monolithic record whose behavior the typechecker cannot
unfold, with invertibility reconstructed by a Z3/SMT solver; partiality pushed out
into `wfcv`/`rest_cond` guards; text handled only as lossy ASCII `% 256`; and a
Pulse/C-extraction layer bolted on. The Lean port (`../lean-codec`) is the opposite:
a thin `Iso`/`Rel` core over one length-indexed `Bytes n` substrate, structural
invertibility (`Iso.law` a field), the paper's backtracking-union decoder preserved
(`[D2]`/`[D3]`), binary leaves treated as _instances_ of a clean core (not record
fields), and only the genuine byte/binary deltas listed as `[D1]`–`[D8]`. Each F\*
deviation maps to a place where Lean stayed _closer_ to the paper, not further.
