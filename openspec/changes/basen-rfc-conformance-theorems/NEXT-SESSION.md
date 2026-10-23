# Next session — `basen-rfc-conformance-theorems` (re-anchored to the uniform surface)

Status at handoff: **4 / 19 tasks done (0.1, 0.2, 1.2, 1.3)**, plus a **facade-first
milestone** landed (uniform `encode`/`decode` over `List UInt8`), plus the
**content-extraction primitive** (this session, `../lean-basen` `2303421`). The
whole-input **roundtrip** (task 1.4) and the bespoke-triple **deletion** (task 1.1)
remain, and are tightly coupled: 1.1 cannot land until 1.4 gives the facade a
Codec-value roundtrip to dispatch to (the facade currently calls
`encodeBytes`/`decodeBytes`, which wrap the strict `encodeB64Strict`/`decodeB64Strict`).
Committed in `../lean-basen`; see §"Landed this session".

## Landed this session (commit `2303421` in `../lean-basen`)

**The content-extraction primitive** (task 1.4 crutx, item (a)) in `BaseN/Common.lean`:

- `Rel_count_satisfy_length p k xs s : Rel (count k (satisfy p)) xs s → xs.length = k`
  — the mirror of `Rel_count_satisfy_len` (`n = k`); together they give `n = xs.length`.
- `Rel_count_satisfy_ofFn p k xs s : Rel (count k (satisfy p)) xs s → List.ofFn s = xs`
  — pins the byte string to the exact list, where `Rel_count_satisfy_forall` only gave
  the predicate. Proved by structural induction on `k` + the `splice`/`concat`/`Fin`
  cast commutation (`List.ext_getElem?` + `splice_prefix_read`/`splice_apply` +
  `List.getElem?_ofFn` + `List.getElem?_cons` + `omega` on the `Fin` index).

Both are `#print axioms` = `[propext, Quot.sound]` (the length one is `[propext]`),
zero `sorry`, `lake build` green zero warnings. This was the precise "content-extraction
primitive" the task 1.4 note called out as missing; the `List.ofFn`/`Fin`-cast friction
you hit is real — use `List.ext_getElem?` (total `[i]?` form, no length hypothesis) rather
than `List.ext_get`/`getElem` to dodge the `n = n-1+1` index-validity subgoals.

## The one thing every session must not re-litigate

**`many` is derived, not a constructor.** Both references agree and it is verified
un-implementable in Lean:

- Paper §3.4: `many p = nil $ pure () | cons $ p ∗ many p` — a _derived recursive
  combinator_, never an elementary description.
- F\* `Data.Codec.Types.fst`: no `many` at all — `satisfy_many0`/`count`, `let rec`
  over the finite input; `codec a` is a _record_ of `enc`/`dec`/`roundtrip`.
- Lean: `many {α} (p) (h : Productive p) : Codec (List α)` with a denotational
  `Productive`/`ConsumesByte` field hits the `Codec → witness → Rel/decode → Codec`
  cycle; the mutual-inductive escape is rejected by the universe check (`Codec :
Type → Type 1` vs `Rel : … → Prop`). This is the same wall `11f7072` hit — it was
  _right_ about the impossibility, _wrong_ to fall back to per-format run triples.

**The fix is packaging, not a core change.** `relRepeat`/`decodeRepeat`/`encodeRepeat`
(and `takeWhile`/`sepBy`) are already in `Combinators.lean`, law-bearing,
`[propext, Quot.sound]`-only. The uniform surface is a **`Run` value** (a `structure`
bundling `elem : Codec α` + `step : ConsumesByte elem`, with `decode`/`encode`/`rel`
inherited) + a facade `encode (b : Base)` / `decode (b : Base)`. No `codec`-core change,
no `Codec.rec` conversion, no bespoke per-format function.

## Landed this session (commit in `../lean-basen`)

1. **`Run α`** in `BaseN/Common.lean` (task 0.1) — generic in the element value type
   `α` (fixed-width bases have `α = UInt8`; base32/64 have `α = List UInt8` block).
   Bundles `elem : Codec α` + `step : ConsumesByte elem`; accessors `Run.decodeFull`/
   `Run.decode`/`Run.encode`/`Run.rel` inherit `decodeRepeat`/`encodeRepeat`/`relRepeat`.
2. **Uniform facade** in `BaseN.lean` (task 2.1, facade-half) — `encode (b : Base) :
List UInt8 → List UInt8` (total) and `decode (b : Base) : List UInt8 → Option
(List UInt8)`, one value type `List UInt8`, `cases b` dispatch.
3. **`B32`/`B64 ↔ List UInt8` byte transport** in `BaseN/Base32.lean`/`BaseN/Base64.lean`
   (`b32BytesOf`/`b64BytesOf`/`b32OfBytes`/`b64OfBytes` + `roundtripBytes`),
   `[propext, Quot.sound]`-only. The transport is **bijective** because the
   terminal-tail shape is recoverable from byte length `mod` the block width.
4. **`Bridge.bytesToList`/`Bridge.listToBytes`** for the fixed-width `Bytes n ↔
List UInt8` facade conversion.

`lake build` + `lake build bench` green, zero `sorry`/warnings; `#print axioms` on the
new `roundtripBytes` laws = `[propext, Quot.sound]`.

### The remaining deep work is NOT done (do not claim it is)

The facade currently **wraps the existing strict/parse base32/64 functions**
(`decodeB32Strict`/`encodeB32Strict`/`decodeB64Strict`/`encodeB64Strict`) with the
byte transport. Task 1.1 (delete those bespoke run triples) and 1.3 (re-express
base32/64 as a **`Codec` value** over the full-block `Run` + terminal-tail
`alt`/`iso` onto `B32`/`B64`) are **still open**. That is the next unit of work.

## Next implementation order (remaining §0–§5)

**The single blocking item is task 1.4's whole-input roundtrip**
`decodeFullB64 (encodeB64 bs) = some bs` (and the base32 mirror). Nothing else can
land first: task 1.1 deletes the strict triples the facade still dispatches to, and
that deletion is only safe once `decodeFullB64`/`encodeB64` have their roundtrip proved
(so the facade can rewire to the Codec value, task 2.1). Correct order:

1. **1.4 (the hard core)** — prove `decodeFullB64 (encodeB64 bs) = some bs`. The
   `decodeFullB64` definition is `List.head? ((decodeRepeat b64BlockElem … n s).filterMap …)`,
   so the proof needs the **committed-block-prefix uniqueness** (item (b) of the task
   1.4 note). The pieces that exist:
   - `decodeRepeat_prefix_concat` lifts `(blocks, empty m₁) ∈ decodeRepeat … sb` to
     `(blocks, Suffix.drop m₁ (concat sb st))` (Common.lean).
   - `decodeFull_b64Tail_suffix_nil`/`_cons` decode the tail over the dropped suffix.
   - `not_rel_b64BlockElem_of_pad` + `b64Char_pad_false` (the block element can't match a
     `=` byte). `Rel_b64BlockElem_canonical` (block bytes are all `b64Char`, no pad).
   - the new `Rel_count_satisfy_ofFn` (content extraction).
   - **Not yet written**: (i) `encodeB64Tail tail = some ⟨q,st⟩ → tail ≠ [] →
∃ i : Fin q, (st i).toNat = 61` (the tail encoding has a `=` pad — read it off
     `b64BlockUnapply [b] = [c0,c1,61,61]` / `[a,b] = [c0,c1,c2,61]`, then
     `Codec.encode b64TailElem` = `b64TailUnapply` `bind` `count 8 (satisfy b64OrPad)`);
     (ii) the uniqueness lemma: any `(blocks', t') ∈ decodeRepeat b64BlockElem … (concat sb st)`
     with `decodeFull b64TailElem t'.bytes ≠ none` has `blocks' = blocks`. The pad dichotomy
     (alphabet vs `=`) disambiguates the length-8 edge cases (2 blocks of 4 bytes vs a
     tail: `b64TailApply` rejects a 3-byte output, so a full-block prefix never decodes as
     a tail at the wrong boundary); (iii) a `List.head?`-of-`filterMap`-with-unique-hit
     lemma pinning the result. **A cleaner alternative to consider**: re-express
     `decodeFullB64` without `head?`/`filterMap`, as a `decodeFullStep`-style direct
     `Option`, so the inherited `decodeFull` machinery applies (design D1 says the value
     type should be the terminal-tail `B64` via `iso`, not the current flattened
     `List UInt8` + `head?`) — that is a design-decision, flag it before re-scoping.
   - **A decomposition lemma was attempted this session and is Sigma-eq-fiddly**: to
     unwrap `encodeB64 bs = some ⟨n,s⟩` into `encodeRepeat b64BlockElem (b64Split bs).1
= some ⟨m₁,sb⟩ ∧ encodeB64Tail (b64Split bs).2 = some ⟨m₂,st⟩ ∧ n = m₁+m₂ ∧ HEq s
(concat sb st)`, do `cases (Option.some.inj he')` on the Sigma equality (gives `rfl`
     for the length and a `HEq` for the bytes); do **not** `congrArg Sigma.snd` (dependent
     projection) and do **not** let `simpa [heb,het]` rewrite the in-scope `heb`/`het`.
2. **2.1/2.2/2.3** — rewire the facade `encode`/`decode` to dispatch `cases b` to
   `encodeB64`/`decodeFullB64`/`encodeB32`/`decodeFullB32` (not `encodeBytes`/`decodeBytes`),
   then prove the `Base`-dispatching `roundtrip`, `decode_encode_inverse`, `encode_injective`.
3. **1.1** — now delete `parseB64`/`encodeB64Strict`/`relB64Strict`/`decodeB64Strict` +
   base32 analogues and their per-format lemmas (keep `B32`/`B64`, digit math, block `Iso`s).
4. **3.x/4.x** — re-prove the three conformance families per base over the uniform
   `Codec.decode`/`Codec.encode` (rejection / canonical / converse + injectivity);
   the fixed-width halves already have these laws (`decodeFull_canonical`,
   `rejects_invalid_byte`, `rejects_lowercase`, `rejects_odd_arity`, etc.).
5. **5.x** — re-anchor `Bench.lean` to the facade (never the bespoke fns), gate
   `lake build` + `lake build bench`, `#print axioms` = `[propext, Quot.sound]`,
   `nix flake check` green; update `openspec/changes/lean-basen/` §4.1.

## Recall: the re-anchor commit and what it superseded

`lean-codec` `40e88eb` (2026-10-22) re-anchored this change to the uniform surface,
explicitly superseding the `../lean-basen` run-triple commits `bb46230` through
`1cc040e` (the strict/parse base32/64 work). Those strict functions are **still in
the tree** (re-used by the facade-first milestone) and are precisely what tasks
1.1/1.3 delete next.
