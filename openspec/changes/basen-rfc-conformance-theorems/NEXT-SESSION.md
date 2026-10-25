# Next session — `basen-rfc-conformance-theorems`

**Status at handoff: 25 / 31 tasks done. `openspec validate` green.**
`../lean-basen` `HEAD` = `73f2583`; `../lean-codec` = `8cb0d5b`. Both pushed.

## START HERE — implement task 6.4

The rejection theorems are a **finite vector set**, not the general law the
proposal promises. Prove, for **all** `s` (then mirror for base32):

- **(a)** any byte `b` with `b64Valid b.toNat = false` ⇒ `decodeFullB64 s = none`
  (generalise `reject_invalid_char` — it is index-0 only — to **every** index);
- **(b)** a `=` at a **non-terminal** position ⇒ `none` (the `Zg==Zg==` /
  `MY======MY======` class — currently only implicit in the D8 `≤ 1` guard; no
  theorem states it);
- **(c)** `n % 4 ≠ 0` ⇒ `none` (base32: `n % 8 ≠ 0`). **Only genuinely hard
  one** — needs the arity argument lifted off the named vectors.

Every law `[propext, Quot.sound]`-only, gated in `Axioms.lean`, bench-covered.
Work in `../lean-basen`, in that repo's own `nix develop`.

Starting points that exist and are confirmed present in `BaseN/Base64.lean`:
`decodeFullB64_some` (decomposes into blocks + a `≤ 1`-element tail),
`Rel_b64BlockElem_len` (4 bytes/block), `relB64Tail_len` (4 bytes/tail), the D8
`tails.length ≤ 1` guard inside `decodeFullB64_reject_ZgAAAA`, and
`b64BlockDecodeLenient`'s pad-rejection arms. For (c): `b64Split`'s block run
consumes `4 · blocks.length` and the tail `0` or `4`, so `n` must be `4·k`.

**Then** `tasks.md` § "6.5 — Remaining order": **6.11 _then_ 6.6** (6.11 first —
both MODIFY the same requirement block and archive silently keeps one version).
Section 7 is a separate change, out of scope.

## Landed last session (6.2 + 6.3, and 4.4 with them)

- **6.2 (CRITICAL C2)** — the spec's injectivity Scenario is
  `encode{X} v = encode{X} v' → v = v'`; the shipped theorems assumed both sides
  `= some ⟨n,s⟩`. Fixed by **proving totality and restating**, never by weakening
  the spec. Seven `…_injective_eq` laws; totality layer is
  `Common.encode_satisfy_ne_none` / `encode_seq_ne_none` /
  `count_satisfy_encode_ne_none` plus `{x}BlockUnapply_digits` /
  `b{64,32}BlockUnapply_len{3,5}` / `b{64,32}TailUnapply_len{12,14}` /
  `b{64,32}Split_ofBytes_shape_bounds` / `encodeB{64,32}_ne_none`.
- **6.3 (MEDIUM M3)** — `decodeFullB{64,32}_char`:
  `decode s = some v ↔ ∃ w, encode w = some ⟨n,s⟩ ∧ v = w`. Pure assembly over
  `decodeFullB*_conv` (→) and `decodeFullB*_roundtrip` (←).

**Gotcha worth knowing before you start 6.4** (now in the `lean` skill): a
_dependent_ `cases`/`match` on a list whose **equation** is in context
(`bs.length = 1 ∨ bs.length = 2`, `ds.length = k`) leaks `Classical.choice` even
when every cited lemma is `[propext]`-clean. Restate the hypothesis numerically
(`1 ≤ bs.length`, `bs.length ≤ 2`) or derive the index from the term. Bisect by
shrinking the body to `⟨_, rfl⟩`: if it still leaks, it is the match.

---

# Historical: earlier sessions

## This session (2026-10-24): precision/coherence pass — no task-code changes

An independent hypercritical review of `PAPER.md` / `README.md` / `Codec/` /
`openspec/` found **3 CRITICAL** + **4 WARNINGS**, all in the _scholarly-attribution
and type-label layer_ (not the code's correctness). All fixed and re-validated
(`lake build` green, `openspec validate` green):

1. **CRITICAL — fabricated paper provenance.** The paper defines only `many` (§3.4)
   and `chainl1` (§6.1); `sepBy`/`chainr1`/`optional`/`maybe`/`choice` are **not** in
   the paper. Fixed the `README [S6]` and `Codec/Combinators.lean` docstring to say
   these are `codec`'s own additions in the §6.1 derivation style (not "paper §6.2",
   which is the Abstract Syntax section and defines nothing).
2. **CRITICAL — `NEXT-SESSION` mis-wrote base64's tail as `count 8 (satisfy b64OrPad)`**
   (base32's width). Fixed to `count 4`.
3. **CRITICAL — §3.1 vs §6.3 for `ignore`** (`ignore` is defined at §6.3, not §3.1;
   §3.1 is the general "modulo equivalence classes" remark). Fixed `README [D4]`.
4. **WARNINGS — fixed-width bases mis-typed as `Codec (List UInt8)`**; they are an
   element `Codec UInt8` + the derived `Run`. Fixed in the synced `specs/basen/spec.md`
   and the change's basen delta. Also loosened the "three instantiations of `ignore`"
   (it is two + one composition) and the "inherited `Codec.roundtrip`" wording
   (the padded composition has no single `Codec`; roundtrip is per-component + one
   split lemma).

The **plan is now precise and coherent**; the next session starts directly on
task 1.4 under the settled D7 shape (block `Run` ▸ tail `Codec` ▸ `iso` to `B64`/`B32`,
roundtrip = inherited per-component laws + one named split-uniqueness lemma).

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
base32/64 as a **composition** — the full-block `Run` + terminal-tail
`Codec`, `iso`-ed onto `B32`/`B64`; see the D7 correction) are **still open**.
That is the next unit of work.

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
     `Codec.encode b64TailElem` = `b64TailUnapply` `bind` `count 4 (satisfy b64OrPad)`);
     (ii) the uniqueness lemma: any `(blocks', t') ∈ decodeRepeat b64BlockElem … (concat sb st)`
     with `decodeFull b64TailElem t'.bytes ≠ none` has `blocks' = blocks`. The pad dichotomy
     (alphabet vs `=`) disambiguates the length-8 edge cases (2 blocks of 4 bytes vs a
     tail: `b64TailApply` rejects a 3-byte output, so a full-block prefix never decodes as
     a tail at the wrong boundary); (iii) a `List.head?`-of-`filterMap`-with-unique-hit
     lemma pinning the result. **D7 is now settled (this session's correction):**
     there is **no** single `Codec B64`, so do **not** try to "re-express as one
     value with only the inherited law"; the whole-input decoder is a **composition**
     (full-block `Run` = `decodeRepeat b64BlockElem`, then `decodeFull b64TailElem`,
     `iso`-ed to `B64`), and the roundtrip is the inherited per-component laws **plus
     one named, scoped composition lemma** (the block-run/tail split uniqueness) — see
     design §D7 and `specs/codec/spec.md`. The `head?`/`filterMap` form is replaced by
     the direct `Run.decodeFull`/`Codec.decodeFull` composition, **not** by an
     impossible single AST value.
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
