# Audit — `basen-radix` law surface: are the seven block ties law-bearing?

Scope: `/Users/user/_/lean-basen/BaseN/RadixTie.lean` (1172 lines, read in full),
`/Users/user/_/lean-codec/openspec/changes/basen-radix/{specs/basen/spec.md,tasks.md,design.md}`,
plus the gated universe in `lean-basen/Axioms.lean`.

Central claim attacked: _each of the seven per-base block isomorphisms is "tied to the
generic fold" by a theorem that actually constrains it._

**Verdict on the central claim: partially true, and the part that is false is the part
the spec makes mandatory.** Bases 2/4/8/10/16 (`_8`) carry real content and survive
mutation on both axes (finding P1). Bases 32/64 (`_L`) do **not** deliver a tie in the
direction that matters: their `→` is a conjunction whose second arm never mentions
`toNat`, and their `←` covers 1 of the 5 (resp. 3) block arities the `apply` accepts
(findings M2, M3). Separately the spec's _mandated_ "iff about the block's domain" for
bases 8/10 is **not proved anywhere** — only a one-directional sufficient condition
(M1), and the docstrings claim otherwise (M4).

---

## Summary counts

| severity                    | count | ids                |
| --------------------------- | ----- | ------------------ |
| MUST                        | 4     | M1, M2, M3, M4     |
| SHOULD                      | 5     | S1, S2, S3, S4, S5 |
| NITPICK                     | 5     | N1, N2, N3, N4, N5 |
| Refuted / could not confirm | 3     | R1, R2, R3         |

Questions yielding **nothing** (answered "no finding"): Q1's vacuity suspicion (the `_8`
`→` **is** non-vacuous — refuted, R1); Q4's suspicion that `*BlockIso_apply` "constrains
nothing" _in isolation_ is true but is a MUST because of what it was introduced to do
(M4-b/S3); Q6's "weakest theorem" is answered as M4.

---

## MUST

### M1 — The spec's mandatory "iff about the block's domain" is not stated, for either base 8 or base 10

**Severity: MUST.** The spec is imperative and this is the load-bearing half of the
requirement.

- Spec demand: `/Users/user/_/lean-codec/openspec/changes/basen-radix/specs/basen/spec.md:127-129`
  > "The rejection law SHALL state the **complete** characterisation, not merely a
  > sufficient condition: for bases 8 and 10 a block succeeds **exactly when** its value
  > is at most `255`, which makes the rejection law an iff about the block's domain
  > rather than one half of it."
- What exists: `BaseN/RadixTie.lean:514` and `:770`, both **one-directional**.

Evidence:

```
$ sed -n '512,516p' BaseN/RadixTie.lean
theorem octBlockApply_overflow (d0 d1 d2 : UInt8)
    (h : 255 < BaseN.Base8.octToVal d0.toNat * 64 + BaseN.Base8.octToVal d1.toNat * 8
      + BaseN.Base8.octToVal d2.toNat)
    (hv : BaseN.Base8.octValid d0.toNat = true) (hv2 : BaseN.Base8.octValid d1.toNat = true)
    (hv3 : BaseN.Base8.octValid d2.toNat = true) :
    BaseN.Base8.octBlockApply [d0, d1, d2] = none
```

That is `255 < value → apply = none`. The converse-of-success half — `apply ≠ none →
value ≤ 255` — is nowhere.

Greps run (whole repo, `.lean` only, excluding `Axioms.lean`/`scratch`):

```
$ grep -rn "octBlockApply\|digBlockApply" --include=*.lean . | grep -i "iff\|isSome\|↔"
./BaseN/Base8.lean:197:    octBlockApply cs = some b ↔ octBlockUnapply b = some cs := by
./BaseN/Base10.lean:187:   digBlockApply cs = some b ↔ digBlockUnapply b = some cs := by
./BaseN/RadixTie.lean:684: (docstring prose only)
```

Both hits are the **`Iso` law** (`apply/unapply` round-trip), not the domain claim. There
is no theorem in the tree whose type relates `octBlockApply`'s success to a value bound.

**The missing theorem is 6 lines and I proved it** (`/tmp/probe/p18.lean`):

```lean
theorem oct_domain_iff_derivable (d0 d1 d2 : UInt8)
    (h0 : BaseN.Base8.octValid d0.toNat = true) (h1 : …) (h2 : …) :
    (BaseN.Base8.octBlockApply [d0, d1, d2]).isSome = true
      ↔ BaseN.Base8.octToVal d0.toNat * 64 + BaseN.Base8.octToVal d1.toNat * 8
          + BaseN.Base8.octToVal d2.toNat ≤ 255 := by
  rw [BaseN.Base8.octBlockApply]; simp only [h0,h1,h2, Bool.and_self, ite_true]
  by_cases hle : … ≤ 255
  · rw [ite_eq_left hle]; simp [hle]
  · rw [ite_eq_right hle]; simp [hle]
#print axioms oct_domain_iff_derivable
```

Output of the probe:

```
'oct_domain_iff_derivable' depends on axioms: [propext]
'dig_domain_iff_derivable' depends on axioms: [propext]
```

Both `[propext]`-only — i.e. **cheaper than the gate's own `[propext, Quot.sound]` budget**.
The absence is not a difficulty, it is an omission.

**Fix:** add these two theorems to `RadixTie.lean` after their `_overflow` twins, name
them `octBlockApply_domain_iff` / `digBlockApply_domain_iff`, add both to `gatedNames`
and to the `#print axioms` block, bump `expectedPub` 722 → 724 / `expectedGated`
670 → 672 and the "universe, as measured" table in `Axioms.lean`.

---

### M2 — `b32BlockApply_of_toNat` / `b64BlockApply_of_toNat`: the second conjunct of the `∧` mentions `toNat` nowhere, so the conjunction is not a tie

**Severity: MUST.** These are presented as the `_L` ties; half of each is not.

- `BaseN/RadixTie.lean:1054-1079` (`b32…`), `:957-975` (`b64…`). Both are
  `toNat … = some (beVal bs) ∧ blockApply … = some bs` over the block's _own encoding
  vector_, with **no hypothesis at all** (they are closed `∀ b0 b1 …, P ∧ Q`).

The proof bodies are, verbatim:

```
  refine ⟨toNat_b64_unapply_three b0 b1 b2, ?_⟩
  exact (BaseN.Base64.b64BlockIso_law _ _).2 rfl
```

(`:971-975`; the b32 twin is `:1089-1092`.) So the right arm is `⟨existing content⟩ ∧
<Iso law at rfl>`: exactly the `⟨existing_bridge_lemma, rfl⟩` repackaging the question
asks about.

**Measured**: I re-derived the second arm as a standalone `example` whose type contains
no `toNat` at all, and it compiles (`/tmp/probe/p12.lean`):

```lean
example (b0 b1 b2 b3 b4 : UInt8) :
    BaseN.Base32.b32BlockApply
      [BaseN.Base32.toByte (BaseN.Base32.valToB32 (b0.toNat / 8)),
       … , BaseN.Base32.toByte (BaseN.Base32.valToB32 (b4.toNat % 32))] =
      some [b0, b1, b2, b3, b4] :=
  (BaseN.Base32.b32BlockIso_law _ _).2 rfl
```

```
$ nix develop --command lake env lean /tmp/probe/p12.lean
basen dev shell — lean (version        # no errors
```

**New content, precisely:** the left arm only — `toNat_b32_unapply_five` /
`toNat_b64_unapply_three` (`:886`, `:838`), which _do_ carry real work (eight/4 case
`rcases` on `b32ToVal` windows + `toNat_map_byteOfDigit` + `omega`). The `∧` wrapping
adds no proof obligation beyond conjunction introduction.

**Why `∧` is the wrong shape.** The docstring at `:832` claims the tie is

```
So the tie is **`toNat b cs = some (beVal bs) ↔ blockApply cs = some bs`**
```

— an `↔` between two functions at a _variable_ `cs`. The delivered statements have no
variable `cs` on the `→` side and the `←` side restricts to one arity (M3). The
docstring describes a theorem that was not written.

**Fix:** (a) delete the `∧` and ship the two arms as separate named theorems (matching
the `_8` schema's `_of_toNat` / `toNat_of_` pair), so no gated name advertises a
conjunction as a tie; (b) rewrite `:832` to describe what exists.

---

### M3 — `toNat_of_b32BlockApply_five` / `toNat_of_b64BlockApply_three` cover 1 of 5 (resp. 1 of 3) arities the block accepts — and the docstrings say the opposite

**Severity: MUST** (the coverage gap is real; the docstring at `:951-952` is _false_, not
merely narrow).

- `BaseN/RadixTie.lean:1080-1082`: `(h : b32BlockApply cs = some [b0,b1,b2,b3,b4])` — a
  hypothesis pinning the result to the **5-element** list only.
- `BaseN/RadixTie.lean:977-979`: same at **3** elements for b64.

`b32BlockApply`'s domain is `b32BlockDecodeLenient` gated by re-encode
(`BaseN/Base32.lean:415-419`) over the 1–5-byte shapes of `b32BlockUnapply`
(`BaseN/Base32.lean:216-228`). The 1-, 2-, 3- and 4-byte arms are _all accepted_.

**Measured** (`/tmp/probe/p13.lean`), b32:

```
[("MY======", some 1, none), ("MZXQ====", some 2, none), ("MZXW6===", some 3, none),
 ("MZXW6YQ=", some 4, none), ("MZXW6YTB", some 5, some 439956234849)]
     ^arity         ^block result        ^toNat
```

b64:

```
[("Zg==", some 1, none), ("Zm8=", some 2, none), ("Zm9v", some 3, some 6713199)]
```

So `toNat_of_*_five` / `_three` prove the `←` direction on **1 of 5** and **1 of 3**
accepted shapes. The other four / two are _not_ covered, and for those the fold returns
`none` while the block returns `some` — the tie genuinely does not hold there.

Is that narrowing spec-forbidden? **Partly.** The spec's arithmetic claim is at
`spec.md:127-129` (bases 8/10) and the arity rule at `spec.md:118-121`
("Both directions SHALL be stated at the block's own arity — its literal digit vector").
The `_L` blocks' "own arity" is _five/three for the full block but they also swallow
padded 1–4-byte values_, so the delivered statement picks the one arity where the
sentence "at the block's own arity" is trivially satisfiable. `RadixTie.lean:1077-1078`
concedes the narrowing as an "arity fact" — but note the contradiction: `b32BlockApply
["MY======"] = some [102]` **succeeds**, so the padded shape is _inside_ `apply`'s
domain and _outside_ the fold's alphabet. That is a **canonicity** divergence, not an
"arity" one — the same class D6's correction 1 names.

**The docstring at `:949-952` is a straight falsehood:**

```
So the two agree on every input the block accepts *canonically* — which, because
`b64BlockApply` re-encodes and compares, is every input it accepts at all
(`b64BlockIso_law`).
```

Measured counterexample:

```
$ nix develop --command lake env lean /tmp/probe/p19.lean
some [102]      -- BaseN.Base64.b64BlockApply "Zg=="
none            -- BaseN.Radix.toNat 64 "Zg=="
true            -- (toNat 64 "Zg==" == none)
```

`"Zg=="` **is** an input the block accepts at all, and the two functions do not agree on
it. Also the theorem is not `∀ cs`, so "every input" cannot be its content by
construction.

**Fix:** (a) strike "every input it accepts at all" at `:951-952`; (b) either state the
`←` direction over the block's full accepted domain (`∃ n, bs.length = n`, with the
padded shapes yielding a _different_ conclusion — e.g. `toNat` on the un-padded prefix), or
record the narrowing as an explicit `[Dn]` departure with a reason, since `spec.md:118`
says the statement is over the block's arity and the block's arity is 1–5.

---

### M4 — The seven `*BlockIso_apply` laws are `rfl` projections introduced solely to silence the def-coverage arm; the repo's own allowlist prose names this exact defect

**Severity: MUST** in the sense the question asks ("should these count as laws?" — **no**).

`BaseN/RadixTie.lean:1141-1161`, seven theorems of the form

```
theorem bitBlockIso_apply (cs : List UInt8) :
    BaseN.Base2.bitBlockIso.apply cs = BaseN.Base2.bitBlockApply cs := rfl
```

Each is `rfl` because `bitBlockIso` is _defined_ as `{ apply := bitBlockApply, … }`
(`BaseN/Base2.lean:401-403`), so the statement is "structure projection = the field it
was built from". It constrains nothing beyond definitional unfolding: a change to
`bitBlockApply` keeps it true (the projection moves with it), and a change to the
`Iso`'s `apply` field is precisely what would have to be made _not_ `bitBlockApply` —
which no one does, because `bitBlockIso` is one line.

**These exist to pass a gate, and the file says so:**
`BaseN/RadixTie.lean:1119-1128`

> "**Measured, it did not hold after §3.2 as first written**: the ties name
> `bitBlockApply`/…, not `bitBlockIso`/…, so the mention proxy still saw the seven as
> unmentioned and the def arm refused the removal. The fix is the one the task actually
> intends — make the theorems name the **value**."

That is a description of _fitting the measurement_, not of a law discovered. And the
repo's own allowlist prose already forbids this shape — `Axioms.lean:1963-1965` (in
`definitionSurfaceAllowlist`'s docstring, on `numeralIso`):

> "a theorem restating a proved field would be the `propProjections` defect wearing a
> `def` name."

`*BlockIso_apply` is that defect wearing a _`theorem`_ name: it restates a projection of a
structure whose `law` field is already proved at the definition site
(`law := bitBlockIso_law`, `Base2.lean:403`). The seven are gated and counted
(`Axioms.lean:2877-2895` `#print axioms`; `:3504-3561` in `gatedNames`), so they inflate
the public-theorem count (`expectedPub := 722`) by seven without adding one law.

**Fix (preferred):** revert the allowlist drop for the seven `*BlockIso` values and
restore them to `definitionSurfaceAllowlist` with the reason _"`Iso`-law-as-field; the ties
constrain the `apply` projection (`bitBlockApply`), which IS named by a gated theorem; the
`Iso` value itself needs no separate law"_ — that is a true reason, and the def arm
explicitly permits it (`Axioms.lean:1921-1924`). Delete the seven `_apply` theorems.
**Fix (alternative):** keep the theorems but state something with content, e.g.
`bitBlockIso.unapply (of some v) = …` or the composed `law`, so the name is not a
projection restatement. Do not leave seven `rfl`s in the gated set.

---

## SHOULD

### S1 — The _converse-of-the-tie_ overflow law is derivable in 3 lines and is not stated

`octBlockApply_overflow` (`:514`) is keyed on the raw value expression
`octToVal d0 * 64 + …`, not on the `n` that `toNat` returns. That means it is **not** the
converse of `octBlockApply_of_toNat` (`:476`), whose hypothesis is `toNat 8 [...] = some n
∧ n ≤ 255`. The pairing a reader wants is:

```
toNat 8 [d0,d1,d2] = some n → 255 < n → octBlockApply [d0,d1,d2] = none
```

I proved it composes from what is already there (`/tmp/probe/p17.lean`, compiles clean):

```lean
example (d0 d1 d2 : UInt8) (n : Nat)
    (h : BaseN.Radix.toNat 8 [d0,d1,d2] = some n) (hn : 255 < n) :
    BaseN.Base8.octBlockApply [d0, d1, d2] = none := by
  … exact octBlockApply_overflow d0 d1 d2 (by rw [hval, natVal_three] at hn; omega) hv0 hv1 hv2
```

So the overflow law as stated forces the reader to redo the `toNat_three` bridge to connect
it to the agreement theorem it is supposed to complement. **Fix:** add
`octBlockApply_of_toNat_overflow` / `digBlockApply_of_toNat_overflow` in `n`-form, or
restate `_overflow` in `n`-form. Same for base 10 (`:770`).

### S2 — `octBlockApply_overflow`'s docstring claims the iff ("**exactly**") that M1 shows is unproved

`BaseN/RadixTie.lean:504-511`:

> "`octBlockApply` succeeds **exactly** when its value is at most `255` (verified over
> all 512 digit triples), so this is a complete statement about the rejection rather than
> one half of it."

The theorem is one-directional (M1). "Verified over all 512 digit triples" is an `#eval`
(`scratch/probe_dig.lean:5-13` — a `#eval` fold, not a `decide` theorem, and `scratch/` is
outside `lean_lib basen` per `lakefile.lean:26-27 roots := #[`BaseN]`), so it is evidence,
not proof. Same overclaim at `:684-686`(base 10 section header),`:765-768`
(`digBlockApply_overflow`docstring: "complete characterisation … succeeds **exactly
when**"), and`tasks.md:657-660`, `design.md:307-312`. **Fix:** either add the `↔` (M1) or
change "exactly"/"complete" to "sufficient condition, converse not stated".

### S3 — The def-coverage arm's mention proxy is satisfied vacuously by `*BlockIso_apply`, and that vacuity is _documented_ but the documentation is now load-bearing in the wrong direction

`Axioms.lean:3899-3900` (correctly honest):

> "Its property is the narrow one it can have: _no public definition is covered by
> silence._ It can be satisfied vacuously, and it is **not** a soundness claim."

Measured: `mentionedByGated` (`Axioms.lean:1914-1921`) takes `type.getUsedConstants` of
gated theorems. `bitBlockIso_apply`'s _type_ mentions `bitBlockIso`, so the def arm sees
it "mentioned" — but the type says nothing about the `Iso` beyond the projection. To
satisfy this vacuously **without** a bogus theorem one could write `example : bitBlockIso =
bitBlockIso := rfl` — except `example` is not a public theorem and would not be seen, so
the cheapest vacuous satisfier _is_ exactly what S/M4 describes. Documented-as-vacuously-
satisfiable is acceptable per the brief; **coupling it to a law that then enters
`gatedNames`** is not, because it converts "the proxy can be gamed" into "the gate was
actually gamed". Covered by M4's fix.

### S4 — `beVal_eq_natVal`, `beVal_two`, `valAt`/`toNat_eq_natVal_map` are orphans

Measured (external + internal use, excluding declarations/docstrings):

```
$ grep -n "beVal_eq_natVal\|natVal_two\|natVal_four\|beVal_two\|valAt\b\|toNat_eq_natVal_map" BaseN/RadixTie.lean
 65: def valAt …
 69: theorem toNat_eq_natVal_map …
 71:   … valAt b ds vs …            <- only mentioning itself
102: theorem natVal_two …
109: theorem natVal_four …
133/378/650: uses of natVal_two/four
868: theorem beVal_eq_natVal …
873: theorem beVal_two …
```

- `toNat_eq_natVal_map` (`:69`): **zero consumers** anywhere (grep over all `.lean` excl.
  `Axioms.lean`/`scratch`/`.lake`). It is the module's headline "reusable core of every
  `_8` tie" — and the ties do not use it; they use `toNat_two`/`_three`/`_four`/`_eight`
  instead.
- `valAt` (`:65`): only mentioned by the orphan above.
- `beVal_eq_natVal` (`:868`): **zero consumers**. `beVal_foldl_eq` is used only to prove
  it.
- `beVal_two` (`:873`): **zero consumers** (only `beVal_three`, `beVal_five` are used).

The docstring at `:69-75` presents `toNat_eq_natVal_map` as the shared foundation; the
five per-base ties each re-derive the same thing at fixed width. **Fix:** delete the four
orphans, or route the per-base proofs through `toNat_eq_natVal_map` as the docstring
claims. As shipped, the docstring at `:57-63` ("The reusable core of every `_8` tie") is
false of the code.

### S5 — Two theorems named `rejects_overflow` for one law family, in the same package, unremarked

`BaseN/Base8.lean:586` and `BaseN/Base10.lean:564` are both `decodeFull … = none` on the
canonical overflow vector, while `BaseN/RadixTie.lean:514`/`:770` are the _block-level_
overflow rejections. So each base has **two** "the overflow is rejected" theorems at two
layers. Not a duplicate (different statements, different functions — verified at
`Base8.lean:586-594` vs `:514`), but nothing in either docstring says which is the law of
record, and the `Bench.lean:600,604` references point at the _whole-input_ ones while the
spec's requirement is about the _block_. **Fix:** one sentence in `_overflow`'s docstring
naming `Base8.rejects_overflow` as the whole-input lift of the same fact (or vice versa).

---

## NITPICK

### N1 — `b32BlockApply_of_toNat`'s docstring says "the strong form of the paper's law, as for bases 2, 4 and 16"

`RadixTie.lean:1047` — but bases 2/4/16 have a _hypothesis-driven_ law
(`toNat … = some n → blockApply … = some …`) while `b32…` has no hypothesis and a _closed
conjunction_. They are not the same form. Comment only.

### N2 — `RadixTie.lean:1077-1078` calls the padding restriction "an arity fact, not a canonicity guard"

Measured (`/tmp/probe/p13.lean`): `b32BlockApply ["MY======"] = some [102]` — the padded
shape is _accepted_, so it is inside the block's arity, not outside it. The divergence is
that `=` is outside the **fold's alphabet** — a canonicity difference. Same wording at
`:973-975` (b64). This is the exact D6-correction-1 confusion the module header
(`:47-58`) says it exists to fix.

### N3 — `natVal_three`/`natVal_four`/`natVal_eight` shadow a generic `natVal` and are proven by `simp; omega`, but `natVal_two` needs no `omega`

Cosmetic: `:102-104` ends `by simp [natVal]` while the 3/4/8 variants need an extra
`omega`. Not a defect; noted because the asymmetry suggests `natVal_two` could have been
`rfl`-adjacent, and a reader will look for the difference.

### N4 — `radixInstances` (`:1099`) and `radixInstances_radices` (`:1113`) are `rfl` restatements of a literal

`radixInstances_radices : radixInstances = [2,4,8,10,16,32,64] := rfl` is true _by
definition_ of `radixInstances` — it cannot fail, so it constrains nothing. Its sibling
`radixInstances_length` (`:1110`, `= 7 := rfl`) is the same. This is the `propProjections`
shape in miniature (though harmless, and neither is in the "law" claim under audit).

### N5 — `numeralIsoAt` (`:1125`) has zero consumers

Same grep as S4: no `numeralIsoAt` outside `RadixTie.lean` and `Axioms.lean`'s allowlist.
It is allowlisted (`Axioms.lean:1970` region) as "the same value, read from the single
radix enumeration", i.e. dead-but-justified. Flagged because S4 shows the module has a
pattern of shipping `def`/`theorem` with no consumer and a docstring that implies one.

---

## Refuted / could not confirm

### R1 — **Refuted**: "the `_8` `→` directions are vacuous" (question 1)

They are not. I mutated the digit order in two independent places and the residue fails in
both.

**The trace (question 1's ask).** After the guard discharge, the residue of
`bitBlockApply_of_toNat` is exactly
`bitsVal (bitVal d0) (bitVal d1) … (bitVal d7) = natVal 2 [bitVal d0, …, bitVal d7]`.
Proven standalone, with no `toNat` and no block (`/tmp/probe/p20.lean`, compiles):

```lean
example (v0 v1 v2 v3 v4 v5 v6 v7 : Nat) :
    BaseN.Base2.bitsVal v0 v1 v2 v3 v4 v5 v6 v7
      = BaseN.Radix.natVal 2 [v0, v1, v2, v3, v4, v5, v6, v7] := by
  unfold BaseN.Base2.bitsVal; rw [natVal_eight]; omega
```

**Nothing is established that would fail if `blockApply` and `toNat` disagreed on digit
order — because they are _forced_ to agree on order by the shared `digitVal`, and the
theorem's entire content is the two sums being the same sum.** But the sentence "would
fail" is the operative test, and the answer is **yes, it would fail**:

_(a) perturb the block's order._ Swap `bitVal d0`/`bitVal d1` in `bitBlockApply`
(`/tmp/probe/Base2.mut.lean`), and:

```
$ nix develop --command lake env lean /tmp/probe/p2.lean
some 64     -- mutated apply  [49,48,48,48,48,48,48,48]
some 128    -- original apply [49,48,48,48,48,48,48,48]
some 128    -- toNat          [49,48,48,48,48,48,48,48]
```

and the statement-level refutation compiles (`/tmp/probe/p3.lean`):

```lean
theorem mut_breaks :
    ¬ (∀ (n : Nat), BaseN.Radix.toNat 2 [49,48,48,48,48,48,48,48] = some n →
        (some (UInt8.ofNat (bitsValMut (bitVal 49) (bitVal 48) 0 0 0 0 0 0)) : Option UInt8)
          = some (UInt8.ofNat n)) := by
  intro h; have := h 128 rfl; simp [bitsValMut, BaseN.Base2.bitVal] at this
```

_(b) perturb the fold's weights._ The residue becomes `bitsVal … = natVal' …`, false at
`v0=1, v1=0` (`/tmp/probe/p5.lean`: `¬ bitsVal 0 1 0… = natVal 2 [1,0,0,…]` — proven by
`decide`). So a wrong-order `toNat` also breaks the theorem.

**Non-vacuity of the hypotheses.** Inhabited, `decide`d (`/tmp/probe/p21.lean`):

```
bitBlockApply [48,49,48,49,48,49,48,49] = some 85   -- so `→`'s h is inhabited
toNat 2         [48,49,48,49,48,49,48,49] = some 85
octBlockApply [48,48,48] = some 0 ; digBlockApply [50,53,53] = some 255
```

And `n ≤ 255` for base 8 is **not** vacuous on the other side: `toNat 8 "777" = some 511`,
`octBlockApply "777" = none` (`/tmp/probe/p15.lean`), so the hypothesis excludes real
inputs. **The `_8` `→` laws are law-bearing.** Question 1 yields no defect.

### R2 — **Could not confirm**: that `toNat_of_b32BlockApply_five`'s narrowing violates the _letter_ of the spec

`spec.md:118-121` says "stated at the block's own arity — its literal digit vector". A
5-byte b32 result _is_ the block's literal full-block vector, so the delivered statement is
arguably compliant; the gap (M3) is that "the block's arity" is ambiguous for a block that
also accepts padded 1–4-byte values. The _docstring_ falsehood (M3) is confirmed; the
spec-violation reading is a judgement and I mark it **UNVERIFIED as a spec breach** —
recommend the owner rule on it rather than a unilateral "MUST fix the statement". M3's
docstring fix is unconditional.

### R3 — **Could not confirm**: any pre-existing theorem, in either repo, stating the

`_L` `↔` that `RadixTie.lean:832` advertises

Grepped `lean-codec` and `lean-basen` for a theorem typed
`toNat b cs = some (beVal bs) ↔ blockApply cs = some bs`. The nearest is
`b32BlockIso_law` (`Base32.lean:653`, `b32BlockApply cs = some bs ↔ b32BlockUnapply bs =
some cs`) — an `Iso` law over `apply/unapply`, **not** over `toNat`. So `:832`'s claim
describes a theorem that exists nowhere. Recorded under M2; listed here because I could
not rule out a `scratch/` draft, and `scratch/` is outside `lean_lib basen`.

---

## Appendix — the `sorry` / `native_decide` posture (question D), measured

```
$ grep -rn "\bsorry\b" --include=*.lean BaseN/ BaseN.lean
BaseN/Base64.lean:15:`< 256`.  `[propext, Quot.sound]`-only, zero `sorry`.
BaseN/Base32.lean:13:`< 256`.  `[propext, Quot.sound]`-only, zero `sorry`.
BaseN/Base32.lean:3655:`[propext, Quot.sound]`-only, zero `sorry`:
```

Three hits, **all in docstrings** — no `sorry` term. Enforcement is real, not observed:
`lakefile.lean:36` and `:50` set `moreLeanArgs := #["-DwarningAsError=true"]` on both
`lean_lib basen` and `lean_lib Axioms`, so a `sorry` is a build error.

```
$ grep -rn "native_decide" --include=*.lean BaseN/ BaseN.lean
(no output, exit 1)
$ grep -rln "native_decide" --include=*.lean .
./Axioms.lean
./.git/mutation-backup-Axioms.lean
./Bench.lean
./.lake/packages/codec/Axioms.lean
```

`native_decide` reaches **no library module** in `BaseN/`. Its two legitimate homes:
`Bench.lean` (bench lane, a _package_ not a `checks` entry — `AGENTS.md`), and
`Axioms.lean` where lines `:3954-4028` are the gate's own **counter** that measures
`Bench.lean`'s `native_decide` count and asserts it (`nativeDecideCount`,
`throwError m!"… stated {stated} … uses but the source has {tacticLines}"`). The
`.git/mutation-backup-Axioms.lean` and `.lake/packages/codec/Axioms.lean` hits are a
backup file (gitignored/untracked by intent) and the dependency's own gate. **Confirmed.**

Axiom footprints I re-measured for the audited laws (`/tmp/probe/p1.lean`):

```
'BaseN.RadixTie.b64BlockApply_of_toNat'   depends on axioms: [propext, Quot.sound]
'BaseN.RadixTie.octBlockApply_overflow'   depends on axioms: [propext, Quot.sound]
'BaseN.RadixTie.digBlockApply_overflow'   depends on axioms: [propext, Quot.sound]
'BaseN.RadixTie.bitBlockIso_apply'        depends on axioms: [propext, Quot.sound]
'BaseN.RadixTie.toNat_of_b32BlockApply_five' depends on axioms: [propext, Quot.sound]
```

Inside budget. (Note: `*BlockIso_apply` costing `Quot.sound` at all is a small curiosity
for a `:= rfl` proof; not pursued.)

---

## Answer to Q6 — the single weakest theorem

`bitBlockIso_apply` (`RadixTie.lean:1141`) — and its six twins. It is `:= rfl` on a
structure projection (`bitBlockIso` is `{ apply := bitBlockApply, … }`,
`Base2.lean:401-403`), i.e. the statement "the field is the field". It cannot fail for any
edit to `bitBlockApply`, it is not consumed by any other lemma (grep: no callers outside
`Axioms.lean`), and the module records at `:1119-1128` that it was written **because the
def-coverage arm refused the allowlist drop** — a gate-satisfying theorem, not a law. The
repo's own allowlist docstring (`Axioms.lean:1963-1965`) names this shape as the
`propProjections` defect. Its existence also raises `expectedPub` 722 by seven, so it is
seven "laws" that make the theorem count look better while the law surface is unchanged.
