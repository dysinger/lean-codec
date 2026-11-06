/- Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later -/

import Codec.Packed
import Codec.Sound

/-!
# The deterministic single-result decoder (gated)

`decodeArray` (the packed decoder, `Codec.Packed`) returns **all** `(value,
consumed count)` pairs a description admits — the full backtracking union. This
file adds `decodeOne`, a *committed* decoder that returns a single result: the
`alt` case commits to the first non-`none` branch (`orElse`), and the `seq` case
commits to the *first* `d₁` result (a `bind`, not a `flatMap` over all of them).

## The gating contract

`decodeOne` commits `|` to one branch and `*` to the first left result, so it is
equal to the backtracking `decodeArray` only when the description is
unambiguous/functional — i.e. when `decodeArray d a i` has at most one result. It is
therefore *never* presented as **equal** to `decodeArray` without that hypothesis.
**Soundness is unconditional**: `decodeOne_mem` (fact 1 below) has no hypothesis and
`[propext, Quot.sound]`-only, so a committed choice never fabricates a result; what
the hypothesis buys is *completeness*. (An earlier revision read "sound only when",
which contradicts `decodeOne_mem` seven lines later.) The facts proved mirror the
`decodeFull_spec` template (`Codec.Decode`):

1. **Unconditional soundness** — `decodeOne_mem`: every result `decodeOne`
   returns is a genuine backtracking result (`(x, c) ∈ decodeArray d a i`), so a
   committed choice never *fabricates* a result. (Note `decodeOne` may return
   `none` even when `decodeArray` has a result — e.g. the first `d₁` result is a
   dead end for `seq` — which is exactly why completeness needs a gate.)

2. **Two conditional facts** — under `Functional d` (one value determines one
   count), `decodeArray_functional_count` pins the consumed count *given the same
   value*; under `Unambiguous d`, `decodeArray_unambiguous_value` pins the value
   *given the same count*. Each takes the other's conclusion as a hypothesis, and
   neither is a route to `decodeOne`'s completeness — they advertise no role they do
   not fill (the "hypothesis that makes `decodeOne` complete" framing is gone).

**Those two halves do NOT compose into "at most one result", and an earlier
revision of this header said they did.** Measured counterexample: take a
hypothetical `d` with `Rel d x "ab"` and `Rel d y "a"`. `Unambiguous d` holds
vacuously (it only compares *equal-length* strings) and `Functional d` holds (each
value sits at exactly one string), yet `decodeArray` yields **two** results,
`(x, 2)` and `(y, 1)`. `decodeArray_functional_count` takes `x₁ = x₂` as a
hypothesis and `decodeArray_unambiguous_value` takes `c₁ = c₂`, so each consumes the
other's conclusion across the count gap that this example inhabits.

The statement that is actually true — and is now proved, not promised — needs a
**third** hypothesis: `RelAligned (Rel d)`, i.e. that values are identified by
their shared byte prefix across lengths. That is exactly what the counterexample
violates (`y`'s `"a"` is a prefix of `x`'s `"ab"` but `y ≠ x`).

3. **Composed uniqueness** — `decodeArray_unique` (below): under `Functional d`
   **and** `RelAligned (Rel d)`, `decodeArray d a i` has at most one result. The
   proof aligns the two consumed prefixes (`prepend_prefix_agree`, a `Suffix`-level
   `splice_prefix_agree`), uses `RelAligned` to identify the values, and then
   `Functional` to identify the counts. `[propext, Quot.sound]`-only.
   `decodeArray_unique_byte` is the instance at `Codec.byte`, discharging both
   hypotheses with `functional_byte`/`relAligned_byte`, so the law is
   demonstrably non-vacuous.

**What is still not proved, stated rather than implied.** The committed decoder's
*completeness* — that `decodeOne d a i` succeeds whenever `decodeArray d a i` is
non-empty, hence `decodeOne` *equals* the unique result — is **not** proved here.
`decodeOne_mem` gives soundness unconditionally; the composition above gives the
uniqueness half the gate needs. The remaining step is the `seq` commitment (the
first `d₁` result may be a dead end), which is exactly the case the gating contract
is about and which is recorded as open rather than advertised as done.

The unconditional `decode (d₁ | d₂) s = decode d₁ s ++ decode d₂ s` law is **not
touched** — `decode`/`decodeArray` remain the full backtracking union; `decodeOne`
is a *distinct* surface, gated as above. This is not a new interpreter: `decodeOne`
reads `a[i]` and threads the same `Nat` cursor / `Array` carrier as `decodeArray`,
only its result is `Option (α × Nat)` instead of `List (α × Nat)`.
-/

namespace Codec

/--
The committed single-result decoder: like `decodeArray`, but `alt` returns the
first non-`none` branch (`orElse`) instead of the union, and `seq`/`iso` thread a
single `Option` (the first `d₁` result, not all of them). `[propext,
Quot.sound]`-clean (same `a[i]` reads and `Nat` cursor as `decodeArray`). -/
def decodeOne {α : Type} (d : Codec α) (a : Array UInt8) (i : Nat) : Option (α × Nat) :=
  match d with
  | Codec.iso j d =>
      (decodeOne d a i).bind fun (x, c) => (j.apply x).map fun y => (y, c)
  | Codec.seq d₁ d₂ =>
      (decodeOne d₁ a i).bind fun (x, c₁) =>
        (decodeOne d₂ a c₁).map fun (y, c₂) => ((x, y), c₂)
  | Codec.alt d₁ d₂ =>
      (decodeOne d₁ a i).orElse fun _ => decodeOne d₂ a i
  | Codec.empty => none
  | Codec.pure x => some (x, i)
  | Codec.byte =>
      if h : i < a.size then
        some (a[i], i + 1)
      else
        none
  | Codec.satisfy p =>
      if h : i < a.size then
        let b := a[i]
        if p b then some (b, i + 1) else none
      else
        none

/-- **Unconditional soundness** of the committed decoder: every result it returns
is a genuine backtracking result of `decodeArray`. The `seq` case is why this is
only soundness, not completeness: `decodeOne` commits to the *first* `d₁` result,
so a dead-end first branch yields `none` even when a later `d₁` result would
succeed; the result it *does* return is always real. `[propext, Quot.sound]`-only. -/
theorem decodeOne_mem {α : Type} (d : Codec α) (a : Array UInt8) (i c : Nat) (x : α) :
    decodeOne d a i = some (x, c) → (x, c) ∈ decodeArray d a i := by
  induction d generalizing a i c with
  | iso j d ih =>
      intro h
      simp only [decodeOne, decodeArray, Option.bind, Option.map] at h ⊢
      rw [List.mem_filterMap]
      cases h₁ : decodeOne d a i with
      | none => simp [h₁] at h
      | some pr =>
          rcases pr with ⟨x₀, c₀⟩
          simp [h₁] at h
          cases h₂ : j.apply x₀ with
          | none => simp [h₂] at h
          | some y =>
              simp [h₂] at h
              rcases h with ⟨hx, hc⟩
              subst x c
              refine ⟨(x₀, c₀), ih a i c₀ x₀ h₁, ?_⟩
              simp [h₂]
  | seq d₁ d₂ ih₁ ih₂ =>
      intro h
      simp only [decodeOne, decodeArray, Option.bind, Option.map] at h ⊢
      rw [List.mem_flatMap]
      cases h₁ : decodeOne d₁ a i with
      | none => simp [h₁] at h
      | some pr₁ =>
          rcases pr₁ with ⟨x₁, c₁⟩
          simp [h₁] at h
          cases h₂ : decodeOne d₂ a c₁ with
          | none => simp [h₂] at h
          | some pr₂ =>
              rcases pr₂ with ⟨y, c₂⟩
              simp [h₂] at h
              rcases h with ⟨hx, hc⟩
              subst x c
              refine ⟨(x₁, c₁), ih₁ a i c₁ x₁ h₁, ?_⟩
              rw [List.mem_flatMap]
              refine ⟨(y, c₂), ih₂ a c₁ c₂ y h₂, ?_⟩
              simp
  | alt d₁ d₂ ih₁ ih₂ =>
      intro h
      simp only [decodeOne, decodeArray, Option.orElse] at h ⊢
      rw [List.mem_append]
      cases ho : decodeOne d₁ a i with
      | none =>
          simp only [ho] at h
          right
          exact ih₂ a i c x h
      | some pr₁ =>
          rcases pr₁ with ⟨x₁, c₁⟩
          simp only [ho] at h
          injection h with hpr
          cases hpr
          left
          exact ih₁ a i c x ho
  | empty =>
      intro h
      simp only [decodeOne, decodeArray] at h ⊢
      cases h
  | pure x₀ =>
      intro h
      simp only [decodeOne, decodeArray] at h ⊢
      simp at h
      rcases h with ⟨hx, hc⟩
      subst x c
      simp
  | byte =>
      intro h
      simp only [decodeOne, decodeArray] at h ⊢
      by_cases hlt : i < a.size
      · simp [hlt] at h
        rcases h with ⟨hx, hc⟩
        subst x c
        simp [hlt]
      · simp [hlt] at h
  | satisfy p =>
      intro h
      simp only [decodeOne, decodeArray] at h ⊢
      by_cases hlt : i < a.size
      · simp [hlt] at h
        by_cases hp : p a[i]
        · simp [hp] at h
          rcases h with ⟨hx, hc⟩
          subst x c
          simp [hlt, hp]
        · simp [hp] at h
      · simp [hlt] at h

/-- **The `decodeArray`-level mirror of `Functional`, at `Codec.byte`.** Two
`decodeArray byte a i` results that agree on the **value** agree on the count.

**What this is, and what it is not.** It is *not* an instance of the `Functional`
definition (`Codec.Sound.Functional`), and it must not be read as one:
`Functional d` is `∀ x s₁ s₂, Rel d x s₁ → Rel d x s₂ → (⟨n₁, s₁⟩ = ⟨n₂, s₂⟩)`, a
statement about the **step relation** at *variable* length with a *fixed* value.
The theorem below is the **mirror shape**: it fixes the value `x₁ = x₂` and
compares the **consumed counts** of two packed results — quantifier order and the
object compared are both different, which is why it cannot discharge a `Functional`
hypothesis anywhere. The actual `Functional Codec.byte` instance is
`Codec.Sound.functional_byte`; this one is the packed-side companion the committed
decoder gates on.

Proof shape: mirror `decodeOne_mem`'s `byte` case, so the `if`-guard reaches the
`decodeArray` membership. Axiom-free. -/
theorem decodeArray_functional_byte (a : Array UInt8) (i : Nat) :
    ∀ {x₁ x₂ : UInt8} {c₁ c₂ : Nat},
      (x₁, c₁) ∈ decodeArray Codec.byte a i →
      (x₂, c₂) ∈ decodeArray Codec.byte a i → x₁ = x₂ → c₁ = c₂ := by
  intro x₁ x₂ c₁ c₂ h₁ h₂ hx
  subst hx
  simp only [decodeArray] at h₁ h₂
  by_cases hlt : i < a.size
  · simp [hlt] at h₁ h₂
    rw [h₁.2, h₂.2]
  · simp [hlt] at h₁

/-- The same-value/same-count mirror of `decodeArray_functional_byte` for the
unambiguity half: two `decodeArray byte a i` results that agree on the **count**
agree on the value. Like its companion this is the **mirror shape**, not
`Unambiguous Codec.byte` — that instance is `Codec.Sound.unambiguous_byte`, which
compares two `Rel` steps at one length. Axiom-free. -/
theorem decodeArray_unambiguous_byte (a : Array UInt8) (i : Nat) :
    ∀ {x₁ x₂ : UInt8} {c : Nat},
      (x₁, c) ∈ decodeArray Codec.byte a i →
      (x₂, c) ∈ decodeArray Codec.byte a i → x₁ = x₂ := by
  intro x₁ x₂ c h₁ h₂
  simp only [decodeArray] at h₁ h₂
  by_cases hlt : i < a.size
  · simp [hlt] at h₁ h₂
    rw [h₁.1, h₂.1]
  · simp [hlt] at h₁

/-- Under `Functional d`, one value determines one consumed count: two `decodeArray`
results for the *same* value must consume the same count.

**What this establishes, and what it does not.** This is a *conditional* fact about
one value: given `x₁ = x₂`, the counts agree. It is **not** a route to
`decodeOne`'s completeness. The pair `decodeArray_functional_count` +
`decodeArray_unambiguous_value` was once presented as "the hypothesis that makes the
committed `decodeOne` complete"; it is not, because each lemma consumes the other's
conclusion as a hypothesis (`x₁ = x₂` here, `c₁ = c₂` there) and the gap between
them — two results with *different* values and *different* counts — is inhabited
(the module header's `Rel d x "ab"` / `Rel d y "a"` example).

The composition that does close is `decodeArray_unique` (below), which needs
`RelAligned (Rel d)` as well and uses neither of these two lemmas. Completeness of
`decodeOne` itself remains **open** (`decodeOne_mem` gives soundness only); see the
module header. `[propext, Quot.sound]`-only. -/
theorem decodeArray_functional_count {α : Type} (d : Codec α) (hd : Functional d)
    (a : Array UInt8) (i : Nat) :
    ∀ {x₁ x₂ : α} {c₁ c₂ : Nat},
      (x₁, c₁) ∈ decodeArray d a i → (x₂, c₂) ∈ decodeArray d a i → x₁ = x₂ → c₁ = c₂ := by
  intro x₁ x₂ c₁ c₂ h₁ h₂ hx
  subst hx
  rw [decodeArray_eq d a i] at h₁ h₂
  rw [List.mem_map] at h₁ h₂
  rcases h₁ with ⟨p₁, hp₁, hp₁'⟩
  rcases h₂ with ⟨p₂, hp₂, hp₂'⟩
  rcases p₁ with ⟨x₁', t₁⟩
  rcases p₂ with ⟨x₂', t₂⟩
  have hp₁'' : (x₁', consumedAbs a i t₁) = (x₁, c₁) := by simpa using hp₁'
  have hp₂'' : (x₂', consumedAbs a i t₂) = (x₁, c₂) := by simpa using hp₂'
  have hx₁' : x₁' = x₁ := congrArg Prod.fst hp₁''
  have hx₂' : x₂' = x₁ := congrArg Prod.fst hp₂''
  have hc₁ : consumedAbs a i t₁ = c₁ := congrArg Prod.snd hp₁''
  have hc₂ : consumedAbs a i t₂ = c₂ := congrArg Prod.snd hp₂''
  -- `decode_spec` rebuilds the genuine consumed prefixes `s₀₁`/`s₀₂` with
  -- `Rel d x₁ s₀₁` and `Rel d x₁ s₀₂`; `Functional d` pins those prefixes equal
  -- (as length-indexed byte strings), hence `t₁.remaining = t₂.remaining` and
  -- therefore the consumed counts agree.
  have hs₁ := (decode_spec d x₁' (bdrop i (arrayToBytes a)) t₁).1 hp₁
  have hs₂ := (decode_spec d x₂' (bdrop i (arrayToBytes a)) t₂).1 hp₂
  rw [hx₁'] at hs₁
  rw [hx₂'] at hs₂
  rcases hs₁ with ⟨s₀₁, hpre₁, hrel₁⟩
  rcases hs₂ with ⟨s₀₂, hpre₂, hrel₂⟩
  have hpre12 : (⟨(a.size - i) - t₁.remaining, s₀₁⟩ : Sigma fun m => Bytes m) =
      ⟨(a.size - i) - t₂.remaining, s₀₂⟩ :=
    hd x₁ s₀₁ s₀₂ hrel₁ hrel₂
  have hrem : t₁.remaining = t₂.remaining := by
    have hlen := (Sigma.mk.inj hpre12).1
    have ht₁ : t₁.remaining ≤ a.size - i := t₁.hle
    have ht₂ : t₂.remaining ≤ a.size - i := t₂.hle
    omega
  -- consumedAbs a i t = i + ((a.size - i) - t.remaining); equal remaining ⇒ equal count.
  rw [← hc₁, ← hc₂]
  unfold consumedAbs
  rw [hrem]

/-- Under `Unambiguous d`, two `decodeArray` results that consume the **same** count
agree on the value.

**What this establishes, and what it does not.** Like its twin, this is a
*conditional* fact: given `c₁ = c₂`, the values agree. It is **not** half of a proof
that `decodeOne` is complete — `decodeArray_functional_count` needs this lemma's
conclusion as its hypothesis and vice versa, and neither says anything about a pair
of results that differ in *both* value and count. The composed law that closes the
question is `decodeArray_unique` (below) under `Functional ∧ RelAligned`, which
proves the result directly and uses neither lemma. `decodeOne`'s completeness is
**open** (module header).

The forward bridge: `(x₁, c) ∈ decodeArray d a i` transports (via `decodeArray_eq` +
`decode_spec`) to `Rel d x₁ s₀₁` for a genuine consumed prefix `s₀₁`; the *same* count
`c` pins both `consumedAbs a i t₁ = c = consumedAbs a i t₂`, hence `t₁.remaining =
t₂.remaining`, and the genuine-suffix invariant (`decode_genuine_suffix_pointwise`,
read pointwise at one index and closed by `omega`) then pins the remainders `t₁ = t₂`
(via `Suffix.ext`). Once `t₁ = t₂`, `t.prepend s₀₁ = t.prepend s₀₂`
forces the prefixes `s₀₁ = s₀₂` (`prepend_prefix_eq`), and `Unambiguous d` forces
`x₁ = x₂`. `[propext, Quot.sound]`-only, zero `sorry`, zero `Classical.choice`. -/
theorem decodeArray_unambiguous_value {α : Type} (d : Codec α) (hd : Unambiguous d)
    (a : Array UInt8) (i : Nat) :
    ∀ {x₁ x₂ : α} {c : Nat},
      (x₁, c) ∈ decodeArray d a i → (x₂, c) ∈ decodeArray d a i → x₁ = x₂ := by
  intro x₁ x₂ c hmem₁ hmem₂
  rw [decodeArray_eq d a i] at hmem₁ hmem₂
  rw [List.mem_map] at hmem₁ hmem₂
  rcases hmem₁ with ⟨p₁, hp₁, hp₁'⟩
  rcases hmem₂ with ⟨p₂, hp₂, hp₂'⟩
  rcases p₁ with ⟨x₁', t₁⟩
  rcases p₂ with ⟨x₂', t₂⟩
  have hp₁'' : (x₁', consumedAbs a i t₁) = (x₁, c) := by simpa using hp₁'
  have hp₂'' : (x₂', consumedAbs a i t₂) = (x₂, c) := by simpa using hp₂'
  have hx₁' : x₁' = x₁ := congrArg Prod.fst hp₁''
  have hx₂' : x₂' = x₂ := congrArg Prod.fst hp₂''
  have hc₁ : consumedAbs a i t₁ = c := congrArg Prod.snd hp₁''
  have hc₂ : consumedAbs a i t₂ = c := congrArg Prod.snd hp₂''
  -- same consumed count ⇒ same remaining length
  have hrem : t₁.remaining = t₂.remaining := by
    have hcons : consumedAbs a i t₁ = consumedAbs a i t₂ := by rw [hc₁, hc₂]
    unfold consumedAbs at hcons
    have ht₁ : t₁.remaining ≤ a.size - i := t₁.hle
    have ht₂ : t₂.remaining ≤ a.size - i := t₂.hle
    omega
  -- the genuine-suffix invariant pins the remainders equal: t₁ = t₂
  have hbytes : cast (congrArg Bytes hrem) t₁.bytes = t₂.bytes := by
    apply Bytes.ext
    intro j
    have hg₁ := decode_genuine_suffix_pointwise d (bdrop i (arrayToBytes a)) x₁' t₁ hp₁ ⟨j.val, by omega⟩
    have hg₂ := decode_genuine_suffix_pointwise d (bdrop i (arrayToBytes a)) x₂' t₂ hp₂ j
    have hc : t₁.consumed = t₂.consumed := by
      unfold Suffix.consumed
      rw [hrem]
    rw [cast_bytes_val' (e := hrem) t₁.bytes j]
    rw [hg₁, hg₂]
    unfold bdrop
    congr 1
    apply Fin.ext
    dsimp
    omega
  have ht : t₁ = t₂ := Suffix.ext hrem hbytes
  -- decode_spec: each result carries a genuine consumed prefix with Rel
  rcases (decode_spec d x₁' (bdrop i (arrayToBytes a)) t₁).1 hp₁ with ⟨s₀₁, hpre₁, hrel₁⟩
  rcases (decode_spec d x₂' (bdrop i (arrayToBytes a)) t₂).1 hp₂ with ⟨s₀₂, hpre₂, hrel₂⟩
  subst t₁
  have hpre : t₂.prepend s₀₁ = t₂.prepend s₀₂ := by
    exact hpre₁.symm.trans hpre₂
  have hs₀ : s₀₁ = s₀₂ := prepend_prefix_eq t₂ s₀₁ s₀₂ hpre
  rw [hs₀] at hrel₁
  have hxv : x₁' = x₂' := hd s₀₂ hrel₁ hrel₂
  rw [← hx₁', ← hx₂', hxv]

/-- **Prefix agreement across two `Suffix.prepend`s at different lengths.** If two
prepends of the same length-`n` string agree, the shorter prefix agrees pointwise
with the longer one's first bytes — the `Suffix`-level twin of
`splice_prefix_agree`, which is exactly what the composed uniqueness law needs to
compare two results that consumed *different* amounts. `[propext, Quot.sound]`-only. -/
theorem prepend_prefix_agree {n : Nat} (t₁ t₂ : Suffix n)
    (s₀₁ : Bytes (n - t₁.remaining)) (s₀₂ : Bytes (n - t₂.remaining))
    (heq : t₁.prepend s₀₁ = t₂.prepend s₀₂)
    (hle : n - t₁.remaining ≤ n - t₂.remaining) :
    ∀ (k : Fin (n - t₁.remaining)),
      s₀₁ k = s₀₂ ⟨k.val, Nat.lt_of_lt_of_le k.isLt hle⟩ :=
  splice_prefix_agree (Nat.sub_le n _) (Nat.sub_le n _) hle s₀₁ _ s₀₂ _ heq

/-! ### Why `decodeArray_unique` needs `RelAligned`, not just `Unambiguous`

The pair `Functional d ∧ RelAligned (Rel d)` is not a decorated form of "the leaves
are unambiguous" — it is strictly stronger, and both halves are **load-bearing**
because neither predicate is inherited by a `seq` composition.

The witness is in `Codec/Sound.lean` and is fully proved there:
`bo := alt (iso bIso byte) (pure false)` relates `true` to `single 0` and `false` to
`emptyBytes` (so `bo` is `Unambiguous`), and `d2 := alt (pure ()) (iso unitIso byte)`
relates `()` to strings of length `0` and `1` (so `d2` is `Unambiguous` too). Their
composition `seq bo d2` relates **two distinct values to the one-byte input
`single 0`** — `(true, ())` via the split `m = 1` and `(false, ())` via `m = 0`. Hence
`uniqSeq_not_congruent : ¬ Unambiguous (seq bo d2)`.

`RelAligned` is exactly the hypothesis that kills it: `bo` relates `false` to the
empty string, which is a prefix of (hence prefix-aligned with) the `single 0` that
`true` relates to, so `RelAligned (Rel bo)` would force `true = false`
(`uniqSeq_not_relAligned` proves the composed form fails the same way). `Unambiguous`
sees only the value at *one whole string*; `seq`'s split point is existentially
quantified, so a value that consumes a byte and a value that consumes none slip past
it.

So `Functional ∧ RelAligned` is **the pair that closes**, and it is a hypothesis a
caller must supply for the composition: it is not a consequence of the leaves being
unique. Every uniqueness-gated law here — `encode_of_decode`,
`encode_injective_of_unambiguous`, `decodeArray_unique`, `decodeFull_spec` — is
accordingly **leaf-only** in this tree. -/
theorem decodeArray_unique {α : Type} (d : Codec α)
    (hf : Functional d) (hal : RelAligned (Rel d))
    (a : Array UInt8) (i : Nat) :
    ∀ {x₁ x₂ : α} {c₁ c₂ : Nat},
      (x₁, c₁) ∈ decodeArray d a i → (x₂, c₂) ∈ decodeArray d a i →
      x₁ = x₂ ∧ c₁ = c₂ := by
  intro x₁ x₂ c₁ c₂ h₁ h₂
  rw [decodeArray_eq d a i] at h₁ h₂
  rw [List.mem_map] at h₁ h₂
  rcases h₁ with ⟨⟨x₁', t₁⟩, hp₁, he₁⟩
  rcases h₂ with ⟨⟨x₂', t₂⟩, hp₂, he₂⟩
  simp only at he₁ he₂
  obtain ⟨hx₁, hc₁⟩ := Prod.mk.inj he₁
  obtain ⟨hx₂, hc₂⟩ := Prod.mk.inj he₂
  rcases (decode_spec d x₁' (bdrop i (arrayToBytes a)) t₁).1 hp₁ with ⟨s₀₁, hpre₁, hrel₁⟩
  rcases (decode_spec d x₂' (bdrop i (arrayToBytes a)) t₂).1 hp₂ with ⟨s₀₂, hpre₂, hrel₂⟩
  have hpre : t₁.prepend s₀₁ = t₂.prepend s₀₂ := hpre₁.symm.trans hpre₂
  -- `consumedAbs` pins the prefix lengths to the counts
  have hlen₁ : a.size - i - t₁.remaining = c₁ - i := by unfold consumedAbs at hc₁; omega
  have hlen₂ : a.size - i - t₂.remaining = c₂ - i := by unfold consumedAbs at hc₂; omega
  -- get x₁' = x₂' by aligning on whichever prefix is shorter
  have hxx : x₁' = x₂' := by
    rcases Nat.le_total (t₁.remaining) (t₂.remaining) with hrem | hrem
    -- larger `remaining` ⇒ shorter prefix, so `t₂`'s prefix is the shorter one here
    · have hle : a.size - i - t₂.remaining ≤ a.size - i - t₁.remaining :=
        Nat.sub_le_sub_left hrem _
      have key : x₂' = x₁' :=
        hal (a := x₂') (b := x₁') s₀₂ s₀₁ hle hrel₂ hrel₁ (prepend_prefix_agree t₂ t₁ s₀₂ s₀₁ hpre.symm hle)
      exact key.symm
    · have hle : a.size - i - t₁.remaining ≤ a.size - i - t₂.remaining :=
        Nat.sub_le_sub_left hrem _
      exact hal (a := x₁') (b := x₂') s₀₁ s₀₂ hle hrel₁ hrel₂ (prepend_prefix_agree t₁ t₂ s₀₁ s₀₂ hpre hle)
  refine ⟨?_, ?_⟩
  · exact hx₁.symm.trans (hxx.trans hx₂)
  have hl : a.size - i - t₁.remaining = a.size - i - t₂.remaining :=
    (Sigma.mk.inj (hf x₁' s₀₁ s₀₂ hrel₁ (hxx ▸ hrel₂))).1
  have hi₁ : i ≤ c₁ := by unfold consumedAbs at hc₁; omega
  have hi₂ : i ≤ c₂ := by unfold consumedAbs at hc₂; omega
  omega

/-- The composed uniqueness law, at `Codec.byte`: `decodeArray byte a i` has at most
one result. The concrete instance `decodeArray_unique` below is the general form;
this one is stated separately because it discharges **both** hypotheses with the
base instances `functional_byte`/`relAligned_byte` already proved, so the composed
law is demonstrated non-vacuously for the leaf every downstream format starts from.
`[propext, Quot.sound]`-only. -/
theorem decodeArray_unique_byte (a : Array UInt8) (i : Nat) :
    ∀ {x₁ x₂ : UInt8} {c₁ c₂ : Nat},
      (x₁, c₁) ∈ decodeArray Codec.byte a i → (x₂, c₂) ∈ decodeArray Codec.byte a i →
      x₁ = x₂ ∧ c₁ = c₂ :=
  decodeArray_unique Codec.byte functional_byte relAligned_byte a i

end Codec
