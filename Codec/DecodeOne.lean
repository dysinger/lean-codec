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
**sound only when the description is unambiguous/functional** — i.e. when
`decodeArray d a i` has at most one result. It is therefore *never* presented as
equal to the backtracking `decodeArray` without that hypothesis. The facts proved
mirror the `decodeFull_spec` template (`Codec.Decode`):

1. **Unconditional soundness** — `decodeOne_mem`: every result `decodeOne`
   returns is a genuine backtracking result (`(x, c) ∈ decodeArray d a i`), so a
   committed choice never *fabricates* a result. (Note `decodeOne` may return
   `none` even when `decodeArray` has a result — e.g. the first `d₁` result is a
   dead end for `seq` — which is exactly why completeness needs a gate.)

2. **Gated** — under `Unambiguous d`, two `decodeArray` results that consume the
   same count agree on the value; under `Functional d`, one value determines one
   count. Together these pin `decodeArray d a i` to at most one result, and the
   committed decoder then *equals* the unique result, with nothing silently
   discarded.

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

/-- Under `Functional d`, one value determines one consumed count: two
`decodeArray` results for the *same* value must consume the same count. Together
with `decodeArray_unambiguous_value` (same count ⇒ same value, under
`Unambiguous`), this pins `decodeArray d a i` to at most one result — the
hypothesis that makes the committed `decodeOne` complete (not just sound).
`[propext, Quot.sound]`-only. -/
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

/-
## Status note (remaining proof work)

`decodeOne` + `decodeOne_mem` + `decodeArray_functional_count` are proved above,
`[propext, Quot.sound]`-only. The *second* half of the pair-uniqueness gate —
`Unambiguous d ⇒` two same-`count` `decodeArray` results agree on the value — is the
remaining sub-obligation for Task 3.1. Its forward bridge is: `(x₁, c) ∈ decodeArray
d a i` transports (via `decodeArray_eq` + `decode_spec`) to `Rel d x₁ s₀₁` for the
genuine consumed prefix `s₀₁`, and the same count pins `s₀₁ = s₀₂` (as the two
`(a.size - i) - remaining`-length prefixes of the same input) before `Unambiguous`
forces `x₁ = x₂`. The `splice`/`prepend`-prefix extraction that discharges `s₀₁ = s₀₂`
is the outstanding step; it is tracked in the task ledger, not silently dropped.
-/

end Codec
