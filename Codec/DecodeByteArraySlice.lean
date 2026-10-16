/- Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later -/

import Codec.DecodeByteArray
import Codec.Decode

/-!
# The slice-returning `ByteArray` decode surface (the "carrier swap, not compiler" fix)

Two efficiency attempts (`extern-c-fast-path`, the archived `compiler-tier-extraction`)
failed for one shared reason: they sped up the boxed byte *loop* while the cost the
bench measures is the **`List UInt8` result carrier** at the API edge — a heap cons
cell (and a `Nat` box) per byte. This module removes that carrier from the hot edge:

  * `decodeByteArraySlice d a i : Option (α × USize)` — a **native first-match
    recursion** reading `a[i]`, threading the index through `seq`, and returning the
    *consumed length* as a `USize`; the `byte` case is **one indexed read + increment**,
    no `List` cell, no per-element `Nat` box.
  * `decodeFullByteArraySlice a i : Option (ByteArray × USize)` — full consumption of
    `Codec.byte` returns the **packed suffix** (one `ByteArray.extract` = a single
    `memcpy`-class copy) plus its length; never an `Option (List α × Nat)`.

Both surfaces are **`USize`-indexed** at their entry point (Decision 2 of the design:
`USize` is a scalar in Lean's IR, so the existing `EmitC` prints a `size_t` loop with no
representation fiction). The provable refinement closes against the unchanged
`Nat`-indexed spec by a one-line `USize.toNat`/`USize.ofNat` correspondence. The `List`
APIs (`decode`, `decodeByteArray`, `decodeFullByteArray`) and every core law are
unchanged — this surface is **additive**.

**Zero-copy lifetime seam (named trust).** The returned `α`/`ByteArray` aliases the
source `a`'s underlying buffer (the `decodeByteArraySlice` `byte` case reads `a[i]`
without copying; `decodeFullByteArraySlice` returns an `extract` whose backing store
shares `a`'s). Lean's value model has no observable aliasing, so this is a *documented
contract*, not a proof obligation: the span is valid while `a` is referenced, and a C
consumer must not `lean_dec_ref`/realloc `a` within that span. This is the same named
trust posture the `@[extern]` seam took, stated at the buffer edge, and it introduces
**no new axiom** — everything below is `[propext, Quot.sound]`-only.
-/

namespace Codec

/-! ## The native greedy decoder (relative consumed length, `Nat`-indexed)

`decodeByteArrayHead` is a **greedy, single-result** decoder: it reads `a[i]` by index,
threads `i + m` through `seq`, and short-circuits at the first step that yields a
result — it materializes *no* `List` of results. Its `byte` case is O(1). Unlike the
relational `decode`, it does **not** backtrack across `seq`/`alt` (a failed `d₂` step
does not try the next `d₁` candidate), so it is *sound but not complete*: every result
it returns is a valid `decode` of the input, but it may return `none` where the
relation has a match. The `USize` surface below wraps it at the boundary. -/

def decodeByteArrayHead {α : Type} (d : Codec α) (a : ByteArray) (i : Nat) : Option (α × Nat) :=
  match d with
  | Codec.iso is d => (decodeByteArrayHead d a i).bind fun (x, n) => (is.apply x).map fun y => (y, n)
  | Codec.seq d₁ d₂ =>
      (decodeByteArrayHead d₁ a i).bind fun (x, m) =>
        (decodeByteArrayHead d₂ a (i + m)).map fun (y, n) => ((x, y), m + n)
  | Codec.alt d₁ d₂ => (decodeByteArrayHead d₁ a i).orElse fun _ => decodeByteArrayHead d₂ a i
  | Codec.empty => none
  | Codec.pure x => some (x, 0)
  | Codec.byte => if h : i < a.size then some (a[i], 1) else none

/-- **Soundness** of the greedy decoder: every result `(x, n)` it returns is a valid
`decode` result over the `Bytes` spec — `x` decodes with the remaining input
`drop (i + n) a.data.toList` (with the one byte fact `a[i] = a.data[i]` in the `byte`
case). Proved by induction on `d`; the greedy `bind`/`orElse`/`map` combinations are all
subsets of the relational `flatMap`/`append`/`filterMap` (no completeness claimed, and
none needed for soundness). `[propext, Quot.sound]`-only. -/
theorem decodeByteArrayHead_sound {α : Type} (d : Codec α) (a : ByteArray) (i : Nat)
    (x : α) (n : Nat) :
    decodeByteArrayHead d a i = some (x, n) →
      (x, a.data.toList.drop (i + n)) ∈ decode d (a.data.toList.drop i) := by
  induction d generalizing a i n with
  | iso is d ih =>
      intro h
      rw [decodeByteArrayHead] at h
      cases hd : decodeByteArrayHead d a i with
      | none => simp [hd] at h
      | some pr =>
          rcases pr with ⟨x', n'⟩
          simp [hd] at h
          cases happ : is.apply x' with
          | none => simp [happ] at h
          | some y =>
              simp [happ] at h
              have hin : (x', a.data.toList.drop (i + n')) ∈ decode d (a.data.toList.drop i) :=
                ih a i x' n' hd
              rw [decode]
              rw [List.mem_filterMap]
              refine ⟨(x', a.data.toList.drop (i + n')), hin, ?_⟩
              rcases h with ⟨hyx, hnn⟩
              simp [happ, hyx, hnn]
  | seq d₁ d₂ ih₁ ih₂ =>
      intro h
      rw [decodeByteArrayHead] at h
      cases hd₁ : decodeByteArrayHead d₁ a i with
      | none => simp [hd₁] at h
      | some pr₁ =>
          rcases pr₁ with ⟨x₁, m⟩
          simp [hd₁] at h
          cases hd₂ : decodeByteArrayHead d₂ a (i + m) with
          | none => simp [hd₂] at h
          | some pr₂ =>
              rcases pr₂ with ⟨x₂, n₂⟩
              simp [hd₂] at h
              rcases h with ⟨a, b, hab, hxa, hmn⟩
              rcases hab with ⟨hx₂a, hn₂b⟩
              subst a
              subst b
              have hx : x = (x₁, x₂) := hxa.symm
              have hn : n = m + n₂ := hmn.symm
              have hin₁ : (x₁, a.data.toList.drop (i + m)) ∈ decode d₁ (a.data.toList.drop i) :=
                ih₁ a i x₁ m hd₁
              have hin₂ : (x₂, a.data.toList.drop (i + m + n₂)) ∈ decode d₂ (a.data.toList.drop (i + m)) :=
                ih₂ a (i + m) x₂ n₂ hd₂
              rw [decode]
              rw [List.mem_flatMap]
              refine ⟨(x₁, a.data.toList.drop (i + m)), hin₁, ?_⟩
              rw [List.mem_flatMap]
              refine ⟨(x₂, a.data.toList.drop (i + m + n₂)), hin₂, ?_⟩
              simp [hx, hn, Nat.add_assoc]
  | alt d₁ d₂ ih₁ ih₂ =>
      intro h
      rw [decodeByteArrayHead] at h
      cases hd : decodeByteArrayHead d₁ a i with
      | none =>
          simp [hd] at h
          have hin : (x, a.data.toList.drop (i + n)) ∈ decode d₂ (a.data.toList.drop i) :=
            ih₂ a i x n h
          rw [decode]
          exact List.mem_append.mpr (Or.inr hin)
      | some pr =>
          rcases pr with ⟨x₁, n₁⟩
          simp [hd] at h
          rcases h with ⟨hx₁, hn₁⟩
          subst x
          subst n
          have hin : (x₁, a.data.toList.drop (i + n₁)) ∈ decode d₁ (a.data.toList.drop i) :=
            ih₁ a i x₁ n₁ hd
          rw [decode]
          exact List.mem_append.mpr (Or.inl hin)
  | empty => intro h; simp [decodeByteArrayHead] at h
  | pure x₀ =>
      intro h
      rw [decodeByteArrayHead] at h
      cases h
      simp [decode]
  | byte =>
      intro h
      rw [decodeByteArrayHead] at h
      split at h
      · cases h
        have hdrop : a.data.toList.drop i = a[i] :: a.data.toList.drop (i + 1) := by
          rw [List.drop_eq_getElem_cons (l := a.data.toList) (i := i) (by simpa using ‹i < a.size›)]
          rw [ByteArray.getElem_eq_getElem_data]
          rfl
        simp [decode, hdrop]
      · simp at h

/-! ## The `USize`-indexed slice surface -/

/-- The slice-returning decode entry point: the first (leftmost) match of `d` against
the packed `ByteArray` `a` starting at `USize` index `i`, as `(value, consumed-length)`
where the consumed length is a `USize`. `USize`-indexed at the boundary (Decision 2);
the `Nat`-indexed `decodeByteArrayHead` recursion above is the provable core. -/
def decodeByteArraySlice {α : Type} (d : Codec α) (a : ByteArray) (i : USize) : Option (α × USize) :=
  (decodeByteArrayHead d a i.toNat).map fun (x, n) => (x, USize.ofNat n)

/-- The refinement law (task 1.3, decode direction): unfolding `decodeByteArraySlice`
is `decodeByteArrayHead d a i.toNat` with the consumed `Nat` wrapped in `USize.ofNat`. -/
theorem decodeByteArraySlice_unfold {α : Type} (d : Codec α) (a : ByteArray) (i : USize) :
    decodeByteArraySlice d a i =
      (decodeByteArrayHead d a i.toNat).map (fun (x, n) => (x, USize.ofNat n)) := rfl

/-- The slice is **spec-sound**: a returned `(x, k)` is `USize.ofNat n` for the (greedy)
consumed count `n`, and `x` decodes against the `Bytes` spec with `n` bytes consumed of
`drop i.toNat` (the remaining input is `drop (i.toNat + n)`). Closes from
`decodeByteArrayHead_sound` (`[propext, Quot.sound]`-only). -/
theorem decodeByteArraySlice_spec {α : Type} (d : Codec α) (a : ByteArray) (i : USize)
    (x : α) (k : USize) :
    decodeByteArraySlice d a i = some (x, k) →
      ∃ n, k = USize.ofNat n ∧
        (x, a.data.toList.drop (i.toNat + n)) ∈ decode d (a.data.toList.drop i.toNat) := by
  intro h
  rw [decodeByteArraySlice_unfold] at h
  rw [Option.map_eq_some_iff] at h
  rcases h with ⟨⟨x', n⟩, hhead, hf⟩
  simp at hf
  rcases hf with ⟨hx, hk⟩
  subst x'
  refine ⟨n, hk.symm, decodeByteArrayHead_sound d a i.toNat x n hhead⟩

/-! ## The full-consumption packed-suffix surface -/

/-- Full consumption of `Codec.byte`: return the packed suffix `a[i.toNat .. a.size)` and
its length as a `USize`, in **one** packed copy — never an `Option (List α × Nat)`.
The suffix is built as `ByteArray.mk ((a.data.toList.drop i.toNat).toArray)` (the same
clean construction `Codec.ExternFastPath.byteSlice` uses: `List.toArray`/`Array.toList`
are `rfl` mutual inverses over the reducible `Array`, so the content law closes by `rfl`,
keeping the axiom record `[propext, Quot.sound]`-only). Returns `none` when `i` is past
the end. -/
def decodeFullByteArraySlice (a : ByteArray) (i : USize) : Option (ByteArray × USize) :=
  if i.toNat ≤ a.size then
    some (ByteArray.mk ((a.data.toList.drop i.toNat).toArray), USize.ofNat (a.size - i.toNat))
  else none

/-- The packed suffix's **bytes** are exactly the tail: whenever the slice returns
`some (b, _)`, `b.data.toList = a.data.toList.drop i.toNat`. Closes `[propext,
Quot.sound]`-only — the `ByteArray.mk`/`List.toArray`/`Array.toList` pair is `rfl` over
the reducible `Array`, with no `Classical.choice` (contrast the stdlib `Array.toList_extract`). -/
theorem decodeFullByteArraySlice_contents (a : ByteArray) (i : USize) (b : ByteArray) (k : USize) :
    decodeFullByteArraySlice a i = some (b, k) →
      b.data.toList = a.data.toList.drop i.toNat := by
  intro h
  unfold decodeFullByteArraySlice at h
  by_cases hle : i.toNat ≤ a.size
  · simp [hle] at h
    rcases h with ⟨hb, _hk⟩
    rw [← hb]
  · exfalso
    simp [hle] at h

/-- The packed suffix's **length** is `USize.ofNat (a.size - i.toNat)` (the `USize`
reading of the consumed tail length; the `Nat` reading is that figure, saturating only
for buffers exceeding the `USize` width, which real buffers cannot). -/
theorem decodeFullByteArraySlice_size (a : ByteArray) (i : USize) :
    (decodeFullByteArraySlice a i).map (fun p => p.2) =
      if i.toNat ≤ a.size then some (USize.ofNat (a.size - i.toNat)) else none := by
  unfold decodeFullByteArraySlice
  split
  · next _h => rfl
  · next hge => rfl

/-- The full-consumption result of `decodeRepeat Codec.byte` is the input alone (the
found `unique`/`full` witnesses for `Codec.byte`, stated locally so this module needs no
`@[extern]` import). -/
theorem decodeRepeat_byte_full (s : Bytes) :
    (s, []) ∈ decodeRepeat Codec.byte byte_consumesByte s := by
  induction s with
  | nil => rw [decodeRepeat_eq]; simp
  | cons b rest ih =>
      rw [decodeRepeat_eq]
      simp [decode]
      exact ih

/-- The uniqueness of `Codec.byte`'s full consumption (the `huniq` hypothesis the
`decodeFullByteArray_spec`/`decodeFull_spec` laws take). -/
theorem decodeRepeat_byte_unique {x : List UInt8} {s : Bytes}
    (hmem : (x, []) ∈ decodeRepeat Codec.byte byte_consumesByte s) : x = s := by
  induction s generalizing x with
  | nil =>
      rw [decodeRepeat_eq] at hmem
      simp [decode] at hmem
      exact hmem
  | cons b rest ih =>
      rw [decodeRepeat_eq] at hmem
      simp [decode] at hmem
      rcases hmem with ⟨a, ha, hb⟩
      subst x
      rw [ih ha]

/-- **The refinement against `decodeFullByteArray_spec` (task 1.3).** Whenever the slice
returns `some (b, k)`, the proved full-consumption `decodeFullByteArray Codec.byte` over
the same `ByteArray`/index reproduces exactly `b.data.toList` (ending at `a.size`) —
the packed suffix *is* the full-consumption result, with no `List` cons cell and no
`Nat` box along the way. Closes from `decodeFullByteArraySlice_contents` +
`decodeFullByteArray_spec` + `decodeRepeat_byte_unique`. `[propext, Quot.sound]`-only. -/
theorem decodeFullByteArraySlice_eq (a : ByteArray) (i : USize) (b : ByteArray) (k : USize) :
    decodeFullByteArraySlice a i = some (b, k) →
      decodeFullByteArray Codec.byte byte_consumesByte a i.toNat =
        some (b.data.toList, a.size) := by
  intro h
  rw [decodeFullByteArray_spec Codec.byte byte_consumesByte
      (fun {x y} {s} hx hy => (decodeRepeat_byte_unique hx).trans (decodeRepeat_byte_unique hy).symm)
      a i.toNat (b.data.toList) a.size]
  constructor
  · have htail : b.data.toList = a.data.toList.drop i.toNat :=
      decodeFullByteArraySlice_contents a i b k h
    rw [htail]
    exact decodeRepeat_byte_full (a.data.toList.drop i.toNat)
  · rfl

end Codec
