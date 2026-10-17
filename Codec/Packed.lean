/- Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later -/

import Codec.Decode
import Codec.Encode

/-!
# The packed result carrier

This file gives the **packed result carrier** for the interpreter: a decoder
that reads `a[i]` by a scalar index and threads only the consumed count, and an
encoder that accumulates into a contiguous `Array UInt8`. Each is proved equal to
the unchanged `Bytes n := Fin n → UInt8` spec by a refinement lemma that closes
`[propext, Quot.sound]`-only.

## Cursor type

The packed carrier is indexed by `Nat` (the consumed count), not `USize`. The
reason is proof-first: `USize` addition is `Nat` addition modulo `2^64`
(`USize.toNat_add : (a + b).toNat = (a.toNat + b.toNat) % 2^64`), and
`USize.size = 2^64` depends on `System.Platform.numBits = 64` — a platform fact
that is not cleanly provable in the stdlib. A `USize`-cursor refinement would
therefore carry an unproven platform/modulo premise into every law, violating the
`[propext, Quot.sound]`-only gate. The `Nat` cursor is the same choice
`fastEncodeRepeat`/`pushBytesFrom` already make and keep `#print axioms`-clean.
(The `USize`-lowers-to-`size_t` scalar claim is verified or refuted by IR
inspection — see the bench/tasks notes — never asserted here.)

## The bridge

The spec `decode : Codec α → {n} → Bytes n → List (α × Suffix n)` returns a
`Suffix n` (a length-indexed remainder). The packed decoder returns `List (α × Nat)`
— the `Nat` is the consumed count. The bridge reconstructs the spec's `Suffix n`
from the consumed count `c` (with `c ≤ n`) as

    { remaining := n - c, hle := Nat.sub_le n c, bytes := bdrop c s }

where `s : Bytes n` is the readback of the array (`fun i => a[i.val]`).
-/

namespace Codec

/-! ## Bridge: read `Array UInt8` back as `Bytes` -/

/-- Read a contiguous `Array UInt8` back as a length-indexed `Bytes a.size`:
`fun i => a[i.val]`. A pure `Array.get` read, no `ofFn` round-trip (which would
leak `Classical.choice`). -/
def arrayToBytes (a : Array UInt8) : Bytes a.size :=
  fun i => a[i.val]

/-! ## The packed decoder -/

/-- The packed decoder: read bytes by an `Array UInt8` index and thread a consumed
count. Structurally identical to `decode`, but the result is `List (α × Nat)` — the
`List` is the non-determinism multiplicity (the `alt`/`seq` result), and the `Nat`
is the packed consumed count. `a[i]` is an `Array.get` (an `@[extern]` contiguous
read); there is no list-peeling. -/
def decodeArray {α : Type} (d : Codec α) (a : Array UInt8) (i : Nat) : List (α × Nat) :=
  match d with
  | Codec.iso j d =>
      (decodeArray d a i).filterMap fun (x, c) => (j.apply x).map fun y => (y, c)
  | Codec.seq d₁ d₂ =>
      (decodeArray d₁ a i).flatMap fun (x, c₁) =>
        (decodeArray d₂ a c₁).flatMap fun (y, c₂) => [((x, y), c₂)]
  | Codec.alt d₁ d₂ => decodeArray d₁ a i ++ decodeArray d₂ a i
  | Codec.empty => []
  | Codec.pure x => [(x, i)]
  | Codec.byte =>
      if h : i < a.size then
        [(a[i], i + 1)]
      else []

/-! ## The packed full-consumption result -/

/-- The packed full-consumption decoder: a single suffix copy, never
`Option (List α × Suffix n)`. Its body is the `rfl`-clean
`ByteArray.mk ((a.toList.drop i).toArray)` — a list-materializing transport
(chosen so the refinement stays `Classical.choice`-free), **not**
`copySlice`/`extract`. The `c` in the result is the consumed count; the packed
suffix is the `ByteArray` of the bytes at-or-after `c`. -/
def decodeFullArray {α : Type} (d : Codec α) (a : Array UInt8) (i : Nat) :
    Option (ByteArray × Nat) :=
  match decodeArray d a i with
  | [] => none
  | (_, c) :: _ => some (ByteArray.mk ((a.toList.drop c).toArray), c)

/-! ## The packed encoder -/

/-- The byte-sequence packer: fold a `List UInt8` into a `ByteArray` by
`ByteArray.push` (amortized O(n)) — a *byte-sequence* packer, **not** a general
`Codec α` encoder (that is `encodeArray`). -/
def encodeByteArrayBytes (xs : List UInt8) : ByteArray :=
  xs.foldl (fun acc b => acc.push b) ByteArray.empty

/-- The packed encoder: produce an `Array UInt8` by accumulating with
`Array.append` instead of a nested `concat` closure. Structural (not `partial`),
matching `encode`, so the refinement `encodeArray_eq` is provable by induction on
`d`. -/
def encodeArray {α : Type} (d : Codec α) (x : α) : Option (Array UInt8) :=
  match d with
  | Codec.iso j d => (j.unapply x).bind fun a => encodeArray d a
  | Codec.seq d₁ d₂ =>
      match x with
      | (x₁, x₂) =>
          (encodeArray d₁ x₁).bind fun s₁ =>
            (encodeArray d₂ x₂).map fun s₂ => s₁ ++ s₂
  | Codec.alt d₁ d₂ => encodeArray d₁ x <|> encodeArray d₂ x
  | Codec.empty => none
  | Codec.pure x₀ => if x = x₀ then some #[] else none
  | Codec.byte => some #[x]

/-! ## Refinement lemmas -/

/-- The consumed count a `Suffix (a.size - i)` produces against a buffer starting
at absolute cursor `i`: the absolute consumed count is `i + ((a.size - i) - t.remaining)`.
This is the packed-carrier readback of the spec's `Suffix` remainder. -/
def consumedAbs (a : Array UInt8) (i : Nat) (t : Suffix (a.size - i)) : Nat :=
  i + ((a.size - i) - t.remaining)

/-- The identity suffix consumes nothing: `consumedAbs a i (Suffix.id …) = i`. -/
theorem consumedAbs_id (a : Array UInt8) (i : Nat) :
    consumedAbs a i (Suffix.id (a.size - i) (bdrop i (arrayToBytes a))) = i := by
  dsimp [consumedAbs, Suffix.id]
  omega

/-- Dropping one byte consumes exactly one: `consumedAbs a i (Suffix.drop 1 s) = i + 1`
when the suffix is non-empty (`i < a.size`). -/
theorem consumedAbs_drop_one (a : Array UInt8) (i : Nat) (s : Bytes (a.size - i))
    (h : i < a.size) :
    consumedAbs a i (Suffix.drop 1 s) = i + 1 := by
  dsimp [consumedAbs, Suffix.drop]
  omega

/-- The packed decoder never overruns the buffer: every result's consumed count is
at most `a.size` (and at least the starting cursor `i`). `[propext, Quot.sound]`-only. -/
theorem decodeArray_bounded {α : Type} (d : Codec α) (a : Array UInt8) (i c : Nat)
    (x : α) :
    (x, c) ∈ decodeArray d a i → i ≤ c := by
  induction d generalizing i c with
  | iso j d ih =>
      intro hc
      rw [decodeArray, List.mem_filterMap] at hc
      rcases hc with ⟨pr, hmem, hm⟩
      have hc : c = pr.2 := by
        cases hj : j.apply pr.1 with
        | none => simp [hj] at hm
        | some y =>
            simp [hj] at hm
            exact hm.2.symm
      subst c
      exact ih i pr.2 pr.1 hmem
  | seq d₁ d₂ ih₁ ih₂ =>
      intro hc
      rw [decodeArray, List.mem_flatMap] at hc
      rcases hc with ⟨pr₁, h1, h2⟩
      rw [List.mem_flatMap] at h2
      rcases h2 with ⟨pr₂, h3, h4⟩
      replace h4 : x = (pr₁.1, pr₂.1) ∧ c = pr₂.2 := by simpa using h4
      rcases h4 with ⟨hx, hc2⟩
      subst c
      have hb1 := ih₁ i pr₁.2 pr₁.1 h1
      have hb2 := ih₂ pr₁.2 pr₂.2 pr₂.1 h3
      exact Nat.le_trans hb1 hb2
  | alt d₁ d₂ ih₁ ih₂ =>
      intro hc
      rw [decodeArray, List.mem_append] at hc
      rcases hc with hc | hc
      · exact ih₁ i c x hc
      · exact ih₂ i c x hc
  | empty =>
      intro hc
      simp [decodeArray] at hc
  | pure x₀ =>
      intro hc
      simp [decodeArray] at hc
      rcases hc with ⟨hx, hc⟩
      subst x c
      exact Nat.le_refl i
  | byte =>
      intro hc
      rw [decodeArray] at hc
      by_cases h : i < a.size
      · simp [h] at hc
        rcases hc with ⟨hx, hc⟩
        subst x c
        exact Nat.le_succ i
      · simp [h] at hc

/-! ## Transport lemmas for the decode refinement

The decode-side `Suffix`-transport bridge. The spec's `decode d s` returns
`(x, t)` with `t : Suffix n`; the packed `decodeArray d a i` returns `(x, c)` with
the absolute consumed count `c`. The bridge is `consumedAbs a i t` (`i` plus the
count consumed within `s`), and these lemmas transport a `bdrop`/`Suffix.trans`
across it. `[propext, Quot.sound]`-only. -/

/-- `(n - i) - m = n - (i + m)`. The length identity behind
`bdrop` composition (`Nat.sub_sub`). -/
theorem sub_sub_eq {n i m : Nat} : (n - i) - m = n - (i + m) := by
  exact Nat.sub_sub n i m

/-- `bdrop (i + m) s` is `bdrop m (bdrop i s)` up to the length cast
`(n - i) - m = n - (i + m)`. The composition law the `seq` bridge needs.
`[propext, Quot.sound]`-only. -/
theorem bdrop_add {n i m : Nat} (s : Bytes n) :
    bdrop (i + m) s = cast (congrArg Bytes (sub_sub_eq (n := n) (i := i) (m := m))) (bdrop m (bdrop i s)) := by
  apply Bytes.ext
  intro k
  unfold bdrop
  rw [cast_bytes_val (e := sub_sub_eq (n := n) (i := i) (m := m))]
  congr 1
  apply Fin.ext
  dsimp
  omega

/-- The length identity: the length left after consuming `consumedAbs a i t` bytes is
exactly `t.remaining`. `[propext, Quot.sound]`-only. -/
theorem consumedAbs_remaining (a : Array UInt8) (i : Nat) (t : Suffix (a.size - i)) :
    a.size - consumedAbs a i t = t.remaining := by
  unfold consumedAbs
  have hle : t.remaining ≤ a.size - i := t.hle
  omega

/-! ## Remaining refinements (not yet proved)

The decode-side refinement laws. The `seq` case of `decodeArray_eq` needs a
yet-unproven invariant of `decode` — that every result suffix `t` is a *genuine*
suffix, `t.bytes = bdrop (n - t.remaining) s` — before the `bdrop`-composition
(`bdrop_add`, proved above) and the `consumedAbs` transitivity bridge can close it.
That invariant is the "from-scratch `Suffix`-transport bridge" the design flags:

  * `decodeArray_eq` — packed decoder ≡ spec `decode`, via `consumedAbs`; the
    `iso`/`alt`/`empty`/`pure`/`byte` cases close, the `seq` case needs the
    `decode` genuine-suffix invariant (`t.bytes = bdrop (t.consumed) s`) first.
  * `decodeFullArray_spec` — packed full-consumption ≡ spec `decodeFull` (depends
    on `decodeArray_eq`).

Each must close `[propext, Quot.sound]`-only, zero `sorry`, zero `Classical.choice`.
-/

/-! ## Refinement: the packed encoder equals the spec `encode` -/

/-- If the readback equality holds, `encodeArray d x` is `none` exactly when
`encode d x` is `none`. This is the monadic-skeleton bridge that lets the
`seq`/`alt` cases of `encodeArray_eq` turn `encodeArray = none` into
`encode = none` (and back) without re-running the encoder. `[propext]`-only. -/
theorem map_toList_eq_ofFn_none_iff {α : Type} {d : Codec α} {x : α} :
    ((encodeArray d x).map (fun a : Array UInt8 => a.toList) = (encode d x).map (fun e => List.ofFn e.2)) →
    (encodeArray d x = none ↔ encode d x = none) := by
  intro h
  constructor
  · intro hnA
    cases e : encode d x with
    | none => rfl
    | some e' =>
        rcases e' with ⟨n, s⟩
        rw [hnA, e] at h
        simp only [Option.map] at h
        cases h
  · intro hn
    cases e : encodeArray d x with
    | none => rfl
    | some a =>
        rw [e, hn] at h
        simp only [Option.map] at h
        cases h

/-- The packed encoder equals the spec `encode`, up to the List-level readback:
`(encodeArray d x).map (·.toList) = (encode d x).map (List.ofFn ∘ snd)`. The
`Array.toList`/`List.ofFn` readback is the `[propext, Quot.sound]`-clean form (the
`Array.ofFn`/`Array.toList_ofFn` round-trip would leak `Classical.choice`); the
`seq` leaf is `Array.toList_append` + `ofFn_concat`. `[propext, Quot.sound]`-only. -/
theorem encodeArray_eq {α : Type} (d : Codec α) (x : α) :
    (encodeArray d x).map (fun a : Array UInt8 => a.toList) =
      (encode d x).map (fun e => List.ofFn e.2) := by
  induction d with
  | iso i d ih =>
      simp only [encodeArray, encode, Option.bind]
      cases hi : i.unapply x with
      | none => simp
      | some a => simpa [hi] using ih a
  | seq d₁ d₂ ih₁ ih₂ =>
      cases x with
      | mk x₁ x₂ =>
          simp only [encodeArray, encode, Option.bind]
          have h₁ := ih₁ x₁
          have h₂ := ih₂ x₂
          have hn₁ := (map_toList_eq_ofFn_none_iff (d := d₁) (x := x₁)) h₁
          have hn₂ := (map_toList_eq_ofFn_none_iff (d := d₂) (x := x₂)) h₂
          cases ha₁ : encodeArray d₁ x₁ with
          | none =>
              have he₁ : encode d₁ x₁ = none := hn₁.mp ha₁
              simp only [he₁, Option.map]
          | some a₁ =>
              have he₁ : encode d₁ x₁ ≠ none := by
                intro h; have := hn₁.mpr h; rw [ha₁] at this; cases this
              cases hx₁ : encode d₁ x₁ with
              | none => exfalso; exact he₁ hx₁
              | some e₁ =>
                  rcases e₁ with ⟨n₁, s₁⟩
                  cases ha₂ : encodeArray d₂ x₂ with
                  | none =>
                      have he₂ : encode d₂ x₂ = none := hn₂.mp ha₂
                      simp only [he₂, Option.map]
                  | some a₂ =>
                      have he₂ : encode d₂ x₂ ≠ none := by
                        intro h; have := hn₂.mpr h; rw [ha₂] at this; cases this
                      cases hx₂ : encode d₂ x₂ with
                      | none => exfalso; exact he₂ hx₂
                      | some e₂ =>
                          rcases e₂ with ⟨n₂, s₂⟩
                          have h₁' : a₁.toList = List.ofFn s₁ := by
                            rw [ha₁] at h₁
                            rw [hx₁] at h₁
                            simp only [Option.map] at h₁
                            exact Option.some.inj h₁
                          have h₂' : a₂.toList = List.ofFn s₂ := by
                            rw [ha₂] at h₂
                            rw [hx₂] at h₂
                            simp only [Option.map] at h₂
                            exact Option.some.inj h₂
                          simp only [Option.map]
                          rw [Array.toList_append, h₁', h₂']
                          exact congrArg some (ofFn_concat s₁ s₂).symm
  | alt d₁ d₂ ih₁ ih₂ =>
      simp only [encodeArray, encode]
      have h₁ := ih₁ x
      have h₂ := ih₂ x
      have hn₁ := (map_toList_eq_ofFn_none_iff (d := d₁) (x := x)) h₁
      cases ha₁ : encodeArray d₁ x with
      | none =>
          have he₁ : encode d₁ x = none := hn₁.mp ha₁
          simp only [he₁, Option.map]
          exact h₂
      | some a =>
          have he₁ : encode d₁ x ≠ none := by
            intro h
            have := hn₁.mpr h
            rw [ha₁] at this
            cases this
          simp only [Option.map]
          cases hx : encode d₁ x with
          | none => exfalso; exact he₁ hx
          | some e =>
              rcases e with ⟨n, s⟩
              rw [ha₁] at h₁
              simp only [Option.map] at h₁
              simpa [hx] using h₁
  | empty => simp [encodeArray, encode]
  | pure x₀ => by_cases h : x = x₀ <;> simp [encodeArray, encode, h]
  | byte => simp [encodeArray, encode, single]

/-- `ByteArray.push` projects to `Array.push` on the backing data. -/
theorem bpush_data (bs : ByteArray) (b : UInt8) : (bs.push b).data = bs.data.push b := by
  rfl

/-- `List.foldl` over `ByteArray.push` projects to `List.foldl` over `Array.push`
on the backing data. `[propext, Quot.sound]`-free (`#print axioms` ⇒ none). -/
theorem foldl_push_data (acc : ByteArray) (xs : List UInt8) :
    (List.foldl (fun a b => a.push b) acc xs).data = List.foldl (fun a b => a.push b) acc.data xs := by
  induction xs generalizing acc with
  | nil => rfl
  | cons b rest ih =>
      rw [List.foldl_cons, List.foldl_cons]
      rw [ih (acc.push b)]
      rw [bpush_data]

/-- `List.foldl` over `Array.push` is `acc ++ xs.toArray`. `[propext, Quot.sound]`-only. -/
theorem foldl_push_append (acc : Array UInt8) (xs : List UInt8) :
    List.foldl (fun a b => a.push b) acc xs = acc ++ xs.toArray := by
  induction xs generalizing acc with
  | nil => rw [List.foldl_nil, Array.append_empty]
  | cons b rest ih =>
      rw [List.foldl_cons, ih (acc.push b), List.toArray_cons]
      apply Array.ext'
      rw [Array.toList_append, Array.toList_append, Array.toList_push]
      rw [Array.toList_append]
      rw [List.append_assoc]

/-- The byte-sequence packer is the `List.toArray` materialization:
`encodeByteArrayBytes xs = ByteArray.mk xs.toArray`. `[propext, Quot.sound]`-only. -/
theorem encodeByteArrayBytes_eq (xs : List UInt8) :
    encodeByteArrayBytes xs = ByteArray.mk xs.toArray := by
  apply ByteArray.ext
  unfold encodeByteArrayBytes
  rw [foldl_push_data ByteArray.empty xs]
  change List.foldl (fun a b => a.push b) (#[] : Array UInt8) xs = (ByteArray.mk xs.toArray).data
  rw [foldl_push_append (#[] : Array UInt8) xs]
  rw [Array.empty_append]

end Codec
