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

/-! ## Remaining refinements (not yet proved)

The following are the remaining Layer-1 refinement laws, left for a dedicated
follow-up (they need the from-scratch `Suffix`-transport bridge on the decode side
and an `Array`-`ofFn`-clean readback inversion on the encode side — both the
"real proof work" the design flags as not-yet-existing):

  * `decodeArray_eq` — packed decoder ≡ spec `decode`, via the `Suffix`
    reconstruction `{ remaining := n - c, hle := Nat.sub_le n c, bytes := bdrop c s }`.
  * `decodeFullArray_spec` — packed full-consumption ≡ spec `decodeFull`.
  * `encodeArray_eq` — packed encoder ≡ spec `encode` (List-level readback).
  * `encodeByteArrayBytes_eq` — byte-sequence packer ≡ `List.toArray` materialization.

Each must close `[propext, Quot.sound]`-only, zero `sorry`, zero `Classical.choice`.
-/

end Codec
