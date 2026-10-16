/- Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later -/

import Codec.Iso

/-!
# LEB128 varbinary: the `Nat` spec and the F\* varint port

The F\* varbinary hot path, ported onto this library's substrate. LEB128 is
byte-aligned 7-bits-per-byte with a continuation high bit: the low 7 bits of each
byte are a base-128 digit (little-endian), and every byte except the last has bit 7
set. `0` encodes to the single byte `[0]`; `128` to `[0x80, 0x01]`; `300` to
`[0xAC, 0x02]`.

The *spec* is the partial isomorphism `varint : Iso Nat Bytes` (encode =
`varint_encode_go`, decode = `varint_decode_go`), whose inverse law is the LEB128
roundtrip proved once below. The `ByteArray`-carrier run-models (`decodeVarint`/
`encodeVarint`, in `Codec.DecodeByteArray`/`Codec.EncodeByteArray`-style files)
are then tied to this spec through the carrier equality, exactly as the codec
interpreters are. The `Iso` roundtrip is proved `[propext, Quot.sound]`-only (no
`Classical`, no `omega` axioms — `omega` elaborates to plain `Nat` arithmetic).
-/

namespace Codec

open List

/-! ## The byte-level encoder -/

/-- LEB128 encode: the low 7 bits of each byte carry a base-128 digit
(little-endian); every byte except the last has the continuation bit (`bit 7`) set.
Well-founded recursion on `n` via `n / 128 < n` (for `n > 0`), so `0` is the base
case `[0]` and `n ≥ 128` prepends `(n % 128) + 128` before the encoding of
`n / 128`. -/
def varintBytes (n : Nat) : List UInt8 :=
  let q := n / 128
  let r := n % 128
  let b : UInt8 := UInt8.ofNat r
  if q = 0 then [b] else (b + 128) :: varintBytes q
termination_by n
decreasing_by
  simp_wf
  exact Nat.div_lt_self (by omega) (by decide)

/-! ## The byte-level decoder -/

/-- One LEB128 read step, threading an accumulator `acc : Nat` (the value of the
already-read prefix) and `mult : Nat` (the place value of the next digit, a power
of 128). Returns `(value, remaining-bytes)`; `none` on an empty or overlong
input. A terminating byte may be `0` only at place value `1` (the canonical `[0]`);
anywhere else a `0` digit is an overlong encoding and is rejected. -/
def varintDecodeStep (acc : Nat) (mult : Nat) : List UInt8 → Option (Nat × List UInt8)
  | [] => none
  | b :: rest =>
      let v := b.toNat
      if v < 128 then
        if v = 0 ∧ mult > 1 then none else some (acc + v * mult, rest)
      else
        varintDecodeStep (acc + (v - 128) * mult) (mult * 128) rest

/-- The LEB128 decode of a whole byte string: `some n` exactly when `bs` is the
canonical encoding of `n` (minimal, no trailing bytes). -/
def varintUnapply (bs : List UInt8) : Option Nat :=
  match varintDecodeStep 0 1 bs with
  | some (n, []) => some n
  | _ => none

/-! ## Arithmetic and byte lemmas -/

/-- `(ofNat r + 128).toNat = r + 128` for a data digit `r < 128` (the `+ 128`
wraps mod `2^8`, but `r + 128 < 256`). -/
theorem byte_cont (r : Nat) (hr : r < 128) : (UInt8.ofNat r + 128).toNat = r + 128 := by
  rw [show (UInt8.ofNat r + 128).toNat = ((UInt8.ofNat r).toBitVec + (128 : UInt8).toBitVec).toNat by rfl]
  rw [show (128 : UInt8).toBitVec = BitVec.ofNat 8 128 by rfl]
  rw [show (UInt8.ofNat r).toBitVec = BitVec.ofNat 8 r by rfl]
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : r < 256)]
  rw [Nat.mod_eq_of_lt (by omega : r + 128 < 256)]

/-- `varintBytes (r + 128 * n') = (ofNat r + 128) :: varintBytes n'` for a data
digit `r < 128` and a non-zero consumer `n' > 0` — the encode's `cons` step. -/
theorem enc_cons (r n' : Nat) (hrl : r < 128) (hn' : n' > 0) :
    varintBytes (r + 128 * n') = (UInt8.ofNat r + 128) :: varintBytes n' := by
  rw [varintBytes.eq_def]
  have hq : (r + 128 * n') / 128 = n' := by
    rw [Nat.add_mul_div_left r n' (by decide)]
    rw [Nat.div_eq_of_lt hrl] <;> simp
  rw [hq]
  have hr' : (r + 128 * n') % 128 = r := by
    rw [Nat.add_mul_mod_self_left r 128 n']
    rw [Nat.mod_eq_of_lt hrl]
  rw [hr']
  have hn'ne : n' ≠ 0 := by omega
  simp [hn'ne]

/-- `varintBytes v = [ofNat v]` for a single-digit value `v < 128`. -/
theorem enc_single (v : Nat) (hv : v < 128) : varintBytes v = [UInt8.ofNat v] := by
  rw [varintBytes.eq_def]
  have hq : v / 128 = 0 := Nat.div_eq_of_lt hv
  have hr : v % 128 = v := Nat.mod_eq_of_lt hv
  simp [hq, hr]

/-- Decoding a leading zero byte at place value `> 1` is impossible (overlong). -/
theorem decode_zero_none (acc mult : Nat) (tail : List UInt8) (hmult : 1 < mult) :
    varintDecodeStep acc mult ((0 : UInt8) :: tail) = none := by
  simp [varintDecodeStep, hmult]

/-- The accumulator merge for the *forward* (decode ∘ encode) proof. -/
theorem merge_arith (acc n mult : Nat) :
    acc + n % 128 * mult + n / 128 * (mult * 128) = acc + n * mult := by
  have hmd : n % 128 + 128 * (n / 128) = n := Nat.mod_add_div n 128
  calc
    acc + n % 128 * mult + n / 128 * (mult * 128)
        = acc + mult * (n % 128) + mult * (128 * (n / 128)) := by ac_rfl
    _ = acc + (mult * (n % 128) + mult * (128 * (n / 128))) := by ac_rfl
    _ = acc + mult * (n % 128 + 128 * (n / 128)) := by rw [Nat.mul_add]
    _ = acc + mult * n := by rw [hmd]
    _ = acc + n * mult := by ac_rfl

/-- The accumulator merge for the *backward* (encode ∘ decode) proof. -/
theorem merge_arith_back (acc A n' mult : Nat) :
    acc + A * mult + n' * (mult * 128) = acc + (A + 128 * n') * mult := by
  rw [Nat.add_mul]
  ac_rfl

/-! ## The roundtrip -/

/-- **Forward direction** (`dec_enc`): decoding a canonical encoding reconstructs
the value, for `n > 0` (the `n = 0` case is `[0]`, handled by `varintUnapply`'s
base). Generalized over the accumulator/place-value so the induction can recurse
on the shrunk `n / 128`. -/
theorem dec_enc (n : Nat) (hn : n > 0) :
    ∀ (acc mult : Nat), varintDecodeStep acc mult (varintBytes n) = some (acc + n * mult, []) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      intro acc mult
      rw [varintBytes.eq_def]
      by_cases hq : n / 128 = 0
      · have hnlt : n < 128 := by omega
        have hne : n ≠ 0 := by omega
        simp [hq, varintDecodeStep]
        rw [Nat.mod_eq_of_lt (by omega : n % 128 < 256)]
        rw [show n % 128 = n by omega]
        simp [hnlt, hne]
      · have hqgt : n / 128 > 0 := Nat.pos_of_ne_zero hq
        have hlt : n / 128 < n := Nat.div_lt_self (by omega) (by decide)
        simp [hq, varintDecodeStep]
        rw [Nat.mod_eq_of_lt (by omega : n % 128 + 128 < 256)]
        simp [show ¬ (n % 128 + 128 < 128) by omega]
        rw [ih (n / 128) hlt hqgt (acc + n % 128 * mult) (mult * 128)]
        rw [merge_arith]

/-- **Backward direction** (`enc_dec`): a successful decode step reconstructs a
canonical prefix `varintBytes n` in front of the remaining tail, with the value
`n` uniquely pinned by `m = acc + n * mult`. Generalized over the base `acc`/`mult`
(`0 < mult` — a power of 128 — keeps the reconstruction injective). -/
theorem enc_dec (bs : List UInt8) :
    ∀ (acc mult m : Nat) (tail : List UInt8), 0 < mult →
      varintDecodeStep acc mult bs = some (m, tail) →
      ∃ n, m = acc + n * mult ∧ bs = varintBytes n ++ tail := by
  induction bs with
  | nil => intro acc mult m tail _hpos h; simp [varintDecodeStep] at h
  | cons b rest ih =>
      intro acc mult m tail hpos h
      simp [varintDecodeStep] at h
      by_cases hvlt : b.toNat < 128
      · have hnotover : ¬ (b.toNat = 0 ∧ mult > 1) := by
          intro h0
          simp [h0.1, h0.2] at h
        simp [hvlt, hnotover] at h
        rcases h with ⟨hm, htail⟩
        refine ⟨b.toNat, ?_, ?_⟩
        · exact hm.symm
        · rw [htail]
          rw [enc_single b.toNat hvlt]
          rw [UInt8.ofNat_toNat]
          rfl
      · have hvge : 128 ≤ b.toNat := by omega
        have hb256 : b.toNat < 256 := UInt8.toNat_lt_size b
        simp [hvlt] at h
        have hh := ih (acc + (b.toNat - 128) * mult) (mult * 128) m tail (by omega) h
        rcases hh with ⟨n', hmn', hrest⟩
        have hn'gt : n' > 0 := by
          by_cases hn'0 : n' = 0
          · subst n'
            rw [hrest] at h
            rw [enc_single 0 (by decide)] at h
            rw [show UInt8.ofNat 0 = (0 : UInt8) by decide] at h
            change varintDecodeStep (acc + (b.toNat - 128) * mult) (mult * 128) ((0 : UInt8) :: tail) = some (m, tail) at h
            have hnm := decode_zero_none (acc + (b.toNat - 128) * mult) (mult * 128) tail (by omega)
            rw [hnm] at h
            cases h
          · omega
        refine ⟨(b.toNat - 128) + 128 * n', ?_, ?_⟩
        · rw [hmn']
          rw [merge_arith_back]
        · rw [hrest]
          rw [enc_cons (b.toNat - 128) n' (by omega) hn'gt]
          apply congrArg (fun x => x :: (varintBytes n' ++ tail))
          apply UInt8.toNat.inj
          rw [byte_cont (b.toNat - 128) (by omega)]
          omega

/-- `varintUnapply (varintBytes n) = some n` — decode ∘ encode. -/
theorem varintUnapply_enc (n : Nat) : varintUnapply (varintBytes n) = some n := by
  by_cases hn : n = 0
  · subst n
    rw [varintBytes.eq_def]
    simp [varintUnapply, varintDecodeStep]
  · have hnpos : n > 0 := Nat.pos_of_ne_zero hn
    have h := dec_enc n hnpos 0 1
    rw [varintUnapply]
    rw [h]
    simp

/-- `varintUnapply bs = some n → varintBytes n = bs` — encode ∘ decode. -/
theorem varintUnapply_inj (bs : List UInt8) (n : Nat) (h : varintUnapply bs = some n) :
    varintBytes n = bs := by
  rw [varintUnapply] at h
  cases hd : varintDecodeStep 0 1 bs with
  | none => simp [hd] at h
  | some pr =>
      rcases pr with ⟨m, tail⟩
      simp [hd] at h
      by_cases htail : tail = []
      · rw [htail] at h
        simp at h
        subst n
        have hh := enc_dec bs 0 1 m [] (by decide) (by simpa [hd])
        rcases hh with ⟨n', hm', hbs⟩
        rw [show 0 + n' * 1 = n' by omega] at hm'
        subst n'
        simpa using hbs.symm
      · simp [htail] at h

/-! ## The `varint` partial isomorphism -/

/-- The LEB128 varint as a `Nat`-vs-`Bytes` partial isomorphism: `apply` is the
encode, `unapply` the (minimal, canonical) decode, and the inverse law is the
LEB128 roundtrip proved once, `[propext, Quot.sound]`-only. -/
def varint : Iso Nat (List UInt8) where
  apply n := some (varintBytes n)
  unapply bs := varintUnapply bs
  law := by
    intro n bs
    constructor
    · intro h
      have hb : varintBytes n = bs := by simpa using h
      rw [← hb]
      exact varintUnapply_enc n
    · intro h
      have hb := varintUnapply_inj bs n h
      rw [hb]

/-! ## The `ByteArray`-carrier varbinary run-model

The motivating hot path: the same LEB128 read/write over the packed `ByteArray`
carrier (`a.data[i]` / `ByteArray.mk`), tied to the `varint` spec above through the
carrier equality. `encodeVarint` builds the packed bytes in one `mk`; `decodeVarint a i`
reads one canonical varint starting at absolute index `i` and returns the (unique)
`value` — an `Option`, because the varint is unambiguous: the single result is
structural (at most one), not a prose claim over a list. The consumed length is
recoverable as `(varintBytes n).length`. -/

/-- The packed LEB128 encode: `n` as a single `ByteArray` (`ByteArray.mk` over the
`varintBytes` list-encode, one materialization — no per-byte `push`). -/
def encodeVarint (n : Nat) : ByteArray := ByteArray.mk (varintBytes n).toArray

/-- `encodeVarint` agrees with the `varint` spec (`apply`): the packed bytes are
exactly `varintBytes n`. Reducible through `ByteArray.data`/`Array.toList` (never the
opaque `ByteArray.toList`). -/
theorem encodeVarint_eq (n : Nat) : (encodeVarint n).data.toList = varintBytes n := rfl

/-- The packed LEB128 decode: read one canonical varint starting at index `i` of the
packed buffer, returning the `value` (or `none` on an empty/overlong prefix). Composed
over the `varint` spec's `varintUnapply` on the dropped suffix. The `Option` carrier
makes the unambiguous single result structural. -/
def decodeVarint (a : ByteArray) (i : Nat) : Option Nat :=
  varintUnapply (a.data.toList.drop i)

/-- The carrier refinement: `decodeVarint a i = some n` iff the dropped suffix is the
canonical `varintBytes n` (i.e. `varintUnapply (drop i) = some n`). The consumed length
is then `(varintBytes n).length`. -/
theorem decodeVarint_eq (a : ByteArray) (i : Nat) (n : Nat) :
    decodeVarint a i = some n ↔ varintUnapply (a.data.toList.drop i) = some n := by
  rfl

/-- The packed LEB128 roundtrip: `decodeVarint (encodeVarint n) 0` yields the
original `n` (optionally), at the canonical consumed length `(varintBytes n).length`. -/
theorem roundtripVarint (n : Nat) :
    decodeVarint (encodeVarint n) 0 = some n := by
  rw [decodeVarint]
  rw [encodeVarint_eq]
  simp
  rw [varintUnapply_enc n]

end Codec
