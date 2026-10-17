/- Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later -/

import Codec.Codec
import Codec.Iso

/-!
# LEB128 varbinary over the length-indexed byte string

The LEB128 varint re-based onto the single length-indexed carrier
`Bytes k := Fin k → UInt8`. LEB128 is byte-aligned 7-bits-per-byte with a
continuation high bit: the low 7 bits of each byte are a base-128 digit
(little-endian), and every byte except the last has bit 7 set. `0` encodes to
the single byte `[0]`; `128` to `[0x80, 0x01]`; `300` to `[0xAC, 0x02]`.

The *spec* is the partial isomorphism `varint : Iso Nat (Sigma fun k => Bytes k)`:
`apply` is the canonical little-endian encode returning the bytes together with
their length, and `unapply` is the (minimal, canonical) decode. The inverse law is
the LEB128 roundtrip proved once below, `[propext, Quot.sound]`-only (no
`Classical`, no `omega` axioms — `omega` elaborates to plain `Nat` arithmetic).

There is **one** byte-string carrier: the encoded/decoded bytes are `Bytes k`.
No `List UInt8` spec and no `ByteArray`/`Array`/`Buffer` run-model remain.
-/

namespace Codec

/-! ## The byte-level encoder -/

/-- LEB128 encode: the low 7 bits of each byte carry a base-128 digit
(little-endian); every byte except the last has the continuation bit (`bit 7`) set.
Well-founded recursion on `n` via `n / 128 < n` (for `n > 0`), so `n < 128` is the
base case (the single byte `ofNat n`) and `n ≥ 128` prepends the continuation byte
`(n % 128) + 128` before the encoding of `n / 128`. Returns the byte string and its
length in one `Sigma`. -/
def varintBytes (n : Nat) : Sigma fun k => Bytes k :=
  let q := n / 128
  let r := n % 128
  let b : UInt8 := UInt8.ofNat r
  if _hq : q = 0 then ⟨1, single b⟩
  else
    let ⟨k, rest⟩ := varintBytes q
    ⟨1 + k, concat (single (b + 128)) rest⟩
termination_by n
decreasing_by
  simp_wf
  exact Nat.div_lt_self (by omega) (by decide)

/-! ## The byte-level decoder -/

/-- One LEB128 decode, threading an accumulator `acc : Nat` (the value of the
already-read prefix) and `mult : Nat` (the place value of the next digit, a power
of 128). Reads the first byte of `bs : Bytes k`, recursing on `bdrop 1 bs` while
the continuation bit is set. Returns `(value, remaining-bytes)`; `none` on an
empty or overlong input. A terminating byte may be `0` only at place value `1`
(the canonical `[0]`); anywhere else a `0` digit is an overlong encoding and is
rejected. -/
def varintDecodeStep (acc : Nat) (mult : Nat) {k : Nat} (bs : Bytes k) :
    Option (Nat × Sigma fun m => Bytes m) :=
  if h : k = 0 then none
  else
    let b := bs ⟨0, Nat.pos_of_ne_zero h⟩
    let v := b.toNat
    if v < 128 then
      if v = 0 ∧ mult > 1 then none
      else some (acc + v * mult, ⟨k - 1, bdrop 1 bs⟩)
    else
      varintDecodeStep (acc + (v - 128) * mult) (mult * 128) (bdrop 1 bs)
termination_by k
decreasing_by
  simp_wf
  omega

/-- The LEB128 decode of a whole byte string: `some n` exactly when `bs` is the
canonical encoding of `n` (minimal, no trailing bytes). -/
def varintUnapply (bs : Sigma fun k => Bytes k) : Option Nat :=
  match varintDecodeStep 0 1 bs.2 with
  | some (n, ⟨0, _⟩) => some n
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

/-- `varintBytes (r + 128 * n')` is the continuation byte `ofNat r + 128` followed
by `varintBytes n'`, for a data digit `r < 128` and a non-zero consumer `n' > 0`. -/
theorem enc_cons (r n' : Nat) (hrl : r < 128) (hn' : n' > 0) :
    varintBytes (r + 128 * n') =
      ⟨1 + (varintBytes n').1, concat (single (UInt8.ofNat r + 128)) (varintBytes n').2⟩ := by
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

/-- `varintBytes v = ⟨1, single (ofNat v)⟩` for a single-digit value `v < 128`. -/
theorem enc_single (v : Nat) (hv : v < 128) : varintBytes v = ⟨1, single (UInt8.ofNat v)⟩ := by
  rw [varintBytes.eq_def]
  have hq : v / 128 = 0 := Nat.div_eq_of_lt hv
  have hr : v % 128 = v := Nat.mod_eq_of_lt hv
  simp [hq, hr]

/-! ## Substrate lemmas for the `Bytes`-carrier roundtrip -/

/-- The length cast `(1 + m) - 1 = m` used to recover the tail of a `concat`.
`[propext, Quot.sound]`-only. -/
theorem bdrop_concat_len (m : Nat) : (1 + m) - 1 = m := by omega

/-- Dropping the single continuation byte off `concat (single b) rest` recovers
`rest` (up to the length cast `(1 + m) - 1 = m`). `[propext, Quot.sound]`-only. -/
theorem bdrop_one_concat {m : Nat} (b : UInt8) (rest : Bytes m) :
    bdrop 1 (concat (single b) rest) = cast (congrArg Bytes (bdrop_concat_len m).symm) rest := by
  apply Bytes.ext
  intro i
  simp [bdrop, concat]

/-- Reading the head of a `concat` whose first byte is `single b` gives `b` back.
`[propext, Quot.sound]`-only. -/
theorem concat_head {m : Nat} (b : UInt8) (rest : Bytes m) :
    (concat (single b) rest) (⟨0, by omega⟩ : Fin (1 + m)) = b := by
  simp [concat, single]

/-- Reconstruct a length-`k+1` byte string as its first byte followed by the rest
(up to the length cast `(k + 1) = 1 + ((k+1) - 1)`). `[propext, Quot.sound]`-only. -/
theorem concat_bdrop_one {k : Nat} (bs : Bytes (k + 1)) :
    bs = cast (congrArg Bytes (by omega : (k + 1) = 1 + ((k + 1) - 1)).symm)
          (concat (single (bs ⟨0, Nat.zero_lt_succ k⟩)) (bdrop 1 bs)) := by
  apply Bytes.ext
  intro i
  rw [cast_bytes_val' (e := (by omega : (k + 1) = 1 + ((k+1) - 1)).symm)]
  unfold concat
  by_cases hi : i.val = 0
  · have h0 : i = ⟨0, by omega⟩ := by apply Fin.ext; omega
    rw [h0]
    simp [single]
  · have hge : i.val ≥ 1 := by omega
    have hlt : i.val - 1 < k := by omega
    have hnot : ¬ i.val < 1 := by omega
    simp [hnot, bdrop]
    apply congrArg bs
    apply Fin.ext
    simpa using (Nat.sub_add_cancel hge).symm

/-- Dropping the single byte of `single b` yields the empty byte string.
`[propext, Quot.sound]`-only. -/
theorem bdrop_one_single (b : UInt8) : bdrop 1 (single b) = (emptyBytes : Bytes 0) := by
  apply Bytes.ext
  intro i
  exact Fin.elim0 i

/-- `varintDecodeStep` is insensitive to a length-cast of its input when the
result has an empty remainder (so only the input length is transported).
`[propext, Quot.sound]`-only. -/
theorem varintDecodeStep_cast_empty {k k' : Nat} (e : k = k') (acc mult m : Nat) (bs : Bytes k) :
    varintDecodeStep acc mult (cast (congrArg Bytes e) bs) = some (m, ⟨0, emptyBytes⟩) ↔
    varintDecodeStep acc mult bs = some (m, ⟨0, emptyBytes⟩) := by
  cases e
  rfl

/-- Decoding a leading zero byte at place value `> 1` is impossible (overlong). -/
theorem decode_zero_none (acc mult : Nat) {k : Nat} (tail : Bytes k) (hmult : 1 < mult) :
    varintDecodeStep acc mult (concat (single (0 : UInt8)) tail) = none := by
  rw [varintDecodeStep.eq_def]
  simp [hmult, concat_head (0 : UInt8) tail]

/-- The single overlong encoding: decoding `single 0` at place value `> 1` is
impossible. `[propext, Quot.sound]`-only. -/
theorem decode_zero_single (acc mult : Nat) (hmult : 1 < mult) :
    varintDecodeStep acc mult (single (0 : UInt8)) = none := by
  rw [varintDecodeStep.eq_def]
  simp [single, hmult]

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
the value and consumes every byte, for `n > 0` (the `n = 0` case is `⟨1, [0]⟩`,
handled by `varintUnapply`). Generalized over the accumulator/place-value so the
induction can recurse on the shrunk `n / 128`. -/
theorem dec_enc (n : Nat) (hn : n > 0) :
    ∀ (acc mult : Nat), varintDecodeStep acc mult (varintBytes n).2 = some (acc + n * mult, ⟨0, emptyBytes⟩) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      intro acc mult
      by_cases hq : n / 128 = 0
      · have hnlt : n < 128 := by omega
        rw [enc_single n hnlt]
        rw [varintDecodeStep.eq_def]
        simp [single]
        rw [Nat.mod_eq_of_lt (by omega : n < 256)]
        have hne : n ≠ 0 := by omega
        simp [hnlt, hne]
        rw [bdrop_one_single (UInt8.ofNat n)]
      · have hqgt : n / 128 > 0 := Nat.pos_of_ne_zero hq
        have hlt : n / 128 < n := Nat.div_lt_self (by omega) (by decide)
        rw [show n = n % 128 + 128 * (n / 128) by omega]
        rw [enc_cons (n % 128) (n / 128) (by omega) hqgt]
        rw [varintDecodeStep.eq_def]
        simp
        rw [concat_head (UInt8.ofNat (n % 128) + 128) (varintBytes (n / 128)).2]
        rw [byte_cont (n % 128) (by omega)]
        have hge : ¬ (n % 128 + 128 < 128) := by omega
        simp [hge]
        rw [bdrop_one_concat (UInt8.ofNat (n % 128) + 128) (varintBytes (n / 128)).2]
        rw [varintDecodeStep_cast_empty]
        · rw [ih (n / 128) hlt hqgt (acc + n % 128 * mult) (mult * 128)]
          congr 1
          apply Prod.ext
          · rw [Nat.add_mul]
            ac_rfl
          · rfl
        · omega

/-- **Backward direction** (`enc_dec`): a successful decode of a whole byte string
reconstructs the canonical `varintBytes n`, with the value uniquely pinned.
Specialized to the empty-remainder result (the case `varintUnapply_inj` needs). -/
theorem enc_dec {k : Nat} (bs : Bytes k) :
    ∀ acc mult m, 0 < mult →
      varintDecodeStep acc mult bs = some (m, ⟨0, emptyBytes⟩) →
      ∃ n, m = acc + n * mult ∧ (⟨k, bs⟩ : Sigma fun c => Bytes c) = varintBytes n := by
  induction k with
  | zero =>
      intro acc mult m _hpos h
      rw [varintDecodeStep.eq_def] at h
      simp at h
  | succ k' ih =>
      intro acc mult m hpos h
      rw [varintDecodeStep.eq_def] at h
      let b : UInt8 := bs 0
      have hb : b = bs 0 := rfl
      dsimp [b] at h
      simp at h
      by_cases hvlt : b.toNat < 128
      · dsimp [b] at hvlt
        by_cases hov : b.toNat = 0 ∧ mult > 1
        · -- overlong: decode returns none, contradicting `h`
          dsimp [b] at hov
          exfalso
          simp [hov.1, hov.2] at h
        · -- non-overlong: `hov : ¬ (b.toNat = 0 ∧ mult > 1)`
          dsimp [b] at hov hvlt
          simp [hvlt] at h
          rcases h with ⟨_hneq, hm, hk0, _htail⟩
          refine ⟨b.toNat, ?_, ?_⟩
          · exact hm.symm
          · subst k'
            rw [enc_single b.toNat hvlt]
            congr 1
            apply Bytes.ext
            intro i
            simp [single, UInt8.ofNat_toNat]
            have : i = (0 : Fin 1) := by apply Fin.ext; omega
            rw [this]
      · have hvge : 128 ≤ b.toNat := by omega
        have hb256 : b.toNat < 256 := UInt8.toNat_lt_size b
        dsimp [b] at hvlt
        simp [hvlt] at h
        have hih := ih (bdrop 1 bs) (acc + (b.toNat - 128) * mult) (mult * 128) m (by omega) h
        rcases hih with ⟨n', hmn', hrest⟩
        have hn'gt : n' > 0 := by
          by_cases hn'0 : n' = 0
          · subst n'
            rw [enc_single 0 (by decide)] at hrest
            have hk1 : k' = 1 := (Sigma.mk.inj hrest).1
            subst hk1
            have hb0 : bdrop 1 bs = single (0 : UInt8) := by
              exact eq_of_heq ((Sigma.mk.inj hrest).2)
            have hnone : varintDecodeStep (acc + (b.toNat - 128) * mult) (mult * 128) (single (0 : UInt8)) = none :=
              decode_zero_single (acc + (b.toNat - 128) * mult) (mult * 128) (by omega)
            rw [hb0] at h
            rw [hnone] at h
            simp at h
          · omega
        refine ⟨(b.toNat - 128) + 128 * n', ?_, ?_⟩
        · rw [hmn']
          rw [merge_arith_back]
        · rw [enc_cons (b.toNat - 128) n' (by omega) hn'gt]
          have hk' : k' = (varintBytes n').1 := (Sigma.mk.inj hrest).1
          subst hk'
          let hlen : (varintBytes n').fst + 1 = 1 + (varintBytes n').fst := by omega
          apply Sigma.ext (by exact hlen)
          have hb' : b = UInt8.ofNat (b.toNat - 128) + 128 := by
            apply UInt8.toNat.inj
            rw [byte_cont (b.toNat - 128) (by omega)]
            omega
          have hbs' : bdrop 1 bs = (varintBytes n').2 := by
            exact eq_of_heq ((Sigma.mk.inj hrest).2)
          have hconcat : concat (single (bs ⟨0, Nat.zero_lt_succ (varintBytes n').fst⟩)) (bdrop 1 bs) =
              concat (single (UInt8.ofNat (b.toNat - 128) + 128)) (varintBytes n').2 := by
            set_option maxRecDepth 10000 in
            rw [hbs']
            congr 1
            exact congrArg single (by simpa [b] using hb')
          have hcast : bs = cast (congrArg Bytes hlen.symm)
              (concat (single (UInt8.ofNat (b.toNat - 128) + 128)) (varintBytes n').2) := by
            set_option maxRecDepth 10000 in
            rw [concat_bdrop_one bs]
            rw [hconcat]
          exact (heq_of_eq hcast).trans
            (cast_heq (congrArg Bytes hlen.symm)
              (concat (single (UInt8.ofNat (b.toNat - 128) + 128)) (varintBytes n').2))

/-- `varintUnapply (varintBytes n) = some n` — decode ∘ encode. -/
theorem varintUnapply_enc (n : Nat) : varintUnapply (varintBytes n) = some n := by
  by_cases hn : n = 0
  · subst n
    rw [varintUnapply]
    rw [enc_single 0 (by decide)]
    rw [varintDecodeStep.eq_def]
    simp [single]
  · have hnpos : n > 0 := Nat.pos_of_ne_zero hn
    have h := dec_enc n hnpos 0 1
    rw [varintUnapply]
    rw [h]
    simp

/-- `varintUnapply bs = some n → varintBytes n = bs` — encode ∘ decode. -/
theorem varintUnapply_inj (bs : Sigma fun k => Bytes k) (n : Nat) (h : varintUnapply bs = some n) :
    varintBytes n = bs := by
  rw [varintUnapply] at h
  cases hd : varintDecodeStep 0 1 bs.2 with
  | none => simp [hd] at h
  | some pr =>
      rcases pr with ⟨m, tail⟩
      simp [hd] at h
      cases tail with
      | mk q tq =>
          by_cases hq : q = 0
          · subst q
            have : m = n := by simpa using h
            subst m
            have htq : tq = emptyBytes := by
              funext i
              exact Fin.elim0 i
            subst tq
            have hh := enc_dec bs.2 0 1 n (by decide) (by simp [hd])
            rcases hh with ⟨n', hmn', hrest⟩
            have hn' : n' = n := by
              rw [hmn']
              omega
            subst n'
            change varintBytes n = ⟨bs.1, bs.2⟩
            rw [hrest]
          · simp [hq] at h

/-! ## The `varint` partial isomorphism -/

/-- The LEB128 varint as a `Nat`-vs-length-indexed-`Bytes` partial isomorphism:
`apply` is the encode, `unapply` the (minimal, canonical) decode, and the inverse
law is the LEB128 roundtrip proved once, `[propext, Quot.sound]`-only. -/
def varint : Iso Nat (Sigma fun k => Bytes k) where
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

/-! ## The `Bytes`-carrier varbinary run-model

The LEB128 read/write over the single length-indexed carrier. `encodeVarint n`
returns the encoded bytes and their length (a `Sigma`); `decodeVarint bs` decodes
one canonical varint from a whole byte string, returning the (unique) value —
an `Option`, because the varint is unambiguous. There is no transfer to a
`ByteArray`/`Array`/`Buffer` carrier; the packed run-model *is* `Bytes k`. -/

/-- The LEB128 encode of `n` as a length-indexed byte string. -/
def encodeVarint (n : Nat) : Sigma fun k => Bytes k := varintBytes n

/-- `encodeVarint` agrees with the `varint` spec (`apply`): the encoded bytes are
exactly `varintBytes n`. Reducible through the `Bytes` carrier. -/
theorem encodeVarint_eq (n : Nat) : encodeVarint n = varintBytes n := rfl

/-- The LEB128 decode of a whole byte string: `some n` exactly when `bs` is the
canonical encoding of `n`. -/
def decodeVarint (bs : Sigma fun k => Bytes k) : Option Nat := varintUnapply bs

/-- The carrier refinement: `decodeVarint bs = some n` iff the whole byte string is
the canonical `varintBytes n`. -/
theorem decodeVarint_eq (bs : Sigma fun k => Bytes k) (n : Nat) :
    decodeVarint bs = some n ↔ varintUnapply bs = some n := by
  rfl

/-- The LEB128 roundtrip: `decodeVarint (encodeVarint n)` yields the original `n`. -/
theorem roundtripVarint (n : Nat) :
    decodeVarint (encodeVarint n) = some n := by
  rw [decodeVarint, encodeVarint_eq]
  exact varintUnapply_enc n

end Codec
