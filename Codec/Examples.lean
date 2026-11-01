/- Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later -/

import Codec.Sound
import Codec.Packed

/-!
# Worked leaf codecs — inhabitation witnesses, not a format library

`README.md` `[S3]` says core ships **zero** concrete formats: every format lives
downstream (`lean-binary`, `lean-text`). That rule is kept. This file is not a
format library and is not part of the `codec` contract — it is the **worked
example** the README lacked, and its job is narrower and sharper than "ship `u16le`":

1. **Inhabitation.** The library's whole-buffer machinery
   (`ConsumesByte`, `decodeFull`/`decodeWhole`, `decodeWholeOne`) was previously
   instantiated at exactly one codec, `Codec.byte`, whose decode has one candidate
   per position and no composition. Nothing proved the machinery *works* on a
   description built from `iso` and `seq`. Each codec here is that witness.
2. **A copy-paste recipe.** A downstream author defining their first leaf had no
   in-tree pattern; the `Iso` law had to be filled by hand. These show the intended
   shape, using `Iso.ofTotal` so the `↔` is discharged by two round-trip equations.

Every codec here is fully proved: zero `sorry`, zero `Classical.choice`, and its
laws report `[propext, Quot.sound]`-only.

**What is deliberately absent.** No `varint`, no `utf8`, no length-prefixed or
tagged-sum formats. Those exercise corners (`alt` with *unequal* branch lengths,
which is where `huniq` stops being derivable) that need a proof result this file
cannot supply by example — the honest place for them is a spec change, not a
"miscellaneous examples" module. Naming them here is a record that they are
*known* and *not* covered, so a reader does not mistake coverage for completeness.
-/

namespace Codec.Examples

open Codec

/-! ## `u8` — the degenerate leaf

`u8` is literally `Codec.byte`; it exists as a named definition only so the
downstream naming convention starts here and so its `ConsumesByte` witness has a
name. -/

/-- An unsigned 8-bit value: the primitive, named. -/
abbrev u8 : Codec UInt8 := Codec.byte

/-- `u8` is productive — re-exported under the format name. -/
theorem u8ConsumesByte : ConsumesByte u8 := byteConsumesByte

/-! ## `u16le` / `u16be` — the first composed leaf codecs -/

/-- Little-endian: the low byte first. -/
def u16leRead (p : UInt8 × UInt8) : UInt16 :=
  UInt16.ofNat (p.1.toNat + 256 * p.2.toNat)

/-- The little-endian pair for a value: `(v % 256, v / 256)`. -/
def u16leWrite (v : UInt16) : UInt8 × UInt8 :=
  (UInt8.ofNat (v.toNat % 256), UInt8.ofNat (v.toNat / 256))

/-- **The round trip that discharges `u16le`'s `Iso` law, direction 1.** Reading
back what we wrote recovers the value. -/
theorem u16leRead_write (v : UInt16) : u16leRead (u16leWrite v) = v := by
  have hlt := UInt16.toNat_lt v
  show UInt16.ofNat ((UInt8.ofNat (v.toNat % 256)).toNat
    + 256 * (UInt8.ofNat (v.toNat / 256)).toNat) = v
  rw [UInt8.toNat_ofNat', UInt8.toNat_ofNat',
      Nat.mod_eq_of_lt (by omega : v.toNat % 256 < 256),
      Nat.mod_eq_of_lt (by omega : v.toNat / 256 < 256)]
  rw [Nat.mod_add_div v.toNat 256]
  exact UInt16.ofNat_toNat

/-- **Direction 2**: every 2-byte pair is the canonical pair of exactly one value,
so writing back what we read recovers the pair. -/
theorem u16leWrite_read (p : UInt8 × UInt8) : u16leWrite (u16leRead p) = p := by
  obtain ⟨lo, hi⟩ := p
  have hlo : lo.toNat < 256 := UInt8.toNat_lt _
  have hhi : hi.toNat < 256 := UInt8.toNat_lt _
  show u16leWrite (UInt16.ofNat (lo.toNat + 256 * hi.toNat)) = (lo, hi)
  unfold u16leWrite
  have hb : (UInt16.ofNat (lo.toNat + 256 * hi.toNat)).toNat = lo.toNat + 256 * hi.toNat := by
    rw [UInt16.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  rw [hb]
  have h1 : (lo.toNat + 256 * hi.toNat) % 256 = lo.toNat := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlo]
  have h2 : (lo.toNat + 256 * hi.toNat) / 256 = hi.toNat := by
    rw [Nat.add_mul_div_left lo.toNat hi.toNat (by decide : 0 < 256),
        Nat.div_eq_of_lt hlo, Nat.zero_add]
  rw [h1, h2, UInt8.ofNat_toNat, UInt8.ofNat_toNat]

/-- **`u16le`: two bytes, little-endian, as an `Iso`.** Note the shape a downstream
author needs — `Iso.ofTotal` plus two round-trip equations, no hand-written `↔`. -/
def u16leIso : Iso (UInt8 × UInt8) UInt16 :=
  Iso.ofTotal u16leRead u16leWrite u16leWrite_read u16leRead_write

/-- **A little-endian 16-bit unsigned integer.** -/
def u16le : Codec UInt16 := Codec.iso u16leIso (Codec.seq Codec.byte Codec.byte)

/-- `u16le` is productive — **derived**, via the two new composition witnesses.
Before `seqConsumesByte`/`isoConsumesByte` existed this had to be proved by hand. -/
theorem u16leConsumesByte : ConsumesByte u16le :=
  isoConsumesByte u16leIso (Codec.seq Codec.byte Codec.byte)
    (seqConsumesByte Codec.byte Codec.byte byteConsumesByte byteConsumesByte)

/-- Big-endian: the high byte first. -/
def u16beRead (p : UInt8 × UInt8) : UInt16 :=
  UInt16.ofNat (p.2.toNat + 256 * p.1.toNat)

/-- The big-endian pair for a value. -/
def u16beWrite (v : UInt16) : UInt8 × UInt8 :=
  (UInt8.ofNat (v.toNat / 256), UInt8.ofNat (v.toNat % 256))

theorem u16beRead_write (v : UInt16) : u16beRead (u16beWrite v) = v := by
  have hlt := UInt16.toNat_lt v
  show UInt16.ofNat ((UInt8.ofNat (v.toNat % 256)).toNat
    + 256 * (UInt8.ofNat (v.toNat / 256)).toNat) = v
  rw [UInt8.toNat_ofNat', UInt8.toNat_ofNat',
      Nat.mod_eq_of_lt (by omega : v.toNat % 256 < 256),
      Nat.mod_eq_of_lt (by omega : v.toNat / 256 < 256),
      Nat.add_comm]
  have h : 256 * (v.toNat / 256) + v.toNat % 256 = v.toNat :=
    Nat.div_add_mod v.toNat 256
  rw [h]
  exact UInt16.ofNat_toNat

theorem u16beWrite_read (p : UInt8 × UInt8) : u16beWrite (u16beRead p) = p := by
  obtain ⟨hi, lo⟩ := p
  have hlo : lo.toNat < 256 := UInt8.toNat_lt _
  have hhi : hi.toNat < 256 := UInt8.toNat_lt _
  show u16beWrite (UInt16.ofNat (lo.toNat + 256 * hi.toNat)) = (hi, lo)
  unfold u16beWrite
  have hb : (UInt16.ofNat (lo.toNat + 256 * hi.toNat)).toNat = lo.toNat + 256 * hi.toNat := by
    rw [UInt16.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  rw [hb]
  have h1 : (lo.toNat + 256 * hi.toNat) % 256 = lo.toNat := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlo]
  have h2 : (lo.toNat + 256 * hi.toNat) / 256 = hi.toNat := by
    rw [Nat.add_mul_div_left lo.toNat hi.toNat (by decide : 0 < 256),
        Nat.div_eq_of_lt hlo, Nat.zero_add]
  rw [h1, h2, UInt8.ofNat_toNat, UInt8.ofNat_toNat]

def u16beIso : Iso (UInt8 × UInt8) UInt16 :=
  Iso.ofTotal u16beRead u16beWrite u16beWrite_read u16beRead_write

/-- **A big-endian 16-bit unsigned integer.** -/
def u16be : Codec UInt16 := Codec.iso u16beIso (Codec.seq Codec.byte Codec.byte)

theorem u16beConsumesByte : ConsumesByte u16be :=
  isoConsumesByte u16beIso (Codec.seq Codec.byte Codec.byte)
    (seqConsumesByte Codec.byte Codec.byte byteConsumesByte byteConsumesByte)

/-! ## Value checks

`decodeWhole` goes through `decodeFullArrayFast`, which is defined by **well-founded
recursion** (`termination_by`). Such a definition does **not** reduce in the kernel,
so `decide`/`rfl` cannot evaluate a decode here — and `native_decide` would add an
axiom (`Lean.ofReduceBool`), which the `[propext, Quot.sound]`-only gate forbids in
proven code. So the executable witnesses live in `Bench.lean`
(`benchExamples`), as runtime checks in the style the rest of the bench uses: they
compare the produced value against the expected one and fail the lane on a
mismatch. That is a value check, not a proof, and it is labelled as such — the
*proofs* above are what carry the guarantees. -/

end Codec.Examples
