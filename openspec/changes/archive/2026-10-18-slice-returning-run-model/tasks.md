# Tasks

> Replace the failed compiler / `@[extern]` approaches: the cost is the `List`
> result carrier, so ship a **packed, `USize`-indexed, slice-returning run-model**
> proved equal to the `Bytes` spec. No compiler, no new C.

## 1. Slice-returning decode surface

- [x] 1.1 Add `decodeByteArraySlice : Codec α → ByteArray → USize → Option (α × USize)`:
      the native index recursion (`a[i]` read, `i + m` through `seq`, no `List`
      cell), `byte` case O(1).
- [x] 1.2 Add `decodeFullByteArraySlice : ByteArray → USize → Option (ByteArray × USize)`:
      full-consumption returns the packed suffix in one `ByteArray.extract`/copy,
      never an `Option (List α × Nat)`.
- [x] 1.3 Prove `decodeByteArraySlice_eq` / `decodeFullByteArraySlice_eq` against
      the existing `decodeByteArray_eq` / `decodeFullByteArray_spec`, via the
      `USize.toNat` correspondence — `[propext, Quot.sound]`-only.

## 2. Packed encode accumulator

- [x] 2.1 Promote the `ByteArray.push`-fold accumulator (`encodeByteArrayBytes`)
      and its `foldl_push_toArray` / `foldl_ba_push` lemmas from
      `Codec/ExternFastPath.lean` into the committed `Codec` run-model surface
      (drop the now-vestigial "extern" framing — no custom C needed).
- [x] 2.2 Prove `encodeByteArrayBytes_eq_encodeRepeat` (the O(n) push fold =
      the `List.append` `encodeRepeat` denotation), `[propext, Quot.sound]`-only.

## 3. Bench + acceptance

- [x] 3.1 Add a `Bench.lean` lane: `decodeFullByteArraySlice byte [n]` and
      `encodeByteArrayBytes byte [n]` vs the `List` baseline and a raw
      `memchr`/`memcpy` copy. Record per-byte figures.
- [x] 3.2 Acceptance: the slice decode falls from ~300 µs toward the `memcpy`
      floor (~sub-µs for the packed suffix), and the push encode falls from ~20 ms
      toward ~1.5 ms; no regression on the `List` interpreter lanes.

## 4. Integration gate + docs

- [x] 4.1 `lake build` (zero `sorry`/warnings), `#print axioms Codec.roundtrip` ⇒
      `[propext, Quot.sound]`, `nix build .#checks.<system>.lean` + `.#bench` green.
- [x] 4.2 Record the measured numbers, the **zero-copy lifetime trust seam**, and
      the "carrier swap, not compiler" lesson in README + `AGENTS.md` handoff.
