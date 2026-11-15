# Design — `basen-uppercase-prepass`

**Written 2026-11-15, after implementation.** This artifact was missing while the change
was being landed — the change was authored 2026-11-07 with `proposal`, `specs` and
`tasks` and no `design`, and the gap went unnoticed through three implementation commits
because the task list was read instead of the artifact graph. It is reconstructed here
from the proposal, the **landed** code, and the decisions taken during implementation, so
it records what was decided rather than what was planned. Where the two differ, the
measurement wins and says so.

See `proposal.md` — _Why_ for motivation, and `specs/basen/spec.md` for the requirements.
This document does not restate either.

## Context

`Codec/Normal.lean` (251 lines, in the `codec` package) supplies the whole mechanism for
"one input spelling has many names":

```lean
structure Normalizer (S : Type) (norm : S → S) where
  idem : ∀ x, norm (norm x) = norm x
def fill, decodeNormal, decodeNormal_of_fixed, decodeNormal_encode
```

It is generic over `S`, `norm`, `α` — nothing in it knows about bytes, bases, or formats.

`basen`'s `Base16.lean` at the start of this change compiled **88 declarations**, of which
the case-folding tier was 24 theorems plus its supporting definitions (29 pins in the
axiom gate). The tier built its own `Normal`/`Iso` (`hexFixed`, `foldByte`, `foldList`,
`foldNormalizer`, `hexBlockApplyF`, `hexBlockUnapplyF`, `hexBlockIsoF`, `fill_foldList`)
and did not use `codec`'s. Measured at implementation time: **`hexBlockIsoF` had no
caller outside the tier's own lemmas**, and `decodeHexFold` went through `hexRun` rather
than through that `Iso` — so the tier constructed a quotient object and then decoded
around it.

The justification for all of it was one sentence, stated twice in `Base16.lean` and never
sourced:

> "RFC 4648 §8 requires a Base16 decoder to accept both cases."

§8 says the opposite. `codec` had already corrected this same misquote in
`codec-audit-round-eight` M-1; `basen` never received the fix.

**The constraint that shapes everything here: the pre-pass must be sound for a base, and
soundness is an alphabet property, not a property of the fold.** See D2.

## Goals / Non-Goals

**Goals:**

- One pre-pass definition serving every base for which it is sound, so the next base that
  wants case tolerance pays a `Normalizer` instance rather than a tier.
- The strict decoder unchanged. The tolerance lives in a decoder composed _outside_ the
  `Iso`, never in a relaxed `Iso.law` — the same split `codec`'s `[S1]` forbids collapsing.
- The base-64 exclusion **asserted**, not documented, so extending the pre-pass there is a
  build failure rather than a code review.

**Non-Goals (design-level boundaries, beyond the proposal's scope list):**

- **Not a promotion of `upperBytes` into `codec`.** See D1 — the mechanism is shared, the
  instance is not.
- **Not a general "pre-pass registry."** Two instances exist (case folding, and
  `basen-radix`'s `trimFor` for leading zeros/blanks); a registry keyed by base would be
  the dispatch index this package deliberately avoids (`BaseN.lean` has no `Base`
  inductive for the same reason).
- **Not whitespace trimming or leading-zero stripping.** Those are `basen-radix`'s, and
  its `trimFor` is `Option`-valued and radix-relative, so it cannot live in the shared
  location even in principle. See D1's asymmetry note.

## Decisions

### D1 — The pre-pass lives in `basen`, instantiating `codec`'s mechanism

**Decision:** `upperByte`/`upperBytes`/`upperNormalizer` go in `BaseN/Common.lean`.
`codec` is not touched.

**Why not `codec`.** `upperBytes` is a _concrete alphabet operation_ — it knows that
`a`–`z` are ASCII 97–122 and that they belong at 65–90. `codec` ships **no concrete
format** (`[S3]`); adding a case-folding function to it would be the same breach as the
`Codec/Examples.lean` that was written and then removed. What `codec` supplies is
`Normalizer`/`decodeNormal`, and both bases use it.

**Alternatives considered.**

| alternative                                                    | why rejected                                                                                                                                                                                                                                                      |
| -------------------------------------------------------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `Codec/Normal/Upper.lean` — a portable `upperBytes` in `codec` | case folding is _arguably_ format-agnostic, but there is exactly **one** portable instance today. Promoting an abstraction before its second instance is the trap that produced seven `:= rfl` theorems in `basen-radix` §8.4. Revisit when a second one appears. |
| a per-base `foldByte`, kept but refactored                     | this is what the tier already was. The duplication is the defect, not its shape.                                                                                                                                                                                  |
| no shared location; copy `upperBytes` per base                 | two copies of one map can drift, and this repo has paid for duplicated name lists five times.                                                                                                                                                                     |

**The asymmetry worth recording, because it settles a question a reader will ask:** case
folding is _radix-independent_ (`UInt8 → UInt8`), so it can leave `basen` if it ever needs
to. `trimFor` is `Nat → List UInt8 → Option (List UInt8)` — it **needs the radix**, so it
can never leave. A "shared pre-pass layer" is therefore not one thing: one of the two
instances is portable and one is not, and only the future appearance of a second portable
instance would justify moving the first.

### D2 — Soundness is an alphabet property, measured per base — not a property of the fold

**Decision:** the pre-pass may be applied to a base exactly when that base's alphabet
contains no lowercase symbols. This is checked per base, by measurement, and recorded.

**The measurement, taken on the shipped tree (`scratch/alphabet.lean`, 2026-11-15).**
`basen`'s per-base `Nat`-valued digit functions use an _out-of-range sentinel_ for a byte
outside the alphabet — a value `≥ radix`. That convention is what makes the three-way
split visible in three independent ways at once:

| base | `digitFn 0x61` (`'a'`)  | validity predicate            | verdict                               |
| ---- | ----------------------- | ----------------------------- | ------------------------------------- |
| 16   | `hexToNibble 0x61 = 16` | `hexNibbleValid 0x61 = false` | sentinel → **not** an alphabet member |
| 32   | `b32ToVal 0x61 = 32`    | `b32Valid 0x61 = false`       | sentinel → **not** an alphabet member |
| 64   | `b64ToVal 0x61 = 26`    | `b64Valid 0x61 = true`        | **a real digit** (A = 0, a = 26)      |

So for base 64 the lowercase letters occupy genuine value positions: `'A'` and `'a'` are
0 and 26. Uppercasing does not remove information-free variation there; it **changes the
value**. Measured end to end:

```
"TWFu"  -> some [77, 97, 110]     ("Man")
"twfu"  -> some [183, 7, 238]     a different, equally well-formed value
```

Both are entirely within the alphabet. This is silent corruption, which is why §1.1 of the
tasks committed it as a **permanently failing assertion** (`Bench.b64Lower_decodes`) rather
than a comment: a later reader extending the pre-pass to base 64 now breaks the build.

**Why this is a design decision and not an implementation detail.** The intuitive rule —
"case folding is generic, apply it wherever case-insensitivity is wanted" — is exactly the
rule that corrupts base 64. The correct precondition is not about the _fold_ but about the
_alphabet_, and it must be stated per base with its measurement, because a base added later
cannot inherit it.

### D3 — Pin the RFC at its actual modal verb, and treat the obligation as withdrawn

**Decision:** lowercase acceptance is documented as an **optional convenience**, and the
strict uppercase-only decoder is conformant on its own. RFC 4648 §8:

> "Base 16 encoding does not require case insensitivity; however, Base 16 decoders **MAY**
> accept lowercase letters."

**Why this is a decision and not a doc fix.** The tier existed to discharge a `MUST`. Once
the verb is read as `MAY`, the tier has **no obligation behind it** — and that is what
authorises deleting 29 pins rather than refactoring them. The behavioural change to the
package is _zero_ (both cases still decode), so the change is a deletion justified by a
corrected reading, not a feature removal.

**The general rule this installs:** a normative claim about an external standard is as
checkable as a performance figure. `MUST` obliges, `MAY` permits, `SHOULD` advises — only
the first makes a missing behaviour a defect. No RFC text is vendored anywhere in this
ecosystem, which is precisely why the claim went unchecked for two audit rounds.

### D4 — Base 32's tolerance is additive: a second decoder, not a widened one

**Decision:** `decodeFullB32` is untouched. The tolerant path is a new `decodeB32Fold`,
and `strict_rejects_lowercase` pins that the strict decoder still rejects `"my======"`.

**Why.** The alternative — widening `decodeFullB32` in place — would change an existing
declaration's behaviour, and every base-32 law is stated over it (`roundtrip`,
`decodeFull_canonical`, `decodeFull_B32_char`, …). Two decoders make the ownership split
explicit, exactly as base 16 already had, and keeps "no existing declaration's statement
changes" literally true.

Measured before writing anything: `"my======"` was `none` and `"MY======"` was
`some [102]`, so the widening is strictly additive — no input changes its answer.

## Risks / Trade-offs

- **Silent corruption if the pre-pass reaches a base where case is data.** → Mitigated by
  D2's per-base measurement plus `Bench.b64Lower_decodes`, a permanent assertion that
  fails the build. This is the one failure mode of the change that a type checker cannot
  see, which is why it got an assertion rather than a docstring.

- **A mutation that dies upstream is mistaken for evidence.** Disabling `upperBytes` in
  `Common` fails `Common`'s own arithmetic lemmas and never reaches either base — so it
  proves the pre-pass is self-consistent and says **nothing** about whether a base uses it.
  → The recorded mutations are at the _wiring_ point (`decodeHexFold` / `decodeB32Fold`
  dropping the pre-pass), which fail at `Base16:689`, `:711` and `Base32:3998`, `:4009`,
  `:4054` — precisely the lowercase-equality and roundtrip theorems. `tasks.md` §1.2
  records the distinction rather than four green ticks.

- **The deletion is larger than the addition, so a reviewer cannot tell from the diff
  whether a law was lost.** → `tasks.md` §7.1 records the decomposition (29 pins deleted,
  18 added, allowlist 17 → 16) rather than the net −24, because the net landed near the
  plan's estimate only by an over-count cancelling an under-count. A right net from two
  wrong parts is the shape to distrust.

- **`upperBytes` fixes only ASCII case.** It is a byte-range map, correct for RFC 4648's
  alphabets and meaningless for anything else. → Stated in `BaseN/Common.lean`'s section
  header; the function is not claimed to be general-purpose.

- **Two decoders per base means callers must choose.** → The choice is the point, and the
  ownership split is written down in `README.md` (which decoder owns which law), so
  "proven" is unambiguous per cell.

## Migration Plan

Not a deployed system: `basen` is a library and the behavioural change is nil. The one
consumer-facing note is that `Base16.foldByte`/`foldList`/`foldByteBytes` were **deleted**,
not renamed — a caller (there were none inside the package) would move to
`BaseN.Common.upperByte`/`upperBytes`. `CHANGELOG.md` lists every deleted name so an old
citation can be resolved.

## Open Questions

None. The one genuinely open question this change inherited — whether the pre-pass belongs
in `codec` — was **resolved** during implementation and is recorded as D1 rather than left
here: `basen` keeps it, and the library-division question is answered "no" in
`tasks.md` §6.5. Leaving it as an open question would have been a decision skipped, not a
decision deferred.
