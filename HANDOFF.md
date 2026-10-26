# Handoff — session ending 2026-10-26

Paste this to start the next session. It states current facts only; the
authoritative ledger is `openspec/changes/<name>/tasks.md`, and the architecture
statement is `README.md`.

## What landed this session (all committed and pushed)

**`lean-codec` (`origin/master` = `0aca08d`)** — new change
`codec-normal-form-case-quotient`, **15/16 done**.

- `Codec/Normal.lean` — the information-free-variation layer:
  - `Normal S norm` (the quotient `S/~` as the fixed points of a total idempotent
    `norm`), `Normal.ext`;
  - `Normalizer S norm` — idempotence carried in the **type** (`norm` is a
    **parameter**, not a field, so `Normal S norm` is definitionally shared);
  - `fill` (canonical representative), `fill_raw`, `fill_fixed`
    (`norm ∘ fill = id`, **no axioms**), `fill_surj` (faithfulness),
    `fill_inj`;
  - `decodeNormal` (the normalising decoder — `norm` composed **outside** an
    ordinary `Iso`; not an `Iso`, no inverse), `decodeNormal_of_fixed`,
    `decodeNormal_encode` (with the `hfix : norm s = s` precondition).
- Re-exported from `Codec.lean`; bench value-checks in `Bench.lean`; README `[D4]`
  sharpened; `CHANGELOG.md` entry.
- `lake build` 13 jobs, `lake build bench` 27 jobs — **zero `sorry`, zero
  warnings**. `#print axioms`: `fill_fixed` no axioms, everything else
  `[propext]`-only. No `Classical.choice`.
- **`Codec/Normal.lean` is fully generic** — polymorphic in `S : Type`, no
  `UInt8`/`Bytes`/hex/ASCII/text anywhere in the code. `[S3]` holds. (Only
  docstrings cite RFC 4648 §8 as the motivating consumer.)

**`lean-basen` (`origin/master` = `c3da03a`)** — one groundwork commit:
`import Codec.Normal` in `BaseN/Common.lean`. Build green, 25 jobs, no behavior
change. No §8 code yet.

**Ledgers corrected:**

- `basen-rfc-conformance-theorems` 7.3 — **paused**, with the false
  "breaks `Unambiguous`" rationale withdrawn and the real six-step work list
  recorded.
- `codec-normal-form-case-quotient` 5.1 — the handoff block (below).
- `openspec validate --all` — 8 passed, 0 failed.

**Skill updated:** `~/.pi/agent/skills/lean/SKILL.md`, five new 2026-10-26 entries
(quotient-in-the-object; `norm` as parameter; wrapper's precondition; the
case-split lesson + `omega`/`UInt8` traps; the naming lesson).

## The one open task: `codec-normal-form-case-quotient` 5.1

**Do this first, and read the HANDOFF block in that change's `tasks.md` §5.1
before writing any code.** Two findings are already verified — do not rediscover
them:

1. **The fold must go UP.** `norm` folds `a`–`f` (97..102) → `A`–`F` (65..70).
   Reason: the canonical hex alphabet is uppercase, so the encoder's output must
   be a `norm` fixed point — exactly `decodeNormal_encode`'s `hfix`. Folding down
   makes the normalising decoder fail on its own encoder's output.
   Verified: `foldByte_idem` holds; `A`, `F`, `9` are fixed points; `a`→`A`,
   `f`→`F`.
2. **The blocker is semantic, not plumbing.** `hexBlockApply` is uppercase-only,
   so `unapply f := hexBlockApply f.raw` is **wrong** (a class with a lowercase
   representative will not apply). `unapply` must fold first:
   `hexBlockApply (foldList f.raw)`, then prove
   `hexBlockApply (foldList cs) = hexBlockApply cs` for a 2-element list.

**The lemma that defeated three attempts, and its correct shape.**
`hexToNibble (foldByte b).toNat = hexToNibble b.toNat` is **false as one
equation** — in the non-lowercase branch it demands
`hexToNibble b.toNat = b.toNat`, false for any non-digit. It must be a
**three-way case split** (digit `48..57`: fixpoint, equal; upper `65..70`:
fixpoint, equal; lower `97..102`: folds to `−32`, nibble equal by the digit
lemma). Split first; do not try to unify.

**Order:** (1) the three-way `hexToNibble`/`foldByte` lemma; (2)
`hexBlockApply_fold`; (3) `hexElemF` + law; (4) `decodeHexFold` + the §8
both-cases theorem; (5) discharge `hfix` (uppercase output is a fixed point —
finding 1); (6) the six ledger edits in `basen-rfc-conformance-theorems` 7.3.

**Already proved in probes** (short; re-prove in-tree): `foldByte_idem`,
`foldByte_fixed`, `nibbleToHex_not_lower`, `hexDigit_fixed`,
`hexCanon_fixed`. Note `toByte_nibbleToHex` is `private` in `Base16.lean` —
inline the `UInt8.toNat_ofNat'` + `Nat.mod_eq_of_lt` bridge; and supply
`UInt8.toNat_lt b` before any `n / 16 ≤ 15` `omega` goal.

## Hard rules that bit this session

- **Never `git checkout --` / `git stash` / `git reset` to "start clean".** It was
  reached for once (`AGENTS.md` forbids it) and was harmless only by luck — the
  file held nothing but broken attempts. If a proof will not close, stub **that
  one theorem** and iterate in `/tmp` against the built library.
- **Long builds detached** (`nohup … &`), poll with short calls. Never a huge
  tool timeout.
- **`../lean-basen` consumes `codec` by git input**, so `Codec.Normal` was only
  visible after pushing `lean-codec` and running `lake update codec` there. If
  core changes again, push first.
- **Task ledger gets the facts; `AGENTS.md` gets one current-state block.** Do not
  append session status to `AGENTS.md`.

## Archive ordering (unchanged, still applies)

Archive `lean-basen` **first**, then `basen-rfc-conformance-theorems`, running
`openspec validate --all` after **each**. Both MODIFY "The `basen` bases are
`Codec` values"; the texts were deliberately made identical (task 6.11), so
either order is safe — but reconcile the MODIFIED blocks again if §8 wording
lands in both.

## Not in scope, deliberately

Whitespace collapsing (`skipSpace`/`optSpace`/`sepSpace`) — length-changing, so
not a `Bytes n → Bytes n` normalizer. Needs a different carrier. Recorded as a
boundary in design D6, not a gap.
