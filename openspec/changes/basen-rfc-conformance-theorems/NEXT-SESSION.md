# Next session — `basen-rfc-conformance-theorems`

**Status at handoff: 28 / 31 tasks done. The in-scope queue is EMPTY.**
`../lean-basen` `HEAD` = `306e951`; `../lean-codec` = `1fc75e4`. Both **pushed**.
`openspec validate --all` green (8/8); `lake build` 24 jobs + `lake build bench`
43 jobs green in `../lean-basen`, zero `sorry`, zero Lean warnings.

## START HERE

**Nothing is pending in this change except Section 7, which is out of scope.** The
three remaining unchecked tasks (7.1, 7.2, 7.3) are explicitly scoped to a
**separate change**, `basen-rfc-total-characterization` — see §7 of `tasks.md`.
Do not absorb them into this change.

So the next session's first decision is a **choice of work item**, not a
continuation:

1. **Archive this change** (`/opsx-archive`), after confirming `lean-basen` is
   archived first (see "Archive ordering" below), then start
   `basen-rfc-total-characterization` for §7.
2. **Start Section 7 as a new change** without archiving this one.
3. **Something else** (the user decides).

Ask the user which; do not guess.

## What landed this session (task 6.4, 6.11, 6.6)

### Task 6.4 (MEDIUM M4) — the general rejection law, both bases — DONE

The finding was that the rejection theorems were a _finite vector set_
(`reject_ZgAAAA`, `reject_MYAAAA`, …) while the proposal promised the general
statement. All three parts now hold for **every** `s`, `[propext, Quot.sound]`-only,
gated in `Axioms.lean`, bench-covered:

|                                   | base64                                 | base32                                 |
| --------------------------------- | -------------------------------------- | -------------------------------------- |
| (a) invalid byte at **any** index | `decodeFullB64_reject_invalid_at`      | `decodeFullB32_reject_invalid_at`      |
| (b) `=` at code-word slot 0/1     | `decodeFullB64_reject_pad_at_low_slot` | `decodeFullB32_reject_pad_at_low_slot` |
| (c) `n % 4 ≠ 0` (base32 `% 8`)    | `decodeFullB64_reject_arity`           | `decodeFullB32_reject_arity`           |

Supporting lemmas: `decodeFullB{64,32}_consumed_alphabet`,
`Rel_b{64,32}TailElem_pad_pos`, `decodeFullB64_block_region`,
`decodeFullB{64,32}_arity`.

**Part (c) — billed as "the only genuinely hard one" — was not hard.** It needs no
case-split over examples:

```lean
relB64Block_len  : n - t.remaining = 4 * blocks.length
relB64Tail_len   : t.remaining     = 4 * tails.length
-- hence (needs `t.hle` for `omega`, the equations alone are not enough):
n = 4 * (blocks.length + tails.length)
-- and then:
rw [hn, Nat.mul_mod_right]
```

`omega` **cannot** derive `n % 4 = 0` from `n = 4 * k` — it does not reason modulo.
Convert to the equational form and rewrite. (Now in the `lean` skill.)

**Verification state:** 13 new `#guard_msgs` gates in `Axioms.lean`, and the gate
was re-verified **load-bearing** (flipping one expectation to `[propext]` fails the
build with 2 errors; restoring is green). Bench vectors added for each law. The
`Rel_b32TailElem_pad_pos` proof needs the 1-byte tail's slot 1 handled correctly —
it is `valToDigit`, **not** the pad; that cost real time and is in the skill.

### Tasks 6.11 then 6.6 — done in the required order

6.11 (archive hazard) was resolved **before** 6.6, in one pass across both places,
so they cannot diverge:

- the synced `openspec/specs/basen/spec.md` requirement "The `basen` bases are
  `Codec` values" no longer claims "illegal data after `=` is **unrepresentable**"
  (withdrawn — `B32`/`B64` is a proved total bijective relabeling), and now reads
  "no bespoke `encode`/`decode`" as **no per-format decoder/encoder _triple_**,
  naming `decodeFullB{32,64}`/`encodeB{32,64}` as the value's own entry points. A
  new Scenario records the correction;
- `openspec/changes/lean-basen/specs/basen/spec.md`'s **MODIFIED** block carries
  the _same_ corrected text **and every synced scenario**, so archiving either
  change yields identical text with nothing silently dropped.

**Archive ordering (do not get this wrong):** `lean-basen` MODIFIES the same
requirement. Archive `lean-basen` **first**, then this change, and re-run
`openspec validate --all` after each. Both are green today.

## Section 7 (out of scope here — a separate change)

- **7.1** — the general "decode succeeds iff `s ∈ image encode`" iff for all seven
  bases. Note: for base32/64 this is **already proved** as
  `decodeFullB{64,32}_char` (task 6.3); 7.1 is the promotion to all seven, plus
  whatever the fixed-width bases still lack.
- **7.2** — either prove a type-level `B64`/`B32` that _cannot_ represent trailing
  data, or keep the withdrawal (which 6.6 has now made the synced spec say).
- **7.3** — Base16 case-insensitive decoder (RFC 4648 §8 "MUST accept both
  cases"). Currently a documented **non-goal**: it breaks `Unambiguous` per the
  design, so it needs a documented relaxation first.

## The one thing that must not be re-litigated

**`many` is derived, not a `Codec` constructor** (verified un-implementable:
definition-order cycle `Codec → Productive → Rel → Codec`, and the mutual-inductive
escape fails the universe check). Unbounded repetition is the already-proved
`relRepeat`/`decodeRepeat`/`encodeRepeat` triple, exposed as a **run value**. See
`design.md` §D0/D7.

## Verification recipe (no tooling is on the host PATH)

Work in `../lean-basen`'s own `nix develop`.

```
nix develop --command lake build         # library: zero sorry / zero warnings
nix develop --command lake build bench   # the bench lane
```

Axiom gate — `Axioms.lean` is a `@[default_target]` lib, so `lake build` runs it;
a `Classical.choice` regression fails the build. To check one law by hand:

```
printf 'import BaseN\n#print axioms BaseN.Base64.decodeFullB64_reject_arity\n' > /tmp/c.lean
nix develop --command lake env lean /tmp/c.lean    # expect [propext, Quot.sound]
```

`openspec validate --all` from `../lean-codec` after any spec-delta edit.
`nix flake check` is a **long** build — launch it detached
(`nohup nix flake check > /tmp/fc.log 2>&1 &`) and poll; never foreground it.

## Git hygiene (this bit the previous session — read it)

- Commit **individual files**; print the `git diff --cached --name-only` set before
  every commit. The repo's pre-commit hook runs `nix fmt` and **rejects** the commit
  if it reformats a staged file — re-`git add` and commit again (this happened twice;
  it is normal, not a failure).
- **Never `git stash`/`git reset`/`git checkout -- <file>` to "start clean".** It
  destroyed verified work last session. If a proof will not compile, stub **that one
  theorem** to `sorry`, get the build green, and iterate the proof in `/tmp/probe.lean`
  against the built library. Commit per law-family so a revert is never tempting.
