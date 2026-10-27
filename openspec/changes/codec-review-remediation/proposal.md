# Proposal

## Why

An adversarial review of this repo was run with four independent lenses —
(1) `README.md`/`PAPER.md` scholarship vs the source paper, (2) the Lean proof
surface vs its own claims, (3) `AGENTS.md` as agent operating instructions, and
(4) the global `lean` skill — with every claim that could be mechanically checked
compiled or grepped rather than asserted. The reviews are preserved verbatim in
`review.md`.

They found **74 findings** (2 CRITICAL, 11 HIGH, 20 MEDIUM, 33 LOW, 8 INFO), and three of
them are the kind that actively misinform a future reader or agent:

- **`CHANGELOG.md` stated the wrong type for `Bytes`.** It said
  `abbrev Bytes := List UInt8`; the source is
  `abbrev Bytes (n : Nat) : Type := Fin n → UInt8` and `README.md` devotes a
  whole section to arguing the `List UInt8` carrier was _deleted_ as "the
  defect". A reader following the changelog would have reintroduced the exact
  `Array.extract`/`toList` transport leak the single-carrier decision exists to
  remove. **Fixed already** (commit `57d91ac`).
- **The "zero `sorry`" proof gate is asserted, not enforced.** `default.nix`'s
  `check` derivation runs a plain `lake build` with no `-DwarningAsError` and no
  `sorry` scan; `lake build` reports `sorry` as a warning. An agent can stub a
  theorem to `sorry` and the gate still goes green, while `AGENTS.md` twice calls
  zero-`sorry` "the proof gate".
- **The `Classical.choice` trap guidance was incomplete in exactly the way that
  cost time.** `AGENTS.md` recorded one leak shape; there are at least three.
  **Fixed already** (commit `e72be59`). `decide_eq_true (by omega)` on a disjunction goal leaks
  `[propext, Classical.choice, Quot.sound]` — reproduced — because `omega`
  closes a disjunction by case analysis. The fact is recorded only as a
  parenthetical inside a completed change's history, not in the ergonomics
  section a reader would consult.

Beyond those, the review found two HIGH defects in the **Layer-2 trust seam**'s
evidence chain (`byteSlice` — the headline seam — has no Lean law pinning it,
while its two siblings do; and the only runtime C↔Lean boundary check is
unreachable in a default `bench` run because an earlier lane crashes), plus a
set of derived-not-quoted errors in `README.md`'s `[D#]`/`[S#]` entries: the
quotations from the paper are verbatim-correct but several _reasons_ given for
them are wrong (`[D4]`'s injectivity argument, `[D7]`'s invented "chain-isolated"
precondition, `[S1]` contradicting `[S4]` about whether `foldl`'s law is
unconditional).

**Why now:** the library's own selling point is that its claims are _checked_,
not promised. A document set that misstates its substrate type and a gate that
does not enforce its headline invariant undercut that claim from the inside.
Every finding is small and mechanical; none requires new mathematics.

## What Changes

- **Correct `CHANGELOG.md`'s `Bytes` entry** to the length-indexed substrate, and
  add a note to `AGENTS.md`'s truth table pinning `Bytes n := Fin n → UInt8` as
  the single definition so the two cannot drift again.
- **Make the proof gate real**: add a `sorry` scan (or `-DwarningAsError`) to
  `default.nix`'s `check` derivation so `checks.lean` fails on a `sorry`, and
  state in `AGENTS.md` that the gate is enforced rather than observed. Add an
  in-repo axiom sample (`#print axioms Codec.roundtrip`) so the documented check
  is a `lean-codec` command, not a `BaseN` one.
- **Complete the `Classical.choice` trap section** in `AGENTS.md` to all three
  verified shapes (dependent `match`/`cases` on an equation; `decide_eq_true` on
  a disjunction; a `match` on a `Bool` in the goal), each with its fixing
  spelling, and remove the duplicate parenthetical in the change-history prose so
  the fact lives in one place.
- **Add the two missing Layer-2 seam laws/evidence**: `byteSlice_spec` (the
  headline seam currently has none, while `blitBytes_spec`/`findByte_spec` do),
  and move the seam boundary value-checks to the front of `bench`'s `main` so
  they actually run (plus fix or guard the earlier crashing lane).
- **Correct `README.md`'s derived reasoning** for `[D2]`, `[D4]`, `[D7]`, `[S1]`,
  `[S2]`, `[S6]`, `[D8]`, and the abstraction block's `decode`/`Rel` signatures —
  keeping every passage that the review verified as _verbatim correct_ untouched.
- **Reconcile `Packed.lean`'s header with `ByteSlice.lean`'s** about whether the
  `commitRemainder` seam is wired into a library path (it is not).
- **Split the `lean` skill**: keep the generic half generic (its own stated
  contract), move the project-specific body into this repo, record the missing
  `Classical.choice`/`if_pos`/`ByteArray.append_assoc` lessons, and resolve the
  file's self-defeating "official skill wins on proof engineering" clause against
  its own stricter axiom gate.
- **Close `AGENTS.md`'s verification-recipe and attribution defects**: the recipe
  section mixes `lean-codec` and `../lean-basen` commands under one heading, the
  `nix build .#bench` example contradicts the no-foreground rule, and the
  `bad import Codec.Normal` → stale-flake-lock failure mode is recorded nowhere.

Explicitly **not** changing: any theorem statement or proof (the review verified
zero `sorry`, no `Classical.choice` in 18 sample theorems, `Iso.law` with no
escape hatches, and no C-vs-Lean divergence on reachable inputs), the `[D#]`/`[S#]`
anchor identifiers, or the paper quotations themselves.

## Capabilities

### New Capabilities

- `codec/review-remediation`: the review's findings as a checked obligation set —
  the substrate-type single-definition rule, the enforced zero-`sorry` gate, the
  complete `Classical.choice` leak catalogue, and the Layer-2 seam's law coverage.

### Modified Capabilities

- `codec/byte-string`: the `Bytes n` definition is stated once and pinned across
  every doc that names it (`CHANGELOG.md` currently contradicts it).
- `codec/partial-remainder`: each Layer-2 seam SHALL carry a Lean law pinning its
  body (`byteSlice` currently does not), and the seam's runtime value-checks SHALL
  be reachable in a default `bench` run.

## Impact

- **Docs (behavioural)**: `CHANGELOG.md` (wrong `Bytes` type), `README.md`
  (`[D2]`/`[D4]`/`[D7]`/`[S1]`/`[S2]`/`[S6]`/`[D8]` reasoning, abstraction block
  signatures), `AGENTS.md` (trap section, gate claim, verification recipe,
  attribution, `bad import` rail).
- **Build**: `default.nix`'s `check` derivation gains a `sorry` gate — a real
  behaviour change to the proof gate, so a stray `sorry` now fails the build.
- **Code (additive)**: `Codec/ByteSlice.lean` gains `byteSlice_spec`;
  `Codec/Packed.lean`'s header is corrected; `Bench.lean` reorders/fixes the
  scalar-index lane so `benchSeamBoundaries` runs.
- **Global skill**: `~/.pi/agent/skills/lean/SKILL.md` is split and corrected.
  This is outside the repo, so it is tracked here as a task with an explicit
  external-path note, not as a repo edit.
- **No theorem, proof, or `[D#]`/`[S#]` anchor changes.** No new mathematics. No
  substrate or carrier change — the whole point is that `Fin n → UInt8` is the
  one substrate and the docs now agree.
- **Tracking**: the four verbatim reviews are captured in `review.md` so every
  task cites a reproducible finding rather than a memory.
