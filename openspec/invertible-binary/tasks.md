# `codec` — task ledger

> OpenSpec planning artifact — NOT committed (`openspec/` is gitignored).
> Companion proposal: [`proposal.md`](./proposal.md).

Ground truth: Rendel & Ostermann, *Invertible Syntax Descriptions* (2010),
`doc/rendel10invertible.md`.  **Pure-framework core: `Iso`/`Codec`/`Rel`/the
laws, zero *domain-specific* leaf codecs** (not even `u8`; the primitives are
`byte` and `pure`).  Concrete codecs — binary leaves
(`lean-binary`) and text/Unicode (`lean-text`) — are **downstream consumers**,
built by composition.  The paper (`doc/rendel10invertible.md`) is the spec.

Status legend: `[ ]` queued · `[~]` in progress · `[x]` landed.

---

## T0 — Feasibility spike (BLOCKER)

- [x] T0.1 **Confirm the paper is the spec; inventory what we adopt vs add.**
  Result: adopt `Iso` (§3.1/§5.1), the `Syntax`-as-`Codec` interface (§3.4), `Rel` (§4.3),
  derived combinators (§6.1), `foldl`/`iterate` (§5.2/5.3).  **Re-base:** bytes
  are the primitive concrete syntax (`byte : Codec UInt8`, `Rel` over `ByteArray`).
  **Defer:** all leaf codecs (binary + text) to `lean-binary`/`lean-text` (not core).
- [x] T0.2 **Confirm binary + speed + high-level-Lean feasibility.**
  `ByteArray.push/get!/extract/size`, `UInt8/16/32/64`, `Array`, `List`,
  `Nat.div/mod`, `Nat.div_add_mod`, `Nat.mod_eq_of_lt` all present (stdlib).
  `clang`/`gcc` for extraction.  No mathlib needed (`Iso` is our own stdlib-only
  definition; `Equiv`/`PEquiv` are mathlib and NOT reused).
- [x] T0.3 **The `Iso` inverse law holds unconditionally (resolved by design).**
  There is no "coarse law" and no shape to pick, because departure #4 (lossless
  capture, no `ignore`) removes the *only* primitives that break the strict
  invariant.  The law is simply the strict
  `∀ a b, apply a = some b ↔ unapply b = some a`, and it holds for **every**
  `Iso`-level combinator (`id`/`∘`/`associate`/`commute`/`unit`, `subset`,
  `element`).  `Category Iso`'s `∘`-closure (T1.2) closes under it directly.
  (Codec-level combinators like `many` are sound by the T4 roundtrip theorems,
  not the `Iso.law` field.)  (The paper's §3.1 "modulo equivalence classes"
  caveat exists only because the paper is lossy about whitespace; we are not.)
- [x] T0.4 **`Codec` is a typeclass (decided).**  Prefer the typeclass — it
  matches the paper's own "class of syntax descriptions" (§3.4) and its
  `IsoFunctor`/`ProductFunctor`/`Alternative` superclass structure, and the two
  interpreters (`decode`/`encode`) are naturally *instances* of `Codec` for
  different target representations (the paper's "polysemantic" single program,
  two directions).  A `structure` would be the fallback only if instance
  resolution proves unusable, which is not expected.
- [ ] T0.5 **`ByteArray` proof strategy — preference recorded: `simp` directly**
  over `ByteArray.get!/extract/size` (they reduce to well-founded functions on
  `Nat`, and `simp`/`omega` usually close such goals).  **Fallback only if
  stuck:** reason over a `List UInt8` model + a `ByteArray ⇄ List UInt8`
  transport lemma (proof ergonomics only; the *signature* stays `ByteArray`).
  Empirical confirmation happens during T4, not as a blocking T0 decision.
- [ ] T0.6 **Benchmark a `ByteArray` roundtrip** (multi-MB) to confirm
  O(n) / no boxing.  Acceptance threshold: roundtrip time scales **linearly**
  in input size (doubling input ~doubles time) with no per-byte allocation
  blow-up — i.e. the return-the-rest design is not copying the suffix per step.
  This gates *committing* the design, but the design is already chosen (return-
  the-rest); the benchmark confirms it, it does not re-open it.

**Definition of Done:** T0.4 is decided (typeclass); T0.5 has a recorded
preference (direct `simp`, fallback to a transport lemma); the T0.3 design result
and the T0.5 preference are reflected in `proposal.md` §Open questions; the T0.6
benchmark number (with its acceptance threshold) is in the notes.

---

## T1 — `Iso` (partial isomorphisms, the category) — the foundation

- [ ] T1.1 `Iso α β` with `apply`/`unapply` + the inverse `law` field.
- [ ] T1.2 `Category Iso` (`∘`, `id`) with the composition law proved.
- [ ] T1.3 Product bifunctor `×`, `associate`, `commute`, `unit`.
- [ ] T1.4 `element : α → Iso Unit α`, `subset : (α → Bool) → Iso α α`,
  `inverse : Iso α β → Iso β α`.  Carry `[DecidableEq α]` / `[Decidable p]`
  where the paper carries `Eq α` / predicate guards (the paper's `pure`/`element`
  `Eq` constraint becomes a `DecidableEq` obligation in Lean).
- [ ] T1.5 `foldl`/`iterate` (paper §5.2/5.3): `foldl : Iso (α×β) α → Iso (α, List β) α`
  via `iterate ∘ step`.

**Definition of Done:** every `Iso` combinator carries its law by construction;
`lake build` green, no `sorry`.  The *only* layer the rest depends on.

---

## T2 — `Codec` (the description interface, over bytes; the paper's `Syntax`)

- [ ] T2.1 The interface: `$` (IsoFunctor), `*` (ProductFunctor, tuples),
  `|`/`empty` (Alternative), `pure`, `byte : Codec UInt8` (the paper's `Syntax` class, renamed `Codec`).
  (`many` is a *derived* combinator — see T5.1 — not an interface primitive.)
- [ ] T2.2 **Declare `Rel`'s type signature here** (not in T4.1):
  `Rel : Codec α → α → ByteArray → Prop`, so `Unambiguous d := ∀ s, at most one
  x with Rel d x s` (T3.3) has no forward reference.  Only the *roundtrip
  theorems* live in T4; the signature belongs to the interface layer.

**Definition of Done:** the interface alone, `byte` over `UInt8`; a single
description value with no interpretation yet.

---

## T3 — Two interpretations (decode / encode)

- [ ] T3.1 **Deterministic decoder** `decode : Codec α → ByteArray →
  Except DecodeError (α × ByteArray)` — single threaded, returns the *value plus
  the remaining bytes* (the paper's `String → [(α,String)]` style, byte-ified),
  no `Nat` cursor, no backtracking list, no peeking.  The remaining-bytes value
  is private to `decode` and never part of `Rel`; on failure `DecodeError`
  carries the remaining bytes so the error *position* is structural
  (`whole.size - remaining.size`).
- [ ] T3.2 **Builder encoder** `encode : Codec α → α → Option ByteArray` —
  **partial** (rejects out-of-domain, matching the paper §4.2); growable
  builder in the `some` branch for amortized O(1) append.
- [ ] T3.3 **Unambiguity discipline (HARD precondition).**  `Unambiguous d :=
  ∀ s, at most one x with Rel d x s` — defined using the `Rel` **type signature**
  (its *declaration* is hoisted to T2.2 so there is no forward reference; only
  its roundtrip *theorems* live in T4).  This is a **per-demo proof obligation,
  not a library-decidable property** — `Unambiguous` is a set predicate over
  `Rel`, not a combinator recursor; the library cannot synthesize it.  Prove the
  deterministic decoder is sound and complete w.r.t. `Rel` on the unambiguous
  domain; note (paper §4.4) that `|` is committed-choice and backtracking/peek
  are out of scope.  Prerequisite of every T4 theorem.

**Definition of Done:** the two interpreters are the **executable** layer; both
total (over `Option`), fast, extraction-ready.

---

## T4 — `Rel` (denotational semantics) + roundtrip theorems

- [ ] T4.1 `Rel : Codec α → α → ByteArray → Prop` (the paper §4.3 graph), over
  **whole** byte sequences only (no suffix in the relation — the remaining-bytes
  value is private to `decode`).
- [ ] T4.2 Bidirectional law (with `Unambiguous d` as the hypothesis, because
  completeness — the left-to-right half — needs it):
  `Unambiguous d → (Rel d x s ↔ decode d s = .ok (x, empty))`.
- [ ] T4.3 Roundtrip (encode-success is the only premise; no `Unambiguous`
  needed for this direction):
  `(encode d x) = some s → decode d s = .ok (x, empty)`.
- [ ] T4.4 The laws are *theorems about `Rel`*, closed by `simp`/`rfl`/induction
  — no solver.

**Definition of Done:** the paper's "one description = one relation, two
directions" is a **proved theorem**, not a convention.

---

## T5 — Derived combinators (generic, byte-agnostic; NO domain-specific leaf codecs)

- [ ] T5.1 Paper-derived combinators at the `Codec` level: `many` (§3.4 via
  `nil`/`cons`), `*>`, `<*`, `between`, `chainl1` (§6.1, which *uses* the
  `Iso`-level `foldl`/`iterate` built in T1.5).

**Definition of Done:** these are the *only* generic combinators core provides;
they close over any downstream leaf `Iso`.  **Core contains no `u8`, no
endianness, no `bytes n`, no `varint`, no `text`** — those are all downstream.

---

## T6 — Benchmark & extraction of the *framework* (speed gate on core)

- [ ] T6.1 Extract to C/LLVM (`clang`) the interpreter hot path; confirm `Prop`
  proofs erase.
- [ ] T6.2 Benchmark the `decode`/`encode` interpreters on a synthetic
  `byte`/`many` description (no domain leaf needed) — linear time, no per-byte
  boxing.  Record the number.
- [ ] T6.3 Confirm `get!`/remaining-bytes (not `getElem`-with-proof) is what
  actually runs post-extraction.

**Definition of Done:** the *framework's* speed is demonstrated on core alone;
the full varint/protobuf/image benchmarks live in `lean-binary` (downstream).

---

## T7 — Docs & accept criteria

- [ ] T7.1 `README.md`: the guarantee, the `Iso`/`Codec`/`Rel` model, the
  pure-framework scope, the combinator table, usage.
- [ ] T7.2 Zero-`sorry` + `#print axioms` = stdlib only
  (`propext`, `Classical.choice`, `Quot.sound`).
- [ ] T7.3 Note the deliberate departures from the paper (byte core, return-the-
  rest decode, deterministic single result with backtracking/peek out of scope,
  and **lossless capture** — no `ignore`, `many (subset p byte)` keeps
  skippable bytes verbatim, which is what makes `Iso.law` unconditional)
  and *why*, so no one totalizes `encode` or reintroduces backtracking; document
  `lean-binary` and `lean-text` as the downstream consumers.

**Definition of Done:** a reviewer can build, run the framework benchmark, and
confirm the roundtrip law is a theorem.

---

## Deferred (out of `codec` scope) — downstream consumers

Not part of this ledger.  Two **future** packages, built **by composition**
using `codec`'s `Iso`/`Codec`, each requiring **zero changes to core**:

**`lean-binary`** (binary leaf codecs):
- `u8 : Codec UInt8` (trivially `byte` — the
  one-line *first leaf* that is the acceptance test of core's expressiveness)
- `u16le`/`u16be`/`u32le`/`u32be`/`u64le`/`u64be`, `bytes n`, `count n`,
  `varint` (LEB128, value-dependent arity), `lengthPrefix`
  (where `count n : Codec Unit` decodes/produces exactly `n` bytes — the paper's
  `many` specialized to a fixed count; the `u8` one-liner above is effectively
  `count 1`).
- image-header demo + length-prefixed Protobuf demo + the speed benchmark

**`lean-text`** (text/Unicode combinators on bytes — the paper's domain,
re-based on `utf8`):
- `utf8 : Iso String (List UInt8)` — code points ⇄ UTF-8 bytes, with proved
  overlong/surrogate/invalid rejection (the foundational encoding primitive)
- `text`/`textLiteral` (a `String` literal), `identifier`, `many (letter | digit)`,
  and whitespace-as-value (`many (subset isSpace byte)` — lossless, mirroring the
  core's departure #4, *not* the paper's lossy `skipSpace`/`optSpace`) — the
  paper's §6.1/§6.3 combinator library, re-based on bytes and composed over
  `utf8` with `$`.

Their existence is the *acceptance proof* that the core is genuinely extensible;
they are tracked separately, not here.

---

## Open questions (resolve in T0; law shape and byte core are design decisions)

- **`Unambiguous d` predicate** — exact domain of deterministic-decoder
  soundness/completeness (proposal §What we deliberately change, item 2).
- **`ByteArray` proof strategy** (T0.5) — preference: `simp` directly; fallback
  a `List UInt8` model + transport lemma (proof ergonomics only; the API is
  `ByteArray`).
