# Lean proof notes — `lean-codec`

Project-specific Lean 4 / Lake lessons accumulated while building this library.
**This file is the project half of the global `lean` skill**
(`~/.pi/agent/skills/lean/SKILL.md`), which keeps the generic, reusable half and
points here. Format and conventions are the skill's: reverse-chronological, one
focused entry per lesson, `#print axioms`-verified where an axiom claim is made.

**This is lessons, not direction.** What to do next lives only in `AGENTS.md` and
`openspec/changes/<name>/tasks.md`; if an entry here ever reads like a task list,
it is a defect — move it to the ledger.

**Known duplication, stated rather than hidden.** The skill's Append keeps 57
entries that are _also_ present here verbatim (this file holds all 176 of the
original Append; the skill kept the 57 generic ones when the split happened). The
repo's "one source of truth per concern" rule (see `AGENTS.md`) is therefore
violated 57 times today. `tasks.md` 7.4 tracks closing it — either drain the
skill to a pointer, or keep both and keep this note accurate. Do not add a _new_
entry to both files.

**The generic rules live in the skill, not here.** In particular the axiom-hygiene
catalogue is `SKILL.md` §2b; this file is the raw measured record behind it, plus
everything that only makes sense knowing this library (`Codec`, `Bytes n`,
`relRepeat`, `Suffix`, the Layer-2 seams).

Entries below are **verbatim** as they were written in the skill's Append — they
predate this split, so a few are phrased for the skill ("the specific repo lives
elsewhere") in a context where that is now this file. Nothing was rewritten in the
move.

---

- 2026-11-03 — **`Array.toList_extract` and `Array.getElem_extract` both carry `Classical.choice` in Lean 4.34 — so _every_ proof route through `Array.extract` leaves an axiom-clean-only gate, and the readback is where it enters, not `Array.ext'`.** Trying to prove the two spellings of a suffix copy equal, i.e. `a.extract i a.size = (List.drop i a.toList).toArray`, a proof that went through `apply Array.ext'` _compiled_ and then reported `[propext, Classical.choice, Quot.sound]`. Bisecting the footprint (`#print axioms` on each cited lemma in turn) found it is not `Array.ext'`: `#print axioms Array.toList_extract` and `#print axioms Array.getElem_extract` **both report `Classical.choice`**, so any route that reads an `Array.extract` back as a list inherits it. Consequences worth planning around: (a) if you are writing a refinement between an `Array.extract`-shaped body and a `List`-shaped spec, **check the footprint before believing the proof** — the statement looks clean and elaborates fine; (b) the honest fallback is a _measurement plus a recorded decision_ (the fast transport is real and N× faster; it also cannot be connected inside the gate), not a weakened statement and not a `sorry`; (c) check the individual lemma, not just the tactic — `Array.ext'` was the obvious suspect and was innocent.

- 2026-11-03 — **A per-call micro-benchmark of a _pure_ function is CSE'd by default: `timeBatch reps (fun _ => f a)` measures the optimiser, not `f`, when `f a` does not change between reps.** Two implementations of the same pure transport, timed with `timeBatch 30 (fun _ => impl a)` on the same buffer, reported a **2×** ratio; the same comparison with a _different_ input per sample (`pool.getD (i % 4)`) reported **42–44×** — the true figure. The loop-invariant call is common-subexpression-eliminated (or hoisted entirely), so the timed window contains the _first_ evaluation only and the rest is a register read. Mitigations, in order: (a) give each sample a different input from a pre-built pool, never a shared closure; (b) never divide a single-call span by `reps` (a real bug — `timeBatch 1 f` divided by `reps` scales a correct measurement down by `reps`); (c) a wall clock with ~40 ns granularity cannot resolve a ~20 µs call from one sample, so take a **median of interleaved samples** rather than one shot; (d) assert a **data-dependent, non-zero sink** of the result, because a constant-folded or dead result collapses the window to `0 ns` (seen as literally `0 ns/op`). The tell that you have been fooled: a number that is _impossibly_ good for the work described (`0 ns` for a megabyte, or a backend-shaped `41 ns` flat across sizes).

- 2026-11-02 — **`split` on a `match`-with-a-named-equation is itself a `Classical.choice` source, and an _anonymous `by <tactic>` proof inside a `match` arm_ is the other half of the same leak — the two make an unfolding lemma leaky while its statement (and every lemma it cites) looks clean.** A recursive `def` whose body is `match _hm : n - m with | 0 => … | _ + 1 => f … (by omega) …` compiles its successor arm's bound as a tactic proof over facts only the arm knows. Proving the unfolders by `rw [f.eq_def]; split` then reports `[propext, Classical.choice, Quot.sound]`, and so does the same proof of the _zero_ case — even though the surrounding file's other unfolders are clean. Bisection that names it fast: `#print axioms` on each lemma in turn and on the definition; if all are clean but the theorem is not, stub the theorem's body in halves (each `<;> sorry`) and see which half reintroduces `Classical.choice` — here one `rw [fast_succ …]` did, and `#print axioms` on _that_ lemma showed the leak was already in it. **The durable fix is structural, not tactical:** make the bound an ordinary parameter of both the function and its search sibling (the candidate subtype already carries the `≤` field, so it is passed through rather than invented), after which `conv => lhs; rw [f.eq_def]; dsimp only; rw [h]` — the _other_ recipe, which a previous entry says "does not transfer" — works cleanly. So the earlier entry's conclusion was a symptom of this leak, not an independent fact: **when `split` "works but `dsimp only` makes no progress", check the axiom footprint before adopting `split` as the recipe.**

- 2026-11-02 — **To relate two `List.attach` lists of the _same_ provenance, do not rewrite `attach` — read both positionally through `List.getElem?_attach` and prove the correspondence at an index.** Two attached candidate lists (one `{pr // pr ∈ decodeArray …}`, one `{pr // pr ∈ decode …}`) are element-for-element the same sequence, but stating that as `(a).attach = (b).attach.map f` and `rw`-ing the underlying list dies with "motive is not type correct": the `Membership` proof in each element mentions the list. The proof that does go through states the fact **at an index**: `∀ i c s, xs.attach[i]? = some c → ys.attach[i]? = some s → c.val.1 = s.val.1 ∧ …`, and opens both sides with `rw [List.getElem?_attach]` (which turns the read into `Option.pmap Subtype.mk xs[i]? _`), then `cases xs[i]?` and `Option.some.inj`. Two useful corollaries: `simp only [h] at hc` works where `rw [h] at hc` fails when the hypothesis is under an `Option.pmap`'s proof argument; and `List.length_attach`/`List.getElem?_attach`/`List.mem_of_getElem?` are the three lemmas the whole route needs. Pair this with an _alignment_ record (`same length ∧ ∀ i, aligned`), which is what makes an induction over one list usable against the other.

- 2026-11-02 — **`decode_cast`-shaped transport lemmas are needed for _any_ `B`-indexed function, and the cheapest one is `subst` + `rfl` — but it must be proved as its own lemma, because inlining the transport hits the index's dependent motive.** Wanting `decodeFull n s = decodeFull m (cast (congrArg Bytes e) s)` from `e : n = m`, every attempt to `rw [e]` or `subst` at a use site failed on "motive is not type correct" (the `Bytes` argument's index). Proving `theorem decodeFull_cast (e : n = m) (s : Bytes n) : decodeFull n s = decodeFull m (cast … s) := by subst e; rfl` took one line, and every later `rw [decodeFull_cast … e …]` then fired. Same pattern as the pointwise-equality rule for indexed carriers: **state the transport as a lemma at the type the consumer's motive wants, then rewrite with it** — do not try to make the consumer's goal reduce. Also: when the equation is `Nat.sub_zero`-shaped (`n - 0 = n`), `rw` on it in a `B`-indexed goal is blocked exactly the same way, and the cast lemma is again the way through.

- 2026-11-02 — **`mutual` is a _command_, so a `/-- … -/` doc comment cannot attach to it — and a `set_option … in` placed between the doc and `mutual` is a parse error, not an option.** Writing a documented mutual block, the doc comment above `mutual` fails with "unexpected token 'mutual'; expected … 'def' … 'theorem' …". The cause is that `mutual` is a command form with no declaration to attach a doc to, so the doc comment has nothing to bind and the parser expects a real declaration next. Two spellings work: use a **plain `/- … -/` block comment** (which is what the file's existing, compiling mutual pair already does — check before "fixing" it), or move the doc onto the first `def` inside the block. A `set_option foo in` must go _inside_ the block or _before_ the doc comment, never between the doc and `mutual`. Cheap to fix, but the error text points at `mutual` and reads like a syntax catastrophe when the real problem is the doc comment.

- 2026-11-02 — **A hypothesis you are told to "thread as a parameter" may still be unusable where it is needed: check whether the _use site_ can see it, not whether the _signature_ has it.** Adding `hk : i < a.size` as an explicit parameter of a recursive function does make `termination_by`/`decreasing_by` see it, as intended. But if the recursive call's own argument is an _anonymous proof_ (`by omega`) over facts produced by a _tactic application inside a `match` arm_, `omega` sees none of those facts — the arm's context is not in scope for the argument's elaboration block, and it reports a counterexample that contradicts a hypothesis printed right above it. Two working fixes, in order of preference: (a) **put the fact in a type rather than a hypothesis** — a subtype whose `property` the recursive call reads off a named field, e.g. `{ pr : α × Nat // pr ∈ l ∧ k < pr.2 ∧ pr.2 ≤ n }`, so the discharge is a projection rather than a tactic; (b) hoist the fact into a `have` _outside_ the `match`. Also worth knowing: the "outside `match`" version needs `rfl`/`exact` of the named field and must not depend on `omega` seeing through a `let`.

- 2026-11-02 — **A bound you want is often one-sided for a real reason: `≤ n`, not `< n`, because a zero-consumption step exists.** A natural-looking candidate invariant ("every decoder result consumes strictly fewer than the remaining bytes") is **false**, not merely awkward: a `pure`-like leaf returns the _same_ cursor (`c = i`), so the honest statement is `c ≤ n`. `lt` there fails with a goal that looks like an arithmetic difficulty but is a false theorem. The general lesson: when an arithmetic goal in a well-foundedness proof "will not close" despite plausible hypotheses, first ask whether the bound is _actually_ what you wrote — check an exhaustively-`#eval`'d statement of it, or find the degenerate constructor (`pure`, `empty`, identity suffix) that refutes it. Correcting `<<` to `≤` in both the subtype _and_ the lemma took one edit; raising the priority of the exhaustiveness check is the durable fix.

- 2026-11-02 — **An "unfold recipe" that worked for one definition is not transferable to a sibling that differs only in _what its body mentions_, and the failure looks like "motive is not type correct".** A recursive definition's unfolding lemma was proved with `conv => lhs; rw [f.eq_def]; dsimp only; rw [h]`. The sibling definition — same recursion scheme, same `match _ : n - m with` shape — fails this recipe twice over: `dsimp only` reports "made no progress", and without it `rw [h]` reports "motive is not type correct" because the discriminee has been generalized to a fresh binder (the body mentions an extra parameter, so `.eq_def` abstracts it). The fix is `rw [f.eq_def]; split` with the branches closed directly (and, for a `match`-in-`match` body, `simp only` to force the inner one, then `split`, then `injection` on the discriminant equation to realign `split`'s freshly-named binders with the ones in the statement). **The diagnostic:** when a copied recipe fails with "motive is not type correct", do not hunt for the right lemma — print the _unfolded_ goal (`trace_state` after `rw [f.eq_def]`) and look for a `⟨x✝, c✝⟩`-style generalized binder; then choose `split` over `rw`.

- 2026-11-02 — **`filterMap`-based candidate lists need a _length_ bound lemma, and `List.length_filterMap_le` already exists with its arguments in `(f, l)` order.** An auxiliary list built by `(l).attach.filterMap (fun p => …)` is the right shape for "keep the membership witness while dropping the ones that fail a decidable test", but a well-foundedness measure that counts its length then needs `(filterMap f l).length ≤ l.length`. Writing that by hand (`induction`, `List.filterMap_cons`, `split`, `omega`) works but is unnecessary: `List.length_filterMap_le` is in the stdlib and takes **`f` first, then `l`** (`List.length_filterMap_le f l`), unlike most `List.*` lemmas — a `_ le _`-style argument order is the trap. Compose with `List.length_attach` (a lemma, not a function: use `List.length_attach` bare, not `List.length_attach _`) for `attach`-based lists.
- 2026-11-02 — **A hypothesis you are asked to "derive" may be _strictly stronger_ than the hypotheses it is supposed to follow from — and the gap is usually a hypothesis the statement forgot, not a missing tactic.** A biconditional was recorded as taking `huniq : one value-list per fully-consumed input` as an assumption, with the task "derive it from `unambiguous d`". It is **not** derivable: `unambiguous d` is `∀ ⦃x y⦄ {n} (s : Bytes n), R x s → R y s → x = y` — one _value_ per byte string, at a _fixed_ length. `huniq` needs one _list_ per fully-consumed string, and the list length is pinned by neither. A relation that relates `a` to the empty string makes `[a]` and `[]` both fully consume it, and both are `unambiguous`-compatible. ~~What the derivation actually needs is a **productivity** hypothesis (`∀ a s, R a s → n ≠ 0`) alongside unambiguity.~~ **CORRECTED 2026-11-01: that is also false, and it is now a theorem.** `relUnambiguous` + productivity still does not give `huniq`: `Codec.huniq_not_derivable` exhibits a relation (`uniqCounterexampleRel`) that is both unambiguous and productive, yet at `n = 2` admits _two distinct_ fully-consuming lists of one string. What is actually needed is a **length-determinacy** condition — each value relates only at one length — which pins the _number of steps_, not just each step's length; see `Codec.LengthConst` / `relRepeat_length_of_const` / `lengths_eq_of_const` and `relRepeat_unique_same_length`. **The general lesson this cost two false repairs:** a "we just need hypothesis H alongside the others" diagnosis is itself a claim to test with a counterexample, not to record as the fix — I recorded one here that a later session had to overturn. **The diagnostic that saves a session:** before proving `H₁ → H`, ask what `H₁`'s own quantifier structure _says_, then try to build a two-element counterexample from a degenerate relation (`Rel a emptyBytes`). If the counterexample exists, the plan is wrong, and the fix is to _state the extra hypothesis_ and record that the original derivation was refuted — not to keep hunting for a tactic that closes a false goal. Two hours of `rw`/`intro`/`instance` fights produced no progress at all, and every error pointed at elaboration, never at the statement.

- 2026-11-02 — **A "discharge this hypothesis for a concrete case" task is a _test_ of the definition, so make the test able to fail.** Adding `instance`-style base facts (`unambiguous (byte)`, `functional (byte)`) for predicates that had only ever been _hypotheses_ is worth doing even when the proof is trivial, because it is the only thing that can catch a typo in the definition — but only if you **verify load-bearingness by mutation**: temporarily weaken or re-spell the definition (e.g. quantify over two independent byte strings instead of one) and confirm the instance's proof then _fails_. If the mutated version still proves, the instance is vacuous and tests nothing. This is the same discipline as proving a `sorry`-gate is real by stubbing a theorem and watching the build fail — the check is cheap and it is the difference between "we have a test" and "we have a ceremony".

- 2026-11-02 — **A proof obligation stated at `USize`/`Array`-level arithmetic must be _verified by exhaustive `#eval`_ the same way a `Nat` identity is, and the answer is often "equal because `min` is AC, not because the code matches".** Two implementations of the same clamped-window update were documented as agreeing "term-for-term"; they do not — one computes `min len (min (n-dc) (slen-sc))` and the other clamps sequentially (`len` against `n-dc`, then the result against `slen-sc`). They agree **value-for-value** by associativity and commutativity of `min`. That distinction is the whole content of a trust-seam argument: a reader who compares the two line by line will "fix" a difference that is not a bug, and a reviewer who is told "identical" will not look for the real invariant. Write the _reason_ (AC) and the _order actually used_, and check it exhaustively over small values (`n, slen < 6`, offsets/`len < 9` is 2.3M tuples and runs instantly). Same entry point as the `Nat`-identity rule: one `#eval` line, before writing the prose.

- 2026-11-02 — **`trace_state` is the fastest way out of a "Type mismatch / Application type mismatch" loop whose error message names a _hypothesis's own_ type rather than your argument — and the answer is often "your lemma is about a different `α`".** A long chain of `exact h …` failures kept reporting that a `relRepeat`-shaped hypothesis "is expected to have type `R ?m ?m`", i.e. as if it were a single-step relation. The cause: the quantifier/predicate being applied was monomorphic in the _element_ type, and at the application site `α` was still a metavariable, so Lean instantiated it wrongly and then complained about the argument. Three things that worked where guessing did not: (a) `trace_state` in the failing branch prints every local and its **elaborated** type, including the invisible instantiations — read that before touching tactics; (b) `#check @thm` prints the _explicit-implicit_ binder order, so you learn whether `h s h1 h2` or `h h1 h2 (by …)` is the shape (an `intro`-order mismatch like `{x y} {n} (s)` vs `{x y} (s) {n}` is invisible in the source); (c) if the lemma's own `α` is what is stuck, **state the helper with its own concrete `α`** rather than threading an `@`-application through — a small reshuffle of _which_ lemma quantifies over what is usually cheaper than fighting the elaborator.

- 2026-11-02 — **When a proof has failed 4–5 times on _shapes_ rather than mathematics, stop and check whether the auxiliary lemma is true, not whether it is provable — a `False` goal often means the lemma's `→` direction is genuinely refutable.** A `nil`-case elimination (`relRepeat R xs 0 emptyBytes ↔ xs = []`) looked obviously true and was refuted: `relRepeat R (x :: xs) n s` is `∃ m (hm : m ≤ n) …, s = splice hm s₁ s₂ ∧ R x s₁ ∧ relRepeat R xs (n - m) s₂`, and at `n = 0` **no field of it contradicts anything** — `m = 0`, `s₁ : Bytes 0`, and `R x s₁` is unconstrained by the definition. So the `cons`-at-length-`0` case is _satisfiable_ unless the relation is productive, and the `↔` is false. The tell was that every failure was `Nat.not_succ_le_zero`/`omega` "no usable constraints", i.e. the arithmetic genuinely had nothing — never a motive or rewrite problem. **Rule: if `omega` reports _no constraints_ on a goal that you believe is arithmetic, the goal is not arithmetic; it is a missing theorem or a false statement.** Cheap falsification: instantiate every existential with its degenerate value and see whether the hypothesis is still satisfiable.

- 2026-11-02 — **When `rw [f.eq_def]` fails with "did not find an occurrence of the pattern `n - m`" on a `match`-defined function whose scrutinee is _plainly_ present, the missing step is a bare `dsimp only` between the two rewrites — not a `cases`, not a `split`, not a restatement.** A structurally recursive `def` compiled from `match n - m with …` elaborates to `match n, s, m, acc with | n, s, m, acc => match _hm : n - m with …`, i.e. an outer **tuple-of-all-arguments** match. `conv => lhs; rw [f.eq_def]` produces that wrapper; the inner `n - m` is then not syntactically reachable, so `rw [hk]` reports the pattern as absent and the error reads like a wrong-lemma or wrong-type problem. The working recipe is exactly three steps: `conv => lhs; rw [f.eq_def]`, then `dsimp only`, then `rw [hk]`. Same shape at a _successor_ scrutinee and at a _zero_ one. **Package it as a named lemma the moment it works** (one for each constructor form of the scrutinee) rather than re-deriving the recipe at every call site — this is a proof-engineering step that took several failed sessions to name, precisely because every failure mode looks like a type error. Corollary: if `split` keeps producing case tags that do not match (`h_1` alone, or a binder named `heq`), and `cases n - m` renames the equation out of the hypotheses, you are in this situation — reach for `dsimp only` first.

- 2026-11-02 — **A typeclass argument (`Membership`, `DecidableEq`, `LE`) is selected on the _syntactic head_ of a type, so two definitionally-equal spellings of the same list type get _different_ instances — and the error looks like a wrong-type error, not an instance error.** With two aliases whose element subtype is spelled `decode p (drop m s).bytes` in one place and `decode p (drop 0 (drop m s).bytes)` in another (`rfl`-equal, verified), passing a list of one to a function expecting the other fails with `Application type mismatch: The argument List.instMembership has type Membership (α × S (drop 0 (…)).rem) (List (…)) but is expected to have type Membership (α × S (drop m s).rem) (List (…))` — the complaint names `List.instMembership`, not your term, which is why it reads as nonsense. **Rule: when two spellings of a list/scalar type are only _definitionally_ equal, do not mix them** — pick the spelling the consuming function's own signature produces, and state any helper lemma at that spelling. This is a distinct trap from rewriting under `List.attach`: nothing here is a `rw` motive problem, it is instance resolution, so `cases`/`rfl`-per-branch does not help and the fix is purely to unify the spelling.

- 2026-11-02 — **`#eval` a `Nat`-subtraction identity _exhaustively over small values_ before writing a lemma for it, and treat any `omega` counterexample report as evidence that the identity is false rather than that `omega` is weak.** Two sessions were lost to identities like `n - (m + (n - m - r)) = n - m - r` that "looked right" and are **false** (`r = 0, m = 0, n = 1` refutes it), while the true statement was `… = r`. The check costs one line and settles it:

  `#eval (List.range 8).all (fun n => (List.range 8).all (fun m => (List.range 8).all (fun r => if r ≤ n - m then decide (<candidate identity>) else true)))`

  A `false` tells you to re-derive the identity; a `true` tells you the statement is right and only the proof is missing. Relatedly, `omega` cannot derive `m ≤ n` from a hypothesis mentioning `n - m`: truncated subtraction collapses both `n ≤ m` and `m > n` to `0`, so **any lemma about `n - m` must be case-split on `Nat.le_total m n` first**, with the degenerate branch closed by `n - m = 0 → r = 0`.

- 2026-11-02 — **`conv_lhs`/`conv_rhs` do not exist in Lean 4.34.1 — use `calc`, `nth_rewrite`, or a named `have` — and there is no `List.bind` (it is `flatMap`) nor `List.filter` returning `Option` (it is `filterMap`).** A tactic block written from memory with `conv_lhs => rw […]` fails with a bare `unknown tactic`, which reads like a missing import; likewise `l.bind` fails with `Invalid field 'bind': the environment does not contain 'List.bind'`. Neither is recoverable by `open`, so grep the toolchain rather than assuming the mathlib-era spelling. `conv => lhs; rw […]` (the non-suffixed form) is also unavailable here, so prefer `calc` chains — they are clearer anyway when the goal is a multi-step `Nat` identity.

- 2026-11-01 — **A `termination_by` `Prod.Lex` ranking that "works" for the definition can still make the theorems unprovable — check the _proof_ shape before committing to the measure.** A `mutual` pair where the caller is ranked `(·, n + 1)` and the callee `(·, n)` type-checks fine, but `Prod.Lex` then has **no reflexive case**, so when you want to prove _both_ members' congruences at the same state, neither can call the other at an equal key: the induction hypothesis is only available _strictly below_ the current key. Symptom: the base cases and all the unfolding go through, and the only failure is the hand-off ("expected `Prod.Lex … (state) key`, got `Prod.Lex … (a, b) (a, b.succ)`"). Fixes, in order of preference: (a) state the two facts so that the one that needs the other is ranked _lower_; (b) prove the pair at one key in a single statement whose induction hypothesis is the _conjunction_ (the recursor then hands you the sibling at the same key); (c) re-rank the definition so the _descending_ direction is the one that carries the `+1` tick. Do not try to discharge an equal-key edge — there is nothing to discharge it with. **Follow-up (2026-11-02), because this entry's framing sent a later session down the wrong path for hours: prefer (b) _first_, and treat it as the intended route rather than a last resort.** When you are proving _two_ facts about a `mutual` pair, put **both** in the caller's motive (`motive1` = `fast ∧ search`) and let the recursor's own callee-hypothesis (`motive2`, which the `mutual_induct` already hands you at a strictly shorter sub-measure) supply the sibling. That works with **no** re-ranking, **no** change to the `termination_by`, and **no** change to any declaration's shape — so fixes (a) and (c), which both mean editing the definition, are usually unnecessary. The tell that (b) is available: `#check @f.induct` shows two motives, one per member; if so, the pair is already reachable and the "ranking obstacle" is not real.

- 2026-11-01 — **When two mutually-recursive functions' hypotheses mention a list _derived from_ the input, quantified independently, the empty case is usually unprovable — couple them with a definitional `cast` instead.** A congruence lemma stated `∀ (cs : EntriesAt m) (cs' : EntriesAt 0), f m cs = f 0 cs'` is _false enough to be unprovable_ at `cs = []`: the empty hypothesis constrains only one list, and `cs'` may still be a `cons`. The two lists are in fact the same `List.attach` at two indices differing by a `bdrop 0`-style identity, so state it with **one** list and a re-indexing helper (`abbrev retype (cs : A n) : A m := cs` when the indices are definitionally equal). The tell that you got this wrong is a `nil`/`cons` cross-case that needs an `exfalso` you cannot derive — that is a _statement_ defect, not a tactic problem.

- 2026-11-01 — **`rw [f.eq_def]` does not fire on an applied occurrence when `f`'s body is a `match` nested inside another `match`; `cases` the scrutinee first.** For a function written `| args => match x with | … => match y with | …`, `rw [f.eq_def]` on `f a b c` fails with "did not find an occurrence of the pattern" even though the term is plainly there. Two working routes: `cases` the outer scrutinee (so the application reduces structurally), or state the unfolding as an explicit `have h : f a b c = (match …) := by rw [f.eq_def]` (this form _does_ elaborate when the goal is the bare equation) and then `rw [h]`. Related: a `def` compiled from a `match` with a `_hm :` proof binder produces a _dependent_ `match`, and `generalize`/`rw` on its scrutinee then fails with "motive is not type correct" — reduce it with `cases`/`rfl` per branch rather than rewriting.

- 2026-11-01 — **`Suffix`-style structures whose `drop 0` is written `drop 0 (x.bytes)` infer their index from the _fields'_ dot projection, not the structure's parameter — so the term type-checks in a hypothesis and fails in a goal.** With `structure S (n : Nat) where remaining : Nat; bytes : Bytes remaining` and `def S.drop (m : Nat) (s : Bytes n) : S n := ⟨n - m, bdrop m s⟩`, the term `S.drop 0 (S.drop m s)` (dot-notation argument, no `.bytes`) _does_ elaborate when Lean must infer `n` from it (e.g. `let u := S.drop 0 (S.drop m s)`), but in a **goal** — or inside any function argument whose parameter type fixes the index — it fails with "expected `S n`, got `Bytes n`": the inferred `n` is the _third component_ of the value, while the expected type is the structure's parameter. Write `S.drop 0 (S.drop m s).bytes` in goals. Consequences worth knowing: (i) `.bytes` binds after the _application_, so `(S.drop m s).bytes` is fine but `S.drop m s.bytes` is not; (ii) under a `match`, a `let`, or any `@`-application the inference switches back, so the same expression can elaborate on one line and fail on the next — probe with a one-line `let` before writing a statement around it.
- 2026-11-01 — **In a `mutual` block the first item must be a `def`/`inductive` — a `/-- … -/` docstring immediately after `mutual` is a parse error ("unexpected token '/--'"), and putting the docstring _before_ `mutual` attaches it to the block, not to the definition.** Write the documentation as a plain `/- … -/` or `--` comment above `mutual`, and leave the per-definition docstring out (or `add_decl_doc` it afterwards). The error message is unhelpful because it lists _every_ command head as "expected", which reads like a missing keyword rather than a misplaced comment.

- 2026-11-01 — **A mutual definition's `Prod.Lex` termination measure needs the _entry_ edge to be strictly smaller, so give the entry function one extra "tick".** Two mutually recursive functions on `((remaining, cands.length))` cannot both use the identical measure: the `f -> g` edge at the same `remaining` fails `Prod.Lex.left` (needs `<`) and `Prod.Lex.right` (needs `≤` on the second component, which also fails when the lists are equal). Give the caller `(remaining, decode_len + 1)` and the callee `(remaining, cands.length)`; then `f -> g` is `right` (`cands.length = decode_len < decode_len + 1`) and `g -> f` is `left` (`ConsumesByte`-style strict decrease). Also: there is **no `Prod.Lex.refl`** — every edge needs a real `left`/`right`, so a reflexive edge must be removed by re-ranking, not discharged.

- 2026-11-01 — **When a proof keeps failing on rewrite shapes after 3-4 attempts, stop and question the _statement_, not the tactics.** A bridge lemma `fastRoot = spec` was pursued for dozens of tactic iterations ("did not find an occurrence", "motive is not type correct") before it was tested empirically — and turned out to be **false**: the fast path committed to the first candidate while the spec backtracked. The tell is that the failures are _all about index alignment and match-shape_, never about mathematics; that pattern means the two sides of the equation are not the same function. **Cheap falsification test for any "these two decoders/parsers/evaluators agree" lemma: build a tiny input where they differ structurally, `#eval` both, and compare.** Do it _before_ the proof, not after; a `#eval` line costs seconds and can save a session. This is the same class as the earlier "refuted diagnosis" entries, but the lesson is sharper: a _statement_ can be wrong in a way no amount of tactic work reveals.

- 2026-11-01 — **A `dsimp`/`unfold` early in a proof can silently invalidate a lemma you were about to apply, because it rewrites the _terms inside a dependent type index_.** A lemma `step_bytes_pointwise` was stated at `t : Suffix (Suffix.drop m s).remaining`. Calling `dsimp only [Suffix.drop]` (to expose `remaining` for `omega`) rewrote the root to `n - m`, so `t`'s own type no longer matched the lemma's argument and the application failed with a confusing "Application type mismatch: expected `Suffix (n - m)`" — while looking like a problem with `t`. **Rule: capture every dependent-type fact you will need into a `have` _before_ any `dsimp`/`unfold`**, then do the arithmetic afterwards. Concretely: `have hpt : ∀ i : Fin t.remaining, … := fun i => the_lemma … i` first, `dsimp` second, `rw [hpt i]` last. Corollary: when an "application type mismatch" names a _local hypothesis's_ index rather than the argument you passed, look for a `dsimp`/`unfold`/`subst` earlier in the block — the term was reindexed under you.

- 2026-11-01 — **A `let`-bound value from a well-founded recursor's hypothesis is opaque to `subst` and `rfl`, but you can still name it and rewrite with it.** `decodeFullFast.induct` produces `ihyp : Nat := m + (…)` followed by the actual hypothesis; `subst hsub` and `show … from rfl` both fail on it (the `let` is not a definitional equation the way a binder is). Three things that work: `intro` the cursor and the hypothesis as **separate names** (`intro … mlet mlet_ih`) so neither shadows the other; state the arithmetic as `have hmlet : mlet = <flat form> := by show <its own form> = _; omega`; then `rw [hmlet] at hIH`. Symptom that you hit this: `error: Invalid rewrite argument: Expected an equality … but `ih`is a value of type`Nat`` — the recursor reused your `ih` name for the `let`.

- 2026-11-01 — **Do not develop proofs outside the repo. A working directory is not a version control system, a build gate, or a handoff.** A session produced hours of verified lemmas in a scratch file under `/tmp` intending to splice them "at the end". That file is invisible to `git`, to the `-DwarningAsError` gate (so the half-finished state looks _identical_ to a finished one), and to whoever resumes — and one reboot deletes it. **Write new theorems into the real source file and let the unfinished one carry a `sorry` that fails the build**: the failing gate is the honest, durable marker of exactly what is left, and it is visible to every future reader. Use a scratch file only for the narrow case where the library genuinely does not build and you must iterate against a _built_ dependency — and delete it the moment the real build is green.

- 2026-10-31 — **When an induction's spec index and the recursor's index are numerically equal but not definitionally equal, write the lemma's statement with the _recursor's_ form and the mismatch never arises — and then rewrite only the RHS with `conv`.** Two halves of one fix, both cheaper than any transport argument: (1) a target type `Suffix (n - m)` and a recursor that produces `Suffix (Suffix.drop m s).remaining` are not definitionally equal _in the `Suffix (·)` position_, so an induction hypothesis at one cannot be used at the other; stating the core lemma's conclusion with `(Suffix.drop m s).remaining` makes the `n - m = 0` base case close _outright_ and removes the need to transport anything. (2) Once stated that way, the spec side is reachable with `conv => rhs; rw [recursion_eq …]` — rewriting **only the right-hand side** so that a hypothesis whose type depends on the left-hand term (e.g. a `have hmem :=` produced by a `mem`-style lemma) is never touched, which is exactly what a whole-goal `rw` would break. General rule: when a lemma is stuck because one side's type index has a reducible-but-not-definitionally-equal alias, **choose the alias the recursor generates** rather than proving they agree.

- 2026-10-31 — **"Motive is not type correct" is almost always a dependent `rw`, and the fix is to change the _statement_, not to fight the tactic.** A rewrite fails when it must abstract over a term that other hypotheses or the goal's own type depend on. Three shapes, all hit in one session, with the fix for each:
  1. **Rewriting under a `List.attach`.** `l.attach` carries a `Membership` proof per element, so any term mentioning `x ∈ l` depends on `l`; `rw [h]` on `l` then fails. Fix: take the list as a **parameter** and `cases`/`induction` on it — never rewrite it. (`cases d` then `simp only [List.attach_cons, List.cons.injEq, Subtype.mk.injEq]` reduces both sides to `… = hd`, and the pair is then proved by transitivity.)
  2. **Rewriting a `Finset`/`Sigma`-packed index.** `rw [hk]` inside `f ⟨n, s⟩` cannot abstract because `s : Bytes n` mentions `n`. Fix: state the lemma with the index **abstract and the equality as a hypothesis** (`∀ k t, k = 0 → f k t = …`), so the caller supplies the arithmetic and no in-place rewrite is needed.
  3. **Rewriting a length inside an indexed type.** `Suffix (Suffix.drop m s).remaining` and `Suffix (n - m)` are numerically equal but **not definitionally equal in the `Suffix (·)` position**, so an induction hypothesis at one cannot be used at the other. Fix: write the _lemma's statement_ using the form the recursor actually produces; the mismatch then never arises. Do not try to transport it.
     Corollary: **rewrite one side at a time.** `conv => rhs; rw [eq]` reaches the conclusion without touching a hypothesis whose type depends on the term, and is often the difference between a 5-line proof and an unfinishable one.

- 2026-10-31 — **For a `Bytes`-like indexed carrier, state equalities _pointwise_ (as reads at indices) to avoid a length cast that then blocks everything.** The natural `Bytes`-level lemma (`t.bytes = drop …`) forces a cast at the index (`drop o s : Bytes (n - o)`, not `Bytes t.remaining`), and that cast is opaque to `rw`: every downstream rewrite fails with "motive is not type correct". Stating the _same_ fact as `t.bytes i = s ⟨i.val + …, _⟩` for `i : Fin t.remaining` has **no cast anywhere**, and the downstream proof becomes `Fin.ext` + `omega`. This was the single decision that unblocked a month-long stuck proof; the cast form was a dead end attempted many times.

- 2026-10-31 — **`omega` will not use a hypothesis whose type contains a projection that hasn't reduced.** `t.hle : t.remaining ≤ (drop m s).remaining` looks usable, but `omega` sees the `drop` and gives up. Fix: **restate it numerically first** — `have h : t.remaining ≤ n - m := t.hle` — then `omega` closes immediately. Same class as the modulo rule: `omega` wants a plain numeric hypothesis, not one wrapped in a definition.

- 2026-10-31 — **`congr 2` can be the entire proof of a `WellFounded.fix` recursion equation, and is load-bearing when it is.** To unfold a `WellFounded.fix`-defined recursive function at a `Nat.succ` index: `rw [f, WellFounded.fix_eq]` then `simp only [Nat.add_one]` then `congr 2`. The last step discharges the residual comparison of the fix's `ih` against the function itself — which _is_ the fix point, definitionally — so the goal does not close without it. Do not delete it as "redundant"; a `congr` that seems to do nothing may be doing the only step that matters.

- 2026-10-31 — **A `match`-based recursion's `.eq_def` rewrite is often a complete proof, so follow it with nothing.** `rw [f.eq_def]` on a `match`-defined function whose scrutinee is already a known constructor form reduces the goal entirely; appending `cases`/`simp` to be safe then errors with **"No goals to be solved"**. If a tactic line errors that way, the fix is to _delete the following lines_, not to add `try`.

- 2026-10-28 — **A lazily-composed _input_ is the same trap as a lazily-composed result: feeding a "dropped prefix" function its own output builds a closure chain, and reading through it is Θ(depth).** A decoder returned its remainder as a function (`drop k s` is a _closure over `s`_, cheap and non-copying) — which is the right design for memory, and the wrong one for iteration. Passing that remainder back in as the next step's input **composes** the closures, so reading byte 0 at depth `k` applies `k` closures: O(1) per step becomes O(k), O(n) becomes Θ(n²). Measured on otherwise identical work (n `decode` calls, same helpers): **chained remainder 92,876 µs vs re-derived from the root 139 µs at n=4096 — 668×**. Fix: keep the **original** input fixed and carry a consumed-count cursor, re-deriving each step as `drop m root`; the composition lemma (`drop m (drop k s) = drop (k+m) s`, up to the length cast the type index forces) is what licenses it. Effect: 24.9 s → 2.75 ms at n=65536, and the walk goes linear. **Diagnostic**: if a "fast" lazy carrier is O(1) per step yet the whole run is super-linear, time `chained` vs `flat` over the same helpers — a large gap is the chain, not the algorithm. Corollary: this is invisible to `#print axioms` and to any per-operation profile; only an end-to-end A/B that differs in _exactly_ this one dimension finds it.
- 2026-10-28 — **The _result type_ decides the order of magnitude, and the gap between a `List`-returning and a cursor-returning step is ~5× on the same reads.** Same data, same machine, same run, one process — measured against a `memcpy`-class bulk op as the C reference:

  | path                                               | MiB/s   | vs `memcpy` |
  | -------------------------------------------------- | ------- | ----------- |
  | `memcpy`-class bulk op                             | 1,891   | 1×          |
  | **bulk cursor decode** (read a byte, `Array.push`) | **222** | **8.5×**    |
  | plain `Array.get` loop                             | 307     | 6.2×        |
  | per-step `List` decode (`[(a[i], i+1)]` per byte)  | 40      | 47×         |
  | backtracking _search_ decoder                      | ~0.01   | ~10^5×      |

  **Rule: a small single-digit multiple of C is reachable in pure Lean** (`Array UInt8` + an integer cursor + an `Id.run do` accumulating loop, ~8.5×), so "Lean is 20-40× off C" is an _architecture_ statement, not a language one. A path that is 47× is returning a `List` per step (a cons cell + `Prod` + boxed `Nat` for what is one array read); a path that is 10^5× is doing a **search** where a single pass would do. Diagnose by measuring one step in isolation: 6,100 µs for n steps of "one array read" vs 767 µs for the same reads in a plain loop is a 8× that no scalar-type change can touch. Corollary: assert the **ratio to a same-run `memcpy`**, never an absolute MiB/s floor — an absolute floor is machine-dependent and gets tuned down the first time CI is slow, while the ratio is the property you actually mean. Corollary 2: when the requirement is "within N× of C", make the _result type_ the first design question, before any FFI or backend work.

- 2026-10-28 — **`termination_by` and `WellFounded.fix` are the SAME recursion — so "re-express it structurally" is never a performance fix.** A function defined by `WellFounded.fix (InvImage.wf (fun x => x.1) Nat.lt_wfRel.wf) …` looked like the obvious culprit for a ~500× slowdown (its emitted IR genuinely contains `lp_WellFounded_fixC…` and allocates a closure per level). Rewriting it with `termination_by n _ => n` + `decreasing_by` changed the time by **0.5%** (93,691 vs 94,137 µs at n=4096). Seeing scary machinery in the emitted C is not evidence that it costs anything — measure that layer too. **Decompose before you rearchitect:** time the components in isolation (here: all n `decode` calls in a plain loop = 140 µs; `.attach` = nil; building the result list = nil; the composite = 91,382 µs). If the parts are cheap and the whole is not, the cost is in how they are **composed** — which is where the _next_ entry starts. (This entry originally concluded "the cost is a backtracking search, fix it by a single-pass fold"; that was **wrong**, and the correction is worth recording: a tail-recursive rewrite making the _same_ calls was **still** 1.5 s at n=16384. Decomposition narrows the suspect; it does not name it, so do not ship a conclusion from it without an A/B that differs in exactly one dimension.)
- 2026-10-28 — **Measuring Lean performance has three traps that all report `0 us` or a plausible-but-wrong number; force the value or you measured nothing.** (1) **`lake env lean file.lean` _interprets_** — it does not compile, and a `main` defined there **does not run at all**, so timings from it (or from `#eval` on a large computation) are meaningless; you need a real `lean_exe` (`lakefile.lean`: `lean_exe foo where root := \`Foo`) and run the built binary. (2) **Dead-code elimination**: if you time `(f x).length`or`(g x).1`, the compiler can compute only the length/index and elide the payload — a function that *should* take seconds reports `0 us`while printing a correct-looking answer. Force the whole value through a returned tuple, e.g.`let (out, dt) ← timeBatch 1 fun _ => f x`where`timeBatch`returns`(α × Nat)`, exactly the shape a bench harness should have. (3) **A warm-cache first call is not a measurement**, and neither is one run — batch `reps`and divide, and sanity-check by scaling`n`(a clean 4× time for 2× size means Θ(n²), which is usually a bug, not a constant factor). **Acceptance test: if any of your lanes reports`0 us`, treat it as "not measured" and fix the forcing — never as "instant".** Corollary: an A/B must differ in _exactly one_ dimension; hold the types, the helpers, and the input identical, so the delta is attributable.
- 2026-10-27 — **`decide_eq_true (by omega)` on a _disjunction_ leaks `Classical.choice` — `omega` closes a `∨` by case analysis (trichotomy), so building the disjunct explicitly is the fix.** `#print axioms` on `theorem t (n : Nat) (h : 65 ≤ n ∧ n ≤ 70) : decide ((48 ≤ n ∧ n ≤ 57) ∨ (65 ≤ n ∧ n ≤ 70)) = true := decide_eq_true (by omega)` reports `[propext, Classical.choice, Quot.sound]`, while `decide_eq_true (Or.inr h)` on the same goal is clean. `decide` is not the problem — the _disjunctive_ proof handed to it is. This is the same `Nat.lt_or_gt_of_ne`/trichotomy family as the earlier `omega`-disjunction entry, but the composition trap is far more common and is easy to miss because the goal looks like plain arithmetic: **rule — in a `Classical.choice`-gated law, never hand `omega`/`by_contra`/`decide_eq_true` a disjunctive goal; build the disjunct with `Or.inl`/`Or.inr` and let `omega` close only the conjunctive/arithmetic leaf.**
- 2026-10-27 — **A `match`/`if` on a `Bool` _in the goal_ (with `h : b = true` in context) is a dependent match: `subst h; rfl` and `cases b` both fail.** The symptoms are "`rfl` failed: the left-hand side `match true, ⋯` is not definitionally equal to …" and, for `cases`, "Dependent elimination failed". Neither is a `Classical.choice` leak — it is the motive mentioning the discriminee. Fix: `cases b <;> simp_all`, or restate so the match is not dependent (move the discriminee into a hypothesis), or prefer `if h : p then` to keep the fact in the branch. Recorded separately from the leak catalogue because the _fix_ is different: no axiom problem, just a motive problem.
- 2026-10-27 — **`if_pos`/`if_neg` are deprecated in favour of `ite_eq_left`/`ite_eq_right` — and the replacements are _applied_, not `rw`-able and not `Iff`s.** Both halves are deprecated (not just `if_neg`), so a repo-wide `if_pos`/`if_neg` habit emits warnings that a `-DwarningAsError` gate turns into build failures. The shapes are `ite_eq_left : c → (if c then t else e) = t` and `ite_eq_right : ¬c → … = e` — functions of a proof argument. Write `exact ite_eq_left h` or `rw [show (if P then a else b) = a from ite_eq_left h]`; `rw [ite_eq_left]` bare and `.mpr` **do not work** (no `Iff` projection to take).
- 2026-10-26 — **When a proof refuses to compile and you want a clean slate, never `git stash`/`git reset`/`git checkout --` the file — move the broken _theorem_ to a `sorry` instead, so the library still builds and you can iterate in a scratch file.** Debugging a hard lemma, the library is unbuildable, so `lake env lean` on a scratch probe fails too ("olean does not exist") — which tempts a "revert and start over". Reverting broadly destroys verified sibling work (it did, mid-session). The cheap, safe move is to stub the one declaration (`:= by sorry`), let `lake build` go green, then iterate the real proof in `/tmp/probe.lean` against the built library — with `sorry` you also get the _goal state_ printed, which is usually the fastest way out. Commit incrementally (one base / one law family per commit) so a revert is never tempting.
- 2026-10-26 — **`simp [f] at h` where `f` matches on a list _nested one level deeper_ than `h` shows will leave an unreduced `match` — `rcases` the list down to a concrete length first.** `b32TailUnapply (v0 :: w :: r2) = some a` reduces only after `r2` is known to be `[]`/`[_]`/`[_,_]`, because the `def`'s match covers 1–4-element lists; `simp only [unapply, blockUnapply, Option.some.injEq] at h` then `subst h; rfl` per arm is the reliable pattern, and the _impossible_ arms (5+ elements) reduce to `none = some a` and close by `simp [unapply] at h` alone. Also: a `simp` argument reported "unused" in one arm is usually needed in the _other_ arms — don't delete it globally, delete per-arm, or you trade a warning for a compile error.
- 2026-10-26 — **Generalising a "named vector" rejection proof to a _for-all_ law: the arity case is free once you have the two region-length lemmas — `n = k·(|a| + |b|)`, then `Nat.mul_mod_right`.** A queue item billed as "the only genuinely hard one" (`n % 4 ≠ 0 → decode s = none`, for a decoder that splits into a _repeat run_ plus a _terminal element_) needed no case-split over examples: the run-length lemma gives `n - t.remaining = k · blocks.length`, the tail-length lemma gives `t.remaining = k · tails.length`, the two regions partition `n` (needs the suffix's own `≤` witness, **not** just the equations — `omega` stalls without it), so `n = k · (blocks.length + tails.length)` and `rw [hn, Nat.mul_mod_right]` closes. Corollary worth checking _before_ assuming difficulty: `omega` **cannot** derive `n % 4 = 0` from `∃ k, n = 4 * k` — it does not reason modulo; always convert to the equational form and rewrite.
- 2026-10-26 — **"Invalid byte at _any_ index" generalises cleanly by proving _every consumed byte_ satisfies the (weaker) alphabet-or-pad predicate, then splitting the index on the region boundary — do not try to re-index into the run.** For a whole-input decoder = _run of an alphabet-only element_ then _a padding-capable terminal element_, `∀ i : Fin n, OrPad (s i) = true` follows from: `relRepeat_forall` on the run (each block byte is `Char`, hence `OrPad`), the terminal element's own `count k (satisfy OrPad)` window for the tail region, and a `by_cases i.val < n - t.remaining` split. The tail-region read is the only fiddly part; **`bdrop_prepend`** (`bdrop (n - t.remaining) (t.prepend s₀) = cast … t.bytes`) gives it in one step — far cheaper than re-deriving `splice_suffix_read`. A useful bonus: this single lemma subsumes a whole family of "byte at index k is bad" vectors.
- 2026-10-26 — **For "a `=` may only appear at position ≥ 2 of the padded block", enumerate the block-encoder's _value shapes_ (1/2 or 1/2/3/4 bytes) — and remember the 1-byte shape's slot 1 is an alphabet char, not the pad.** A tail-block window is `[c₀, c₁, =, …]` (`[c₀, c₁, c₂, =]`, etc.); slots 0 and 1 are always `valToDigit` outputs (`valToDigit_not_pad`), and the pad run starts at slot 2 in _every_ shape including the 1-byte one (whose window is `[c₀, c₁, =…]` — slot 1 is still `valToDigit`). Getting this wrong in a comment ("slot 1 is the pad in the 1-byte shape") sends the proof chasing an unreachable case; the goal state (`hi : s ⟨1,·⟩ = 61` alongside `hsl : some [c₀, c₁, 61, …] = some a`) is what corrects you. Practical shape: prove two small `have`s — slot 0 is `valToDigit (v0 / k)`, slot 1 is `valToDigit (…)` for the 2+-byte shapes and the 1-byte shape's own second char — each by `rcases`-ing the tail list to concrete lengths and `simp only [unapply, blockUnapply, Option.some.injEq] at h; subst h; rfl`. The 5+-byte arm closes with `simp [unapply] at h` alone (`none = some a`).
- 2026-10-26 — **`rw`/`congrArg` on an index _into_ a `bdrop`/`concat` result fails with "motive is not type correct" when the index's `Fin` proof is `omega`-generated — compare _values_ instead, or `dite`-normalise, never rewrite the index.** Reading `(bdrop m s) ⟨k, _⟩` and wanting `s ⟨k + m, _⟩` needs an equality of `Fin`s whose second components are unreconcilable `omega` proofs; `rw [hidx] at hc` then fails on the motive. Two shapes that work: (a) build the equality with `congr 1; exact Fin.ext (by simp; omega)` (replace both sides by the same _value_-indexed term, let proof irrelevance handle the rest); (b) `simp only [cast_bytes_val_symm]` to strip a `Bytes` length cast, then `congr 1` + the `Nat` arithmetic lemma (e.g. `Nat.sub_sub_self`). Useful invariant: if a residual `cast ⋯ t.bytes` survives your rewrites, the two `fst`s are not syntactically equal and you are fighting the wrong shape.
- 2026-10-26 — **`Bytes n := Fin n → UInt8` equality needs `funext`, so `decide` can NEVER
  close a `Bytes` goal — and that silently makes "write a concrete expected value" proofs look
  impossible. The fix is `Bytes.ext` + one `rfl`/`decide` per index, NOT a better simp set.**
  Writing value-assertion tests for a concrete encoder (`example : encode v = some ⟨4, f⟩ := by
decide`) fails with "`Decidable` instance did not reduce" — the `instDecidableEqBytes` instance
  bottoms out in `Nat.decidableBallLT` over `Fin`, which cannot see through the function. Two
  further traps hide behind it: (1) `decide` on a _`Bytes` index_ after `intro i` fails with
  "Expected type must not contain free variables"; (2) `Bytes k` literals styled
  `fun i : Fin k => [a,b,c][i]` compare fine, but only index-by-index.
  The working shape (8 lines, closes with zero surprises):

  ```lean
  example : encode v = some ⟨4, fun i : Fin 4 => [0x5A,0x67,0x3D,0x3D][i]⟩ := by
    rw [encDef, splitDef]           -- reduce to the block/tail composition
    simp only [...the element defs...]
    refine congrArg some ?_
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Bytes.ext
      intro i
      match i with
      | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl | ⟨2, _⟩ => rfl | ⟨3, _⟩ => rfl
  ```

  **Do not try to generalise this into a `macro "…" : tactic`** — a tactic macro's
  `` `(tactic| …) `` body does not see the `i` introduced by the caller's `intro i`, so the
  trailing `match i with` arms fail or the goal is reported unsolved. Keep it inline
  per-example to generate from a script, and keep the `simp only` list **per-shape**: an
  over-broad list produces `linter.unusedSimpArgs` warnings on the shapes where a branch is
  unreachable (multi-block inputs never reach the tail), which breaks a zero-warning gate.
  Scope the linter off at file level with `set_option linter.unusedSimpArgs false`
  (`set_option … in` only scopes ONE declaration, so it does not help a run of examples).

- 2026-10-26 — **`dsimp only []` is NOT always a no-op; "remove the no-op" can break the proof.**
  A cleanup ticket called `dsimp only []` a no-op, but deleting it made a later `rw` fail
  "did not find an occurrence of the pattern". `dsimp only` with an empty list still performs
  beta/iota/zeta reduction — here it unfolded the `Option`/`Sigma` wrapper so the goal was
  stated in the `(n - t.remaining) + t.remaining` / `concat s₀ t.bytes` form the next step
  matched. Before "cleaning up" any `dsimp`/`simp only []`, delete it and recompile; if a
  later step stops matching, it was load-bearing — then replace it with an explicit
  `dsimp only` plus a comment saying why, rather than restoring an opaque `[]`.

- 2026-10-26 — **Turn an axiom-discipline invariant into a build-enforced `#guard_msgs` gate;
  it is cheap, and it is the only thing that stops a silent `Classical.choice` regression.**
  `#guard_msgs in #print axioms foo`, preceded by a `/-- info: 'Foo.foo' depends on axioms:
[propext, Quot.sound] -/` comment, pins the _exact_ diagnostic text: any axiom that appears
  or disappears changes the message and fails compilation. Two layout rules matter:
  (1) the `info:` doc comment must be **immediately** before `#guard_msgs in` — putting an
  ordinary `/-- … -/` docstring in between gives "unexpected token '/--'";
  (2) a `lean_lib` holding only these needs `roots := #[`GateName]`**and**`@[default_target]`on it, or plain`lake build` will not compile it (a non-default lib is
  only built when named). Generate the file from a script over the law list so it stays
  complete; verify BOTH failure directions (wrong expected text, and a law whose axioms
  change) before trusting it.

- 2026-10-25 — **A _dependent_ `cases`/`match` on a list whose **equation** (not a bound) sits in the context is itself a `Classical.choice` leak — restate the hypothesis by _number_ (`≤`/`<`) before matching.** Proving `exists cs, unapply bs = some cs` with the hypothesis `bs.length = 1 ∨ bs.length = 2` in scope and `match bs with | [v0] => … | [] => simp at h`, the proof term goes through `Eq.ndrec`/`noConfusion` (the `match`'s motive mentions `bs`), and `#print axioms` reports `Classical.choice` **even though every lemma you cite is `[propext]`-clean and the same proof with no hypothesis at all is clean**. Swapping the disjunctive equation for numeric bounds — `(hlen : 1 ≤ bs.length) (hlen2 : bs.length ≤ 2)`, then `match bs, hlen, hlen2 with` — makes the elimination non-dependent and the law `[propext, Quot.sound]`-only again. Diagnostic shape to remember: `#print axioms` says `Classical.choice`; bisect the _skeleton_ (drop the body to `⟨_, rfl⟩`) and it still leaks ⇒ the leak is in the `match`/`cases`, not the arithmetic. Corollary: the same trap hits `Partial`-style length hypotheses `ds.length = k`, so **derive** the index from the term (`count ds.length …`, not `count k …` plus `ds.length = k`) rather than threading an abstract `k`. The general rule unifying all the `Classical.choice` entries in this file: a hypothesis whose _type mentions_ the variable you are about to eliminate makes that elimination dependent, and dependent elimination reaches `Decidable`/`noConfusion` machinery that is not axiom-free.
- 2026-10-25 — **"Unique canonical inverse"-style requirements are usually _two already-proved laws and nothing else_ — state the iff and assemble, do not re-derive.** A spec sentence like "decode succeeds exactly on the encoder's image" reads like new work, but if you already have `decode s = some v → encode v = some ⟨n,s⟩` (converse) and `encode v = some ⟨n,s⟩ → decode s = some v` (roundtrip), then `decode s = some v ↔ ∃ w, encode w = some ⟨n,s⟩ ∧ v = w` is `⟨v, conv …, rfl⟩` one way and `rw [hv]; exact roundtrip w he` the other. Two traps: (a) `rintro ⟨w, he, rfl⟩` **fails** — substituting the _value_ equation with `rfl` in the pattern does not rewrite the existential body's bound occurrences; use `rintro ⟨w, he, hv⟩; rw [hv]; exact roundtrip w he`; (b) `subst hv` on `hv : v = w` **eliminates `w`**, so a later `roundtrip w he` errors with "unknown identifier `w`" — `rw` rewrites the goal without clearing the binder. When a queue says "mostly assembly", check for these two first; they cost far less than a re-derivation.
- 2026-10-25 — **A "converse" law can be _true and proved_ while the _injectivity_ (or any sibling) law you ship is silently weaker than the spec — audit each statement against the spec sentence, not against "it compiled".** Concretely: a spec says "`encode v = encode v'` ⇒ `v = v'`" (equality of the two `Option` results), and the theorem is proved as "`encode v = some ⟨n,s⟩` ⇒ `encode v' = some ⟨n,s⟩` ⇒ `v = v'`" (two success hypotheses). That is _strictly different_: it cannot be applied to the `none = none` branch, and the bridge between the two forms is `encode` is **total** — which, if never proved, makes the shipped law quietly conditional on an unstated fact (and a docstring that then says "partial bijection" is overstating). Two honest fixes: (a) prove `encode v ≠ none` and restate as the spec's `Option`-equality form, splitting the `some/some` case to the existing proof and refuting `none`/mixed by totality; or (b) amend the spec Scenario to say "both `= some ⟨n,s⟩`" **and** state the totality lemma beside it. Rule: for every law, put the spec sentence and the Lean statement side by side and check they are the _same_ Prop, not merely both true. A green `#print axioms` and a green build say nothing about this.
- 2026-10-25 — **A "vector check" that unpacks an existing ∃-decomposition theorem and repacks a _subset_ of its conjuncts is a tautology — it verifies nothing about the bytes.** `obtain ⟨blocks, m₁, m₂, blk, tail, ha, hb, hc, _, _⟩ := encode_canonical … he; exact ⟨blocks, m₁, m₂, blk, tail, ha, hb, hc⟩` in an `example` drops conjuncts 4–5 (alphabet-only bytes, exact pad arity) — the only content — so a deliberately broken encoder (wrong case, wrong pad count) would still satisfy it. A real vector must assert the _concrete output_: `example : encode foobar = some ⟨8, <literal Bytes 8 for "Zm9vYmFy">⟩ := rfl` (or `decide` / a `List.ofFn` equality), naming the expected byte string. **Acceptance test for any "value check": corrupt the encoder and confirm the check fails.** If it still passes, it is a restatement, not a test. Also: the concrete strings in a bench must be produced _by the whole-input encoder_, not by a lower-level block function (`blockUnapply`/`blockApply`) — testing the block function says nothing about the composition.
- 2026-10-25 — **`simp at h` on a hypothesis `h : (a :: t).length = k` (or any list-length contradiction) can pull in `Classical.choice`** (it reaches `List.length_eq_zero`/`Nat`-`Decidable` instances in the full context) — same family as the `omega`/`decide` leaks. In a `Classical.choice`-gated law, replace `simp at h` with an explicit `simp only [List.length_cons] at h; omega` (or `simp only [List.length_nil] at h; omega` for the `[]` case), where `omega` stays constructive on the resulting `Nat` arithmetic. Diagnose exactly as usual: `#print axioms <your theorem>` is the only authoritative gate; each cited lemma being clean is necessary but not sufficient, because the leak lands in a generated `_proof_*`.
- 2026-10-25 — **Normalise a `Bytes (n - (Suffix.empty n).remaining)`-typed witness to `Bytes n` with `simp only [Suffix.empty, Nat.sub_zero] at st hrelt`, then `subst hst_eq` — and pick the `cast` direction up front to avoid per-index `cast_bytes_val'` churn.** When a `decodeRepeat_spec`-recovered witness lands as `st : Bytes (n - 0)` (because `(Suffix.empty n).remaining` is `0` only by `rfl`/delta), the type index is _syntactically_ `n - 0` and defeats `cast (congrArg Bytes hst_ty) st` pattern-matching. `simp only [Suffix.empty, Nat.sub_zero] at st hrelt` rewrites the _types_ of the local hypotheses so `st : Bytes n`, and a later `have hst_eq : st = t.bytes` (proved by reading through `Suffix.prepend_empty`) can be `subst`-ed so the whole downstream goal loses its `- 0` casts. Note `rw [hE, Nat.sub_zero] at hrelt` **fails** ("motive is not type correct") on the `relRepeat`/`decodeFull` hypothesis whose _length argument_ is dependent — use `simp only … at …` (which rewrites at the `Nat` level before the index becomes dependent), not `rw`.
- 2026-10-25 — **To prove `⟨n - k + k, concat x y⟩ = ⟨n, z⟩` (two `Sigma`s at _definitionally different but equal_ lengths) you cannot `apply Sigma.ext` then `apply heq_of_eq`** — `heq_of_eq` demands both sides in the _same_ type, so it fails on `n - k + k` vs `n`. Three working shapes, in order of preference: (1) `have hlen : n - k + k = n := Nat.sub_add_cancel hle` and assemble `hsig : (⟨n-k+k, concat x y⟩ : Sigma fun m => Bytes m) = ⟨n, z⟩ := Sigma.ext hlen (by have h1 : HEq (concat x y) (cast (congrArg Bytes hlen.symm) z) := heq_of_eq hbytes; exact h1.trans (cast_heq (congrArg Bytes hlen.symm) z))`, where `hbytes : concat x y = cast (congrArg Bytes hlen.symm) z` is the pointwise byte equality — `cast_heq` supplies the `HEq` across the differing lengths; (2) better, `subst` the length away first (`st`/`t.bytes` at the same index) so no `Sigma.ext` on unequal lengths arises; (3) `cases hlen` **fails** with "dependent elimination" when `n` is also the `Bytes` index — do not reach for it. A residual `cast ⋯ t.bytes` in the goal after rewriting means the two `fst`s are not syntactically equal, and you are fighting the wrong shape.
- 2026-10-25 — **Mirroring a proof to a second base with different block/tail widths: the _statements_ differ (3-byte vs 5-byte blocks, 1–2 vs 1–4 byte tails) but the _proof script_ is identical — so name the mirrors identically and hoist the generic part.** Three lemmas (`relBlock_all_size{k}`, `split_blocks_tail`, `encodeTail_of_rel`) were re-derived per base only because the block size and tail shape differ; the inductions are character-for-character the same. Naming them with the same suffix (`…_all_size3`) while one proves length 3 and the other proves length 5 is a **lie that survives review** — name by the fact (`…_len3`/`…_len5`), and parameterise the generic part (`∀ elem len, (∀ x s, Rel elem x s → x.length = len) → …`) into a shared `Common` module rather than cutting a per-base copy, per the "reuse the shared generic lemmas instead of re-deriving them" convention.
- 2026-10-25 — **A design doc's "we will _not_ use shape X" header is not evidence the code avoids X — grep the code.** A design decided to replace a `List.head? ((decodeRepeat …).filterMap …)` decoder with a direct `Run`▸tail composition ("this _removes_ the flattened `head?`/`filterMap` step"), but the shipped decoder was byte-for-byte the original `List.head? (… .filterMap …)`, guarded by a `≤ 1` bound instead. The proof was fine; the _documentation_ was false, and a reviewer trusting the decision header believed a restructuring that never happened. When a design commits to a shape change, either do the change or amend the decision to say "kept shape X, guarded" — and in review, diff the design's claim against an actual `grep` of the definition it names.

- 2026-10-25 — **Before proving a converse/uniqueness law, `#eval` a _counterexample_ — a whole-input decoder that backtracks over a multi-block terminal tail silently breaks "decode → encode reproduces input".** A decoder `head? ((decodeRepeat block).filterMap (decodeFull tailElem))` accepts an input with data _after_ a terminal `=` that is _itself_ a valid padded block (e.g. `Zg==Zg==` → `[[f],[f]]` for a base64-ish tail), because `decodeFull tailElem` is `decodeRepeat`-based and admits `n` tail blocks. Such an input decodes to a canonical value `v` whose re-encode differs from the input, so the converse `decode s = some v → encode v = some ⟨n,s⟩` is **false as stated** — not a hard proof, an _unsatisfiable_ one. Find the smallest `#eval` counterexample figure first (took two lines), rather than grinding a `[propext, Quot.sound]` proof that cannot close. The fix is a **guard, not a re-shape**: add `if tail.length ≤ 1 then some (…) else none` to the `filterMap` step (single-block tail bound), which keeps `tail : List (List α)` and hence the whole `relRepeat (Rel tailElem)`/boundary-pin proof library intact — the only surfaced delta is one extra `tails.length ≤ 1` conjunct in the decomposition (`decodeFull_*_some`) and the roundtrip/rejection `rcases`. The "cleaner" alternative (decode `tailElem` _once_ via single-element `decode`, requiring `t₂.remaining = 0`) changes the tail value to a single `List α` and forces re-deriving the roundtrip singleton + rejection family over a new boundary-pin input — semantically identical, dramatically more churn.

- 2026-10-25 — **`bidir : Rel d x s ↔ (x, Suffix.empty n) ∈ decode d s` (in `Codec/Sound.lean`) is the one-line bridge from a `Rel` fact to a decode-membership fact, and it is what makes `encode_of_decode` (`Rel`→`encode`) fire in a converse proof.** To re-encode a single decoded tail block `x` from `Rel d x s`, write `(bidir d x m s).2 hrel : (x, Suffix.empty m) ∈ decode d s`, then `encode_of_decode d (hd : Functional d) x that-membership : encode d x = some ⟨m, s⟩`. (The alternative is `(decode_spec d x s (Suffix.empty m)).2 ⟨cast (Nat.sub_zero m).symm s, (prepend_empty_eq s).symm, (Rel_cast d x (Nat.sub_zero m).symm s).2 hrel⟩` — `bidir` is exactly that, pre-packaged.) Note `Functional d` is definitionally `relFunctional (Rel d)`, so a `Functional` witness feeds `encodeRepeat_of_rel`'s `relFunctional (Rel p)` argument directly.

- 2026-10-25 — **`omega`'s _disjunction_ search (`k < n ⊢ k = 0 ∨ k = 1 ∨ … ∨ k = n-1`) leaks `Classical.choice` via `Nat.lt_or_gt_of_ne` (trichotomy); the clean fix is nested `cases k` + `omega` **only** for the `False` contradiction.** The rejection/`hall`-style byte case commonly wants `k = 0 ∨ k = 1 ∨ … ∨ k = n-1` from `hk : k < n` for a free `k`. `omega` discharges it, but `#print axioms <.theorem>` reports `Classical.choice` because the generated proof turns `Nat.lt_or_gt_of_ne` / `Nat.lt_trichotomy` (both `Classical.choice`-dependent) — even though `#print axioms` on an _isolated_ `theorem t (k) (hk : k < 4) : k = 0 ∨ … := by omega` is clean (context-dependent). The `#print axioms` gate is the _only_ authoritative check; each named dependency being clean is necessary but **not** sufficient (the `_proof_*` subproofs like `YourThm._proof_1_4` are where the leak lands, visible via `#print axioms YourThm._proof_1_4`). Fix: `cases k with | zero => simp | succ k1 => cases k1 …` down to `n-1`, then the final `| succ k₍ₙ₋₁₎ => exfalso; omega` (a `False` goal, where `omega` stays constructive). Spell this once per width as a reusable `nat_lt_four` / `nat_lt_eight` in `Common` rather than inlining.

- 2026-10-25 — **The clean `List.ofFn` head extraction is `List.ofFn_succ` + `List.head!`, _not_ `List.getElem_ofFn` on a `Fin` index.** To prove `s ⟨0, ·⟩ = c0` from `htail : List.ofFn s = [c0, c1, c2, c3]`: `have hsucc : List.ofFn s = s ⟨0, by decide⟩ :: List.ofFn (fun i : Fin 3 => s i.succ) := List.ofFn_succ; have hcons := … (rw [← hsucc, htail])…; have hhead := congrArg (fun l : List UInt8 => l.head!) hcons; simp [List.head!] at hhead` — `rfl` then closes `s ⟨0,·⟩ = c0`. The `List.getElem_ofFn` route fails because `(List.ofFn s).length` is **not** definitionally `n` (`List.length_ofFn` is a theorem, not `rfl`), so `by decide` on `0 < (List.ofFn s).length` reports "Expected type must not contain free variables"; `List.ofFn_succ` exposes the head as a raw `cons` and `head!` projects it with no `Fin`-length proof.

- 2026-10-25 — **`Codec.ofFn_concat : List.ofFn (concat s₀ s₁) = List.ofFn s₀ ++ List.ofFn s₁` (in `Codec/Encode.lean`) is the whole-list transport that makes a canonical-encoding _decomposition_ theorem `Fin`-index-free.** To state/prove a whole-input `encode bs = some ⟨n,s⟩` canonical form (alphabet-only blocks + a single padded tail), return `List.ofFn s = List.ofFn blkBytes ++ List.ofFn tailBytes` (plus `List.ofFn tailBytes = [] ∨ [c₀,c₁,=,=] ∨ …`) instead of `s = concat blkBytes tailBytes`. The `s = concat …` form forces Sigma-boxing/`cases hpair` on `(⟨m₁+m₂, concat⟩ : Sigma fun k => Bytes k) = ⟨n,s⟩` (which substitutes `n`/`s` only after a dependent-`Eq` chase); the `List.ofFn s = …` form closes by `cases hpair; exact Codec.ofFn_concat blkBytes tailBytes`, and every per-byte fact (`b64Valid`/pad/terminal) is then a `List.mem`/`List.getElem_ofFn` step, never a `Fin ⟨i, ·⟩`.

- 2026-10-25 — **A `match … with | some [b] => some [b] | some [b0,b1] => … | _ => none` whose target is a _specific literal_ (`= some [b]`, one element) does not reduce under `simp [hb]` when the scrutinee `some (x :: y :: rest)` is only partially length-determined (2+ elements is ambiguous between the `[b0,b1]` and `_` branches); collapse the whole structure with a one-line helper `tailBlock_block : tailApply a = some ys → blockApply a = some ys` (proved by `cases hb : blockApply a; cases bl; …; simpa [tailApply, hb] using h` — `simp` _reduces_ the match, and `some [x] = some ys` closes `[x] = ys` because `ys` is a free variable), then `have hblk : blockApply a = some [b] := tailBlock_block ha`.** Do **not** `unfold tailApply at ha` first (that commits the matched form before `hb` rewrites it); the helper runs `cases hb : blockApply a` + full `cases bl` down to the `_ => none` (5+ elements) branch so every intermediate length is `some`/`none`-determined. The pre-unfold route gets stuck on `(match some (x::y::rest) …) = some [b]` exactly because `rest`'s length is unknown (3 vs 4 vs 5 elements).

- 2026-10-24 — **The empty-blocks result of `decodeRepeat` is _exactly_ `Suffix.id n s`; prove it once as `decodeRepeat_nil_mem_eq_id : ([], t) ∈ decodeRepeat p h n s → t = Suffix.id n s` and it erases an entire class of `Bytes`/`Fin`/`cast` byte-extraction.** Proof: `rw [decodeRepeat_eq] at hmem; rw [List.mem_cons] at hmem`; the `.inl` branch is `congrArg (fun pr => pr.2) hmem` (the pair's suffix field); the `.inr` branch is impossible because every `flatMap` result is `(x :: xs, t.trans r)` (a non-empty block list), so `rw [List.mem_flatMap]`→`rw [List.mem_map]`→`rcases` the `(x::xs,·)=([] ,·)` equality. Once you have `t = Suffix.id n s₀`, `subst t` makes `t.bytes = s₀` and `t.remaining = n` **definitional** — the `splice`/`prepend`/`bdrop`/`cast_fin_symm` chase that a whole-input roundtrip/rejection needs _vanishes_, and the remaining byte read is just `bdrop 4 s₀ = …` + `splice_prefix_read` + `rfl`. Prefer this over the pointwise `prepend_zero`/`cast (congrArg Bytes hrem) t.bytes = s` route (that one is `[propext, Quot.sound]`-provable too, but only after a `cast_fin_symm_val`-keyed `simp` that takes many iterations — `decodeRepeat_nil_mem_eq_id` sidesteps it entirely).

- 2026-10-24 — **`decide`/`omega` on a goal whose `Decidable` must synthesize `∀ i : Fin n, P i` leaks `Classical.choice`; close the _free-`Fin`_ byte case with `rcases i with ⟨k, hk⟩; rcases (k = 0 ∨ … ∨ k = n-1) with rfl | … <;> rfl`, never `decide`.** When a rejection/roundtrip proof needs "byte `k` of this literal list is `b`" for `i : Fin n` with `i` a free variable, the naive `rw [hi]; decide` (with `hi : i = ⟨0⟩` via `Fin.eq_of_val_eq`) forces instance search for `Decidable (∀ i : Fin n, s₀ ⟨i…⟩.toNat = b)`, whose candidate list starts with `Classical.propDecidable` — the synthesized proof carries `Classical.choice` even though _every named lemma_ you cited is `[propext, Quot.sound]`-clean (`#print axioms` on each will agree, while `#print axioms` on your theorem reports `Classical.choice`, and `Expr.getUsedConstants` shows no culprit — the leak is in an auto-generated `_proof_*`/`Decidable` instance, invisible to theme-pretty-printer). The clean spelling is `rcases i with ⟨k, hk⟩; have hk4 : k = 0 ∨ k = 1 ∨ … ∨ k = n-1 := by omega; rcases hk4 with rfl | rfl | … <;> rfl` — `rfl` reduces the `List.getElem` of the literal list at the now-concrete index with **no** `Decidable` search, and `#print axioms` is then `[propext, Quot.sound]`. (The proof of "`[65,65,65,65][i] = 65` for `i : Fin 4`" thus closes by `rfl`, not `decide` — and `simp [theByteList]` first `drop`s the literal prefix down to `[65,65,65,65][…]`.)

- 2026-10-24 — **`omega` on a `Nat`-subtraction trichotomy (`n - t.remaining = 0 → t.remaining = n`) leaks `Classical.choice`; use `Nat.sub_eq_zero_iff_le.mp` + `Nat.le_antisymm` instead.** To pin `t.remaining = n` from `n - t.remaining = 0` given `t.remaining ≤ n`: `have hle : n ≤ t.remaining := Nat.sub_eq_zero_iff_le.mp hz; exact Nat.le_antisymm htle hle` (`Nat.sub_eq_zero_iff_le` is `[propext]`, `Nat.le_antisymm` is axiom-free). Similarly a `4 ≤ n - t.remaining` over a `hm : m ≤ n - t.remaining` + `hm₄ : m = 4` is `simpa [hm₄] using hm`, not `by omega`; and a `4 ≤ 2` contradiction is `Nat.le_trans h4 h2` → `False.elim ((by decide : ¬ (4:Nat) ≤ 2) h42)` or `cases h42`. The rule generalizes the skill's earlier "`Nat.mul_lt_mul_left` is `Classical.choice`-dependent" note to **sub-trichotomy**: `omega`/`decide` on `Nat` `n-m` triggers `ofNat_sub_dichotomy`→`Classical.propDecidable` in the full dependent context even though an isolated `#print axioms` of the _same_ `omega`/`decide` goal reports clean. The `#print axioms <your theorem>` is the only authoritative gate check; `#print axioms <each lemma>` being clean is necessary but **not** sufficient.

- 2026-10-24 — **Do not claim a whole-input decoder "rejects by unrepresentable value type" unless its value type _is_ that restricted inductive; if it returns `List UInt8`, rejection is an _inequation_, not absence-of-inhabitant.** The trap: define a terminal-tail inductive `T` (blocks + tail, tail has no continuation), _also_ define `ofList : List UInt8 → T` **total** and prove `bytesOf (ofList bs) = bs` / `ofList (bytesOf v) = v` — that is a _total bijection_ `List UInt8 ≅ T`, which proves `T` enforces **nothing** (it is a canonical spine/relabeling, not an illegal-state eliminator). Then a `decodeFull : Bytes n → Option (List UInt8)` built as `List.head? ((decodeRepeat …).filterMap (decodeFullTail …))` cannot be "structural (no inhabiting value)" — the malformed input (`tail` bytes then more data) _is_ a `List UInt8` value, so `= none` must be proved as a **pad-dichotomy inequation**: the full-block run cannot consume a block containing the sentinel (block element has no sentinel), and the leftover sentinel-free bytes cannot decode as a tail (tail element _must_ contain the sentinel), hence the `filterMap` is empty and `head?` is `none`. **Review check:** `grep` the plan+code for "unrepresentable"/"structural"/"no bijective flattening"/"no inhabitant" and confirm the value type is actually the restricted inductive — if the decoder returns `List`/`Bytes` and there is a proved `ofList∘bytesOf = id`, every such claim is false and must be rewritten to the inequation framing (a bijection `≅` is the _opposite_ of an unrepresentability guarantee).

- 2026-10-24 — **Unpacking an `Option (Sigma fun k => Bytes k)` encode into per-component commits: `cases hpair` on the `Sigma` equality, and `Option.some.inj` only _after_ `simpa` reduces the `some`-form.** A whole-input encoder `encode bs = let p := split bs; encode' p.1 p.2` unpacked over a `he : encode bs = some ⟨n,s⟩` needs the component `encodeRepeat step blocks = some ⟨m₁,blkBytes⟩` / `encodeTail tail = some ⟨m₂,tailBytes⟩` and `⟨m₁+m₂, concat blkBytes tailBytes⟩ = ⟨n,s⟩`. Build the Sigma equality with `have he' : some (⟨m₁+m₂, concat blkBytes tailBytes⟩ : Sigma fun k => Bytes k) = some ⟨n,s⟩ := by unfold encode encode' at he; simpa [blocks, tail, heb, het] using he; exact Option.some.inj he'` (the explicit `Sigma fun k => Bytes k` annotation is required or the `⟨…, …⟩` fails "expected type could not be determined"). Then `cases hpair` globally substitutes `n := m₁+m₂` and `s := concat blkBytes tailBytes` _throughout the remaining hypotheses and goal_ — no separate `hs`/`hn` `have`s, no `HEq` threading. (Conversely `simp … at he` on the `some`-form collapses it to `m₁+m₂ = n ∧ concat … ≍ s`, which `exact he` will _not_ retype to the Sigma equality — `And` ≠ `Eq Sigma`.)
- 2026-10-24 — **`head?`-of-`filterMap` whole-input decoder: membership via `List.mem_filterMap` (`b ∈ filterMap f l ↔ ∃ a, a ∈ l ∧ f a = some b`), singleton via `head?_eq_some_of_mem_eq b L hmem hall`.** For a decoder `head? ((decodeRepeat …).filterMap fun ⟨blocks,t⟩ => match decodeFull … t.remaining t.bytes with | some tail => some (blocks.flatten ++ tail.flatten) | none => none)`, the roundtrip `= some bs` is `apply head?_eq_some_of_mem_eq bs; exact (membership); intro x hx; …`. The membership half witnesses `(blocks, Suffix.drop m₁ (concat blkBytes tailBytes))` with the block run lifted by `decodeRepeat_prefix_concat`, the tail decode by `decodeFull_…_suffix_nil/_cons`, and the flatten identity `blocks.flatten ++ tail = bs`. The singleton half recovers `blocks'`/`tail'` from `List.mem_filterMap` at `hx`, pins `blocks' = blocks` (boundary pin + run-unambiguity) and `tail'.flatten = tail` (tail pin), then `hx`’s `= blocks'.flatten ++ tail'.flatten` closes.
- 2026-10-24 — **A `decodeFull_…_of_encode tail het` result `= (match tail with | [] => some [] | _ => some [tail])` generalizes the `match` over the in-scope hypotheses that mention `tail` (its proof did `cases tail`), so `rw [htailc : tail = b::rest] at <that>` produces a recursive `match tail, het, hflat, … with` that `simpa [htailc]` looped on. Fix: re-derive the result with _concrete_ `tail`** — `cases htailc : tail with | cons b rest => have het' : encodeTail (b::rest) = some … := by simpa [htailc] using het; have h : decodeFull … = some [b::rest] := by simpa using (decodeFull_…_of_encode (b::rest) het')` — and it reduces cleanly (the `_` branch matches a raw `cons`). Pin the decoded value by `(Option.some.inj (h.symm.trans hdec)).symm`, where `hdec : decodeFull … tailBytes = some tail'`.
- 2026-10-24 — **The `cast (congrArg Bytes hbnd) t'.bytes = tailBytes` bridge for a `decodeFull_cast` tail decodes is cleaner _pointwise_ than via `simpa [hbnd]` on `prepend_concat_suffix`.** `prepend_concat_suffix a b t' s₀ hrem h` concludes `cast (congrArg Bytes (Nat.sub_sub_self t'.hle).symm) t'.bytes = cast (congrArg Bytes (by omega : m₂ = (m₁+m₂) - ((m₁+m₂) - t'.remaining))) b`; `simpa [hrem]` on it does _not_ normalize the RHS cast to `tailBytes` (the `Nat.sub_sub_self`/`add_sub_cancel_left` shape doesn't reduce). Instead prove `cast (congrArg Bytes hbnd) t'.bytes = tailBytes` by `Bytes.ext; intro i; rw [cast_bytes_val' (e := hbnd)]; rw [prepend_suffix_read a b t' s₀ h ⟨i.val, Nat.lt_of_lt_of_eq i.isLt hbnd.symm⟩]; have hk : m₁ + m₂ - t'.remaining = m₁ := by rw [hbnd]; omega; simpa [hk, Nat.add_comm, Nat.add_left_comm] using (concat_tail_read a b i)` — `prepend_suffix_read`/`concat_tail_read` are the private pointwise halves, and `Nat.lt_of_lt_of_eq i.isLt hbnd.symm` is the clean `i < m₂ → i < t'.remaining` transport (the inline `by rw [← hbnd]; exact i.isLt` does not close a `Fin`-`.val` coercion goal).
- 2026-10-24 — **`decodeFull_cast p h (e : n = m) (s : Bytes n)` rewrites `decodeFull p h m (cast (congrArg Bytes e) s) = decodeFull p h n s`; to lift a `decodeFull … t'.remaining t'.bytes` to length `m₂` use `rw [← decodeFull_cast … hbnd t'.bytes] at hdec`** (the `←` direction, since the hypothesis has `t'.remaining`/`t'.bytes` and you want `m₂`/`cast`). The `Nat.sub_sub_self`/`add_sub_cancel_left`-fingerprint `Nat.sub n 0 = n` (`rfl`) and `(Suffix.empty n).remaining = 0` (`rfl`) make a `relRepeat`/`decodeRepeat_spec`-recovered `s₀t : Bytes (t'.remaining - 0)` _already_ `Bytes t'.remaining`; bridge it to `t'.bytes` with `prepend empty`, not a cast chase.

- 2026-10-24 — **Stdlib `Nat` `<`-cancellation lemmas are `Classical.choice`-dependent; the `≤`/`=` forms
  are clean.** `Nat.lt_of_mul_lt_mul_left`, `Nat.mul_lt_mul_left`, `Nat.lt_of_mul_lt_mul_right` all
  `#print axioms` to `[propext, Classical.choice, Quot.sound]` (they route through `Decidable`-`by_cases`),
  while `Nat.mul_le_mul_left`, `Nat.le_of_not_gt`, `Nat.lt_of_le_of_ne`, `Nat.succ_le_of_lt`,
  `Nat.add_left_cancel`, `Nat.sub_add_cancel`, `Nat.sub_sub_self` are `[propext]`-or-less. **For an
  axiom-gated law, `#print axioms <lemma>` _before_ using any stdlib arithmetic lemma** — one `Classical.choice`
  in a single `Nat` step silently pushes the whole theorem off the `[propext, Quot.sound]` gate, and only
  `#print axioms <your theorem>` (not a green build) surfaces it. Replace `4*a < 4*b → a < b` with a tiny
  `private theorem … (h : 4*a < 4*b) : a < b := by omega` — `omega` is constructive.
- 2026-10-24 — **`omega` does not see field projections (`t'.hle`, `i.isLt`): surface them as explicit `have`s.**
  `omega` only uses _local binder_ hypotheses, so `t' : Suffix n` contributes no `t'.remaining ≤ n` and `i : Fin k`
  contributes no `i.val < k`. Before `omega`, write `have hle : t'.remaining ≤ n := t'.hle` and
  `have hi : i.val < k := i.isLt`. The trap is worse in a **theorem statement's** `(by omega : i.val + L < m)`
  index annotation: that `omega` elaborates in the _statement_ context (no `have`s in scope), so either inline
  the facts (`(by have hi := i.isLt; have hle := t'.hle; omega)`) or drop the annotation and pass the index proof
  as a named `(hidx : …)` parameter — the caller then closes the proof-term mismatch by proof irrelevance.
- 2026-10-24 — **`omega`'s Int-model emits _spurious_ "counterexample may satisfy the constraints" on Nat
  subtraction inside a large context** (e.g. `m₁ + m₂ - t'.remaining` with `t'.remaining = 4·|rest|` and
  `m₂ < t'.remaining`; the model lets `a - b` go negative, so its `a - b ≤ -1` constraint violates the real
  `t'.hle`). Fix: don't hand `omega` the whole context with Nat-sub terms — first `rw` the equality hypotheses
  _into the goal_ (`rw [← hL, ← hm₁len]` is safe on a plain Nat inequality, since only the goal's occurrences are
  rewritten), which leaves a clean `4*a < 4*b` / `4*a + 4 ≤ 4*b` fact, then finish with a minimal `omega` or a
  constructive `Nat.mul_le_mul_left` step. (`rw [hL]` fails differently when `hL`'s LHS is itself a _type index_ —
  see the dependent-index entry below.)
- 2026-10-24 — **`rw [hm₂ : m₂ = 0]` fails with a dependent-motive error when `m₂` occurs in the _type_ of a
  projection the goal mentions** — `t'.remaining` for `t' : Suffix (m₁ + m₂)`, even when the goal
  `(m₁ + m₂ - t'.remaining) + 4 ≤ m₁` is a plain Nat inequality. `rw` abstracts `m₂` everywhere in the goal,
  including inside `t'`'s type, and refuses. Use `simpa [hm₂] using t'.hle` (simp rewrites at the `Nat` level
  without abstracting the projection's type) or assemble the arithmetic explicitly (`Nat.sub_add_cancel t'.hle`,
  then `rw [h] at hsub`, then `Nat.add_left_cancel`) instead of `rw`-ing the equality.

- 2026-10-24 — **Rewriting a _dependent_ index (e.g. `bdrop (m₁+m₂-t'.remaining)`'s index) with `rw`
  [hrem]`/`rw [hk]`fails with "motive is not type correct"** — the`bdrop`/`concat`result *type*`Bytes (n - index)`depends on`index`, and `r`w` cannot abstract over the occurrence inside a projected
  type or an anonymous `by omega`/`Suffix.remaining` proof. **Do not `rw` the index; instead prove the
  whole fact pointwise over `Bytes.ext` and feed the index-equality as a _simp lemma_:** `dsimp [bdrop,
concat]` produces `(if i.val + (m₁+m₂-t'.remaining) < m₁ then … else b ⟨i.val + (m₁+m₂-t'.remaining) - m₁,
…⟩)`, and `have hk : m₁+m₂-t'.remaining = m₁ := by omega; simp [hk, hnot]` (with `hnot : ¬ i.val + m₁ < m₁`)
  closes it _defeq-clean_ — `simp` rewrites `m₁+m₂-t'.remaining → m₁` at the `Nat` level _before_ the `Fin`
  index becomes dependent, so no cast survives. (The earlier, rejected spellings were: a `change`-with-
  inline-`splice_add` that leaves an unprovable `splice_add` obligation; and `simp [hnot]` _without_ `hk`,
  which reduces the `if` to `b ⟨i.val + (m₁+m₂-t'.remaining) - m₁, …⟩ = b ⟨i.val, …⟩` and then `omega` cannot
  close that `Fin`-`.val` gap because it does not auto-substitute `hrem`.) The final `Fin`-index alignment
  (`b ⟨i.val + k - m₁, _⟩ = b ⟨i.val, _⟩`) closes by `congr 1; exact Fin.eq_of_val_eq (by rw [hrem]; omega)`.
- 2026-10-24 — **`List.mem_iff_getElem : a ∈ l ↔ ∃ i h, l[i] = a` is the clean membership→`Fin`-index
  bridge (no `Classical.choice`).** To lift "`c ∈ a`" to "`c` is the `i`-th byte of the content-extraction
  `a = List.ofFn s`" (the pad-_presence_ direction of an alphabet/pad-dichotomy proof, dual to the
  `List.ext_getElem?` content-extraction direction): `rcases List.mem_iff_getElem.mp hc with ⟨i, hi, hi'⟩` gives
  `hi : i < (List.ofFn s).length` and `hi' : (List.ofFn s)[i] = c`; then `c = s ⟨i, Nat.lt_of_lt_of_eq hi
List.length_ofFn⟩` closes by `hi'.symm.trans (List.getElem_ofFn hi)` (or the clean hand-proved
  `(List.ofFn f)[i] = f ⟨i, Nat.lt_of_lt_of_eq h List.length_ofFn⟩` variant — see the `ofFn`-bridge `Classical.choice`
  entry). `Nat.lt_of_lt_of_eq hi List.length_ofFn` is the canonical `i < |List.ofFn s|` → `i < n` transport. This
  is how you show a `Rel (iso i (count k (satisfy p))) x s` string _contains_ a sentinel byte (e.g. a `=` pad) from
  the iso's `apply` forcing a sentinel at a terminal position — the pad-dichotomy's tail side.
- 2026-10-24 — **Pinning a `relRepeat` run's _byte length_ is a clean, generic induction:
  `relRepeat (Rel elem) xs n s → n = width · xs.length` for an element that consumes a fixed `width` bytes per step.**
  Prove it by `induction xs generalizing n`, then `rw [relRepeat_cons]`; the hypothesis gives `s₁ : Bytes m` with
  `Rel elem x s₁`, so the element's length fact (`Rel_elem_len : Rel elem x s → m = width`) does `subst m`, the IH gives
  `n - width = width · rest.length`, and the goal `n = width · (x::rest).length` closes by
  `rw [List.length_cons, Nat.mul_add, Nat.mul_one]; omega` (omega cannot distribute `width · (|rest|+1)` on its own — feed
  it `Nat.mul_add`/`Nat.mul_one` first). This is the _length half_ of the block/tail split-uniqueness a padded-base
  whole-input roundtrip needs (the width is 4 for base64 blocks/tails, 8 for base32).
- 2026-10-24 — **Pinning a `Rel (iso i d) x s` value's _size_ unfolds the Iso's `apply` through its internal match:
  `Rel (iso blockIso (count k (satisfy p))) x s → x.length = 1 ∨ x.length = 2`** for a block `Iso` whose `apply` is
  `match unapply-block with | some [b0] => some [b0] | some [b0,b1] => some [b0,b1] | _ => none` (a "tail" iso restricted to
  short outputs). Proof: `rw [Rel_iso]` → `⟨a, ha, _⟩`, `change blockApply a = some x at ha`, `unfold blockApply at ha`,
  `cases hb : <inner block apply> a with`, then `cases` the result list down; in the 1-/2-element branches `simp [hb] at
ha; cases ha; right/left; rfl` (the `cases ha` turns `some x = some [b0,b1]` into `x = [b0,b1]` so `.length` reduces).
  This is the _content half_ of the split-uniqueness argument: the tail value's arity is 1..k-1, the block value's is k.
- 2026-10-24 — **The padded-base whole-input-roundtrip lemma family is _width-parameterized_: base64 (4 chars)
  ↔ 3-byte block / 2 pad-embedding tail shapes, base32 (8 chars) ↔ 5-byte block / 4 tail shapes — mirror the whole
  family by _scaling three numeric spine facts_, nothing else.** To replicate `decodeFullX (encodeX bs) = some bs` for
  a second padded base, keep every lemma's proof structure identical to the first base and change only: (a) the
  `relXBlock_len`/`relXTail_len` width from `4 * xs.length` to `8 * xs.length`; (b) the pad-dichotomy _size_ lemma
  `Rel_xBlockElem_size : … → x.length = full` (full = 3 for base64, 5 for base32) rejects **`full - 1`** pad-embedding
  shapes via that many nested `cases xs` levels (2 for base64, 4 for base32), each embedding a `61` and closed by
  `hnopad (UInt8.ofNat 61) hmem rfl`; (c) the boundary-pin's multiplication-cancellation helper `mul_lt_of_lt :
(width · a < width · b) → a < b` (`four_` = 4, `eight_` = 8, both `by omega`) and the committed-block-prefix bound
  `m₁ + m₂ - t'.remaining ≤ m₁ + (width-1)` (`+3` for base64, `+7` for base32, since the pad byte index `ip.val < width`
  gives `ip.val ≤ width-1`). The `encodeXTail_len` result `n = 0 ∨ n = width` and `decodeFull_xTail_suffix_cons`'s
  nested `cases tail` levels also scale (2 vs 4 cons-levels); `encodeXTail`/`xSplit`/`xSplit_ofBytes_ofBytes` gain the
  matching number of base cases. Everything else (the `concat`/`Suffix.drop`/`bdrop` transport, `prepend_concat_prefix_cast`/
  `_suffix`, the `head?`-filterMap membership/singleton split, `decodeFull_cast`) is width-independent and copies verbatim.

- 2026-10-24 — **Do not fabricate paper provenance for your own derived combinators; verify the source
  actually defines them before writing "paper §X" in a docstring or README.** A faithful port adds
  combinators _in the spirit of_ the source, but the paper only defines `many` (§3.4) and `chainl1` (§6.1);
  `sepBy`/`chainr1`/`optional`/`maybe`/`choice`/`count`/`manyUpTo` are the _port's own_ additions and must be
  labeled as such ("not in the paper"), not cited to a section (§6.2 is the paper's _Abstract Syntax_,
  which defines no combinators at all). `grep` the source paper for each combinator name before citing it;
  a reviewer will.

- 2026-10-23 — **`decodeFull p h n s` is insensitive to a length cast of its byte argument, and this is a
  one-line lemma (`subst e; rfl`), not a long `splice`/`concat` chase.**
  `decodeFull_cast p h : ∀ {n m} (e : n = m) (s : Bytes n), decodeFull p h m (cast (congrArg Bytes e) s) =
decodeFull p h n s`. Use it (together with the already-proved `bdrop_concat`) to reduce a tail-decode over a
  _dropped suffix_ `(Suffix.drop m (concat sb st)).bytes` back to a decode over the bare `st` — the `Suffix.drop`
  fields reduce to `m+t-m`/`bdrop m (concat sb st) = cast (congrArg Bytes (Nat.add_sub_cancel_left m t).symm) st`,
  and `decodeFull_cast … (Nat.add_sub_cancel_left m t).symm st` absorbs the cast, so a `decodeFull_b64Tail_of_encode
st` result transfers verbatim. This is the clean _cast_-level transport the padded-base whole-input roundtrip needs,
  and it replaces fighting the dependent `Bytes` reindexing by hand.

- 2026-10-23 — **`List.ext_getElem?` (the _total_ `[i]?` form) is the fix for the `List.ofFn` content-extraction
  grind: it closes `List.ofFn (splice hm s₁ s₂) = b :: List.ofFn s₂` cleanly, where `List.ext_getElem`*`(the`getElem`form) left unclosable`omega`index-bound goals.**`Rel (count k (satisfy p)) xs s → List.ofFn s = xs`*is* provable`[propext, Quot.sound]`-only without the `Functional`fallback: in the`succ`case, after`rw [hs]`and`change List.ofFn (splice hm (single a.1) s₂) = a.1 :: List.ofFn s₂`, do `apply List.ext_getElem?; intro i;
  simp only [List.getElem?_ofFn]`— this gives`(if h : i < n then some (splice … ⟨i,h⟩) else none) = (a.1 :: List.ofFn s₂)[i]?`(both sides are *total*`Option`), so `by_cases hi : i < n`with each branch`simp [hi]`**and no length hypothesis to
discharge** (the`List.ext_getElem`/`getElem_ofFn`route demanded`n = n-1+1`per element). In the`i < n`branch split
again on`i < 1`: the `i = 0`sub-branch is`splice_prefix_read … ⟨i,hi⟩`then`subst i; simp`, the `i ≠ 0`sub-branch is`splice_apply`+`unfold concat`+`rw [cast_fin_symm]`then`rw [List.getElem?_cons]`+`simp [show i ≠ 0 by omega]`— the`[i]?`cons reduction needs`i ≠ 0`(not`¬ i < 1`) because `(a::l)[i]?`matches`getElem?_cons_succ`only when`i`is
syntactically`j+1`. The outer `¬ i < n`branch closes by`simp [hi]`+`omega`(the cons length`n-1+1 ≤ i`).
- 2026-10-23 — **Unwrapping a `f bs = some ⟨n, s⟩` into per-component encodings needs `cases
(Option.some.inj h)`, not `congrArg Sigma.snd` — `Sigma.snd` is a _dependent_ projection and `congrArg` over it is
  ill-typed (yields `?m ⟨…⟩ = ?m ⟨…⟩`, expected `… ≍ …`).** When `f bs` is a `match encodeRepeat … , encodeTail …` that
  re-pairs into `some ⟨m₁+m₂, concat sb st⟩`, mimic `encodeB64`/`encodeB64'`: after `unfold`/`cases` on the two
  `encodeRepeat …`/`encodeTail …` scrutinees (using `cases heb : …` to keep the _hypotheses_ `heb`/`het` named), build
  `he' : some ⟨m₁+m₂, concat sb' st'⟩ = some ⟨n, s⟩` by `simpa [heb, het] using he` (give the Sigma an explicit type
  annotation `(… : Sigma fun k => Bytes k)` or `⟨⟩` fails to infer), then `have hge := Option.some.inj he'` and
  `cases hge` — this yields `rfl` for the length (`m₁+m₂ = n`) and a `HEq` for the bytes (`concat sb' st' ≍ s`), exactly
  the two facts you need, with no dependent-`congrArg` gymnastics. **Do not** `simp [heb, het] at he` (it rewrites the
  in-scope `heb`/`het` into `some ⟨…⟩ = some ⟨…⟩` and then the goal's `encodeRepeat … = some ⟨…⟩` conjunct no longer
  matches them).
- 2026-10-23 — **`Functional` (one value → at most one `⟨n, s⟩`) is the clean way to _pin content_, and it
  avoids `List.ofFn`/`Fin`-cast index arithmetic entirely.** `Functional d : ∀ x n₁ n₂ s₁ s₂, Rel d x s₁ → Rel d x s₂
→ ⟨n₁,s₁⟩ = ⟨n₂,s₂⟩`. So given `Rel d x s`, get `hne : encode d x ≠ none` via `encode_ne_none`, `cases he :
encode d x`, and `hrel' : Rel d x e.2` via `encode_rel`; then `functional x s e.2 h hrel'` is a **Sigma** equality
  `⟨n,s⟩ = e` and `cases` it substitutes `s := e.2` — i.e. `s` is exactly the _encode_ of `x`. This is the replacement
  for a `Rel (count k (satisfy p)) xs s → s pins xs pointwise` content-extraction lemma, which in a stdlib-only Lean
  is genuinely painful: `List.ofFn_succ` needs a `Fin (n+1)` scrutinee, and rewriting `n = (n-1)+1` into a
  `splice hm (…)` (whose `hm : 1 ≤ n` depends on `n`) raises a dependent-motive error, while `List.ext_getElem`/
  `List.getElem_ofFn` then leave `omega`-unclosable index-bound goals (`i < (List.ofFn s).length` vs `i < xs.length`).
  Prefer the `Functional`+`encode` pin and make the _encode_ side concrete (`#eval` it once), not the `Rel` side.

- 2026-10-23 — **A `List.head?`-over-`filterMap` whole-input decoder needs a _committed-prefix uniqueness_ lemma,
  and its crux is a character _dichotomy_, not a length argument.** `decodeFullX s = List.head? ((decodeRepeat …).filterMap
fun ⟨blocks,t⟩ => …)` returns the _first_ commit, so `= some bs` needs: (a) `bs` is _in_ the filterMap (by
  `decodeRepeat_prefix_concat` + the tail-decode-over-suffix transport), and (b) every commit equals `bs` — which needs
  the block run to be unable to consume into the terminal tail's pad byte, and the tail unable to start inside the
  block run's alphabet-only prefix. Both halves need one primitive each: "a block element (`Rel (count k (satisfy
char))`) never relates to a string containing a pad byte" (from `Rel_count_satisfy_forall` + `char pad = false`,
  closed by `decide`) and "a tail element always relates to a string containing a pad" (from the tail `Iso.unapply`
  emitting a concrete `[c₀, c₁, 61, 61]`/`[c₀, c₁, c₂, 61]`). Do not try to avoid the dichotomy by a pure length
  argument — the tail element's `count k (satisfy orPad)` predicate is lenient (accepts alphabet _or_ pad), so only
  the `Iso`'s 1..k-1-byte output restriction forces the pad, and that needs the content pin.

- 2026-10-22 — **`decodeFull p h n s : Option (List α)` double-wraps when `α` is itself a list type: for a
  block element `Codec (List UInt8)`, it returns `Option (List (List UInt8))` (a list of blocks), not
  `List UInt8`.** So a whole-input decoder that runs full blocks then a terminal tail and flattens to bytes
  must write `blocks.flatten ++ tail.flatten` (both sides are `List (List UInt8)`), not `… ++ tail`. This is
  the one place the _value type_ vs the _list-of-values_ distinction bites: the element's value is a byte
  list, so one decoded block is a `List UInt8` and the run of blocks is a `List (List UInt8)`; `decodeFull` of
  a single padded tail returns `some [[b]]` (or `some []` for the empty tail), and `decodeRepeat`'s step
  value `[b] : List UInt8` must be written `[[b]]` when passed as the `xs : List (List UInt8)` argument of
  `decodeRepeat_spec`/`relRepeat_cast`/`decodeFull_spec`.

- 2026-10-22 — **`encodeRepeat p [x]` is NOT `rfl`-equal to `encode p x`; it returns `⟨q + 0, concat s emptyBytes⟩`**
  (the `[]` tail of the match appends a `concat`-with-empty step and a `n + 0` length). The encoder-soundness
  bridge `encodeRepeat_rel p [[x]]` then gives `relRepeat (Rel p) [[x]] (q + 0) (concat s emptyBytes)`, not
  `relRepeat … q s`. Bridge with a one-line `concat_empty_eq {n} (s : Bytes n) : concat s emptyBytes =
cast (congrArg Bytes (Nat.add_zero n)) s` (prove by `Bytes.ext; intro i; unfold concat; have hi : i.val < n
:= i.isLt; simp [hi]`), then `rw [concat_empty_eq]` + `(relRepeat_cast (Rel p) [[x]] (Nat.add_zero q) s).1`.
  (Keep a _bounded_ element encoder on the bare `Codec.encode` so its result length is the exact `q`, and pay
  the `+0`/`concat-empty` transport only where `encodeRepeat` is forced.)

- 2026-10-22 — **`relRepeat_cons R x xs` returns an `Iff` but is a _function_ until the byte string `s` is
  supplied — `relRepeat_cons (Rel p) x xs s`, then `.mpr ⟨m, hm, s₁, s₂, h_splice, hx, h_rest⟩` to build
  `relRepeat` from its `∃` witness (NOT `.2`, which is an `And` projection and fails "projections cannot be
  used on functions"/`Function.mpr`).** The `(s : Bytes n)` argument is explicit; without it the term is
  `(s) → Iff` and both `.mpr`/`.2` project off a function. Also `relRepeat_nil R` takes an explicit `s
: Bytes n` too (`relRepeat_nil R s : relRepeat R [] n s ↔ n = 0`).

- 2026-10-22 — **`decodeFull_spec`'s uniqueness argument `huniq` has an exact shape to match argument-free:**
  `∀ {x y : List α} {n : Nat} (s : Bytes n), (x, Suffix.empty n) ∈ decodeRepeat p h n s → (y, Suffix.empty n)
∈ decodeRepeat p h n s → x = y`. Pass it as `(fun {x y} {m} (t : Bytes m) => <Xxx>DecodeFull_unambiguous (s := t))`
  where the named `<Xxx>DecodeFull_unambiguous` lifts the `relRepeat`-level `relUnambiguous` ind (itself proved by
  the `relRepeat_nil`/`relRepeat_cons` productivity argument with the element's `Rel_<elem>_len` fact pinning the
  block width `m = k` against `m = 0` via `omega`).

- 2026-10-22 — **The transport lemma family for a padded-base whole-input roundtrip is now _provable_, and it is a
  set of three generic `Bytes`-level facts (put them in a common module, reused by every padded/uniform base):**
  `bdrop_concat {m₁ m₂} (sb : Bytes m₁) (st : Bytes m₂) : bdrop m₁ (concat sb st) = cast (congrArg Bytes
(Nat.add_sub_cancel_left m₁ m₂).symm) st` (prove by `Bytes.ext; intro i; rw [cast_bytes_val' (e := …)]; dsimp
[bdrop, concat]; have hnot : ¬ i.val + m₁ < m₁ := by omega; simp [hnot]`); `concat_eq_drop_prepend sb st :
concat sb st = (Suffix.drop m₁ (concat sb st)).prepend (cast (congrArg Bytes (show m₁ = (m₁+m₂) - (Suffix.drop
m₁ (concat sb st)).remaining from by dsimp [Suffix.drop]; exact (Nat.sub_sub_self (Nat.le.intro rfl : m₁ ≤ m₁+m₂)).symm))
sb)`; and `decodeRepeat_prefix_concat p h xs sb st : (xs, Suffix.empty m₁) ∈ decodeRepeat p h m₁ sb → (xs,
Suffix.drop m₁ (concat sb st)) ∈ decodeRepeat p h (m₁+m₂) (concat sb st)`. The last one is `decodeRepeat_spec … .2`
  with witness `srel = cast … sb`; its two sub-goals are `concat sb st = r.prepend srel` (by `concat_eq_drop_prepend`)
  and `relRepeat (Rel p) xs … srel` (by `relRepeat_cast` over `hidx` plus `sb = s₀` from `prepend_empty_eq`). These
  three are the whole _new_ construction the roundtrip composes on top of the already-proved
  `decodeRepeat_spec`/`encodeRepeat_rel`/`relRepeat_functional`; do **not** attempt to re-derive the `splice`/`concat`
  arithmetic inline in each base.

- 2026-10-22 — **`Nat.sub n 0` is `rfl`-equal to `n`, and `m₁ - 0 = m₁`/`(m₁ - 0) = m₁` close by `rfl` (so do not
  carry a `Nat.sub_zero` cast when the index is literally `n - 0`).** This simplifies every full-consumption
  roundtrip: `s₀ : Bytes (m₁ - (Suffix.empty m₁).remaining)` is **already** `Bytes m₁` (both projections reduce via
  `rfl`), so `relRepeat_cast (Rel p) xs (Nat.sub_zero m₁) s₀` is usually unnecessary. But the _transparency_ boundary
  is a one-way trap: once you `unfold Suffix.empty` (turning it into the structure literal `{ remaining := 0, …​}`),
  an already-bound `s₀ : Bytes (m₁ - (Suffix.empty m₁).remaining)` keeps the _abstract projection_ `(Suffix.empty
m₁).remaining` while the goal's `prepend`/`splice` wants the _reduced_ `{ remaining := 0 }.remaining` — the two are
  not definitionally equal under that unfold, so `rw [prepend_apply]` then fails with the dependent motive error.
  The fix: **do not unfold `Suffix.empty` by hand; close the `(Suffix.empty m₁).prepend s₀ = s₀` identity by
  `apply Bytes.ext; intro i; simp [Suffix.prepend, Suffix.empty, splice, concat]`** (let `simp` unfold all four together,
  which handles the projection atomically rather than splitting it).

- 2026-10-22 — **`prepend_apply`/`splice_apply` introduce a `cast (congrArg Fin (splice_add (Nat.sub_le …​))).symm i`
  index, and reducing it needs `rw [cast_fin_symm]` (the _full-index_ form, which rewrites `cast (Eq.symm (congrArg Fin e))
i` to `⟨i.val, …​⟩`), **not** `cast_fin_val`/`cast_fin_symm_val` (the `.val`-only forms) — the `.val` forms fail with
  a dependent-motive error because the surrounding `concat`'s `if h : ↑(cast … i) < m` scrutinee uses the full `Fin`
  (its bound proof `h` feeds `s ⟨↑(cast … i), h⟩`).** After `rw [cast_fin_symm]` you get a leftover
  `splice_add`/`Nat.sub_sub_self` arithmetic proof goal (`… = n`), closed by `omega`. Also: `cast (congrArg Bytes e) s =
cast (congrArg Bytes e') s` for two _different_ proofs `e e' : n = m` is `cast_bytes_irrel e e' s`, but when the two
  casts are _definitionally_ the same term (e.g. `srel = cast (idx) sb` where `idx` is literally `hidx.symm`),
  `rw [hsb']` closes the goal and a following `apply cast_bytes_irrel` is a no-goals error — remove it.

- 2026-10-22 — **The whole-input roundtrip for a _padded_ base (full-block `Run` + terminal tail) is the genuine
  "one new proof" the design flags, and it turns on three transport facts that are each separately-provable but
  must be _built_, not assumed:** (a) the block-prefix reconstruction `(Suffix.drop m (concat sbx stx)).prepend
sbx = concat sbx stx` (up to the `(m+t)-m = t` / `(m+t)-t = m` length casts via `Nat.add_sub_cancel_left/right`
  and `Nat.sub_sub_self`), threading `s = concat sbx stx` → `bdrop_splice`/`concat_eq_splice` → `Suffix.ext`;
  (b) the tail decode `decodeFull <tailElem> …` of the _remaining_ `stx` (not the whole `s`), recovered by the
  element-level `encode_rel`→`encodeRepeat_rel`→`relRepeat_cast` chain; (c) the `List.head?`-over-`filterMap`
  selection needs the `filterMap` to be exactly `[result]`, i.e. `Unambiguous` of the block element _and_ the
  tail element (the `b64BlockDecodeFull_unambiguous`/`b64TailDecodeFull_unambiguous` pair). Do not try to
  shortcut around the `Suffix`/`Bytes`/`splice`/`prepend`/`cast` threading — it is the substance of the proof.

- 2026-10-22 — **`termination_by` on a `where`-nested recursive proof must name the _helper's own_ parameter, not the
  outer theorem's binder.** A `theorem f (bs) : … := exact go bs where go : (l : List α) → …` with `go` recursing
  three-elements-deep (`b0 :: b1 :: b2 :: t2 ↦ go t2`) needs `termination_by l => l.length` **inside `go`'s
  definition** (`decreasing_by …` right after the `where` cases) — writing `termination_by bs.length` after the whole
  theorem errors `Unknown identifier bs.length`. Also: `decreasing_by simp_arith` is **deprecated** (shorthand for
  `simp +arith +decide`); write `decreasing_by simp +arith` to stay zero-warning. A 3-deep/short-block-length recursion
  is the classic case where plain `induction` gives an IH only on the _immediate_ tail, not the `t2` you need — use the
  `where` helper with its own `termination_by`.

- 2026-10-22 — **A _terminal-tail_ inductive has a _bijective_ `List UInt8` flatten, unlike a homogeneous
  `List (List UInt8)` (which is NOT bijective).** "full blocks (width `k`) then at most one terminal tail (1..k-1 bytes)"
  as `inductive B where | nil | full (b0…b(k-1)) (rest : B) | tail1 … | tail(k-1) …` flattens to `List UInt8`
  **injectively**: the block/tail boundary is recovered from `length mod k` (0 ⇒ all-full, `r ∈ 1..k-1` ⇒ a single
  `r`-byte `tail r`), and the terminal constructors carry no continuation. So a **uniform facade over one value type
  `List UInt8`** is achievable by a _bijective_ transport `B ↔ List UInt8` (flatten + split-by-`length mod k`), with
  roundtrip `flatten ∘ split = id` proved by a 3-/5-deep `where` recursion and `split ∘ flatten = id` by structural
  induction on `B`. This is distinct from the earlier "flatten `List Block × Option Tail` → `List Block` is
  non-bijective" note: that failure is about colliding a _full-width_ tail with the _last full block_; a
  **value-type-level** terminal-tail maker (`tail r` has no continuation, `full` always has full width `k`) avoids the
  collision, so the flatten is genuinely injective.

- 2026-10-22 — **`Bytes n → List UInt8` is materialized by `List.ofFn s`; do not assume a stable
  `List.ofFn_get`-style lemma name.** `abbrev Bytes n := Fin n → UInt8`, so `def bytesToList {n} (s : Bytes n) : List UInt8 :=
List.ofFn s` and `def listToBytes (l) : Bytes l.length := fun i => l[i]` are the two directions of a `Bytes n ↔ List UInt8`
  bridge. Proving `bytesToList (listToBytes l) = l` needs a "`List.ofFn (fun i => l[i]) = l`" fact; the stdlib lemma name
  (`List.ofFn_get` vs `List.getElem_ofFn`) is **version-specific** (absent in the rusted 4.30 pin), so either `funext`/
  `Fin`-induct by hand or defer the inverse lemma until a roundtrip proof actually needs it (the facade types alone need
  only the two definitions, not their inverse law).

- 2026-10-20 — **The converse (`decode s = some v → encode v = s`) is _false_ unless the decoder is
  **canonical**; a "lenient" block decoder that accepts dropped-bit non-canonical encodings breaks it.**
  For a fixed-width/padded _block_ `List UInt8 → List UInt8`, the "lenient" decode that only checks pad
  _positions_ (not that the recovered value's low bits are zero) accepts e.g. `"AB=="` → byte `0x00` for the
  1-byte tail, even though the canonical encoder emits `"AA=="`. So `decode "AB==" = some 0x00` holds but
  `encode 0x00 = "AB=="` is false, and the converse is **unprovable**. The fix is not a theorem: switch the
  parser to the **re-encode-checked** block apply (`apply cs = (lenientDecode cs).filter fun bs => unapply bs = some cs`),
  i.e. `apply cs = some bs ↔ unapply bs = some cs` — then decode only succeeds on canonical blocks and the
  converse `apply cs = some bs → unapply bs = some cs` is the literal backward `Iso.law` direction. Detect the
  gap by `#eval` on a concrete dropped-bit vector (`lenientDecode "AB=="` vs `apply "AB=="`), not by reading names.

- 2026-10-20 — **A successful _structural_ parser's completeness (`parse s = some (v, r) → charsOf v ++ r = s`)
  is a direct structural recursion on `s` — but the recursive branch only fires four/eight elements _deep_,
  so pattern-match the full depth and reassociate `++` before rebuilding.** Write `parse`'s list pattern as
  `c0 :: c1 :: c2 :: c3 :: rest` (or `c0..c7 :: rest` for an 8-wide block) so `rest` is a **strict subterm** and
  the recursive IH call `parse rest` is accepted by the termination checker. In the full-block branch, `unfold
charsOf` then `rw [List.append_assoc]` **before** `rw [ih]`: the goal is `(fullChars ++ charsOf v') ++ r'`
  (definitional nesting), not `fullChars ++ (charsOf v' ++ r')`, so `ih : charsOf v' ++ r' = rest` won't match
  until `List.append_assoc` reassociates; then `rfl` closes `fullChars ++ rest = c0::…::rest` after the block
  `unapply bs = some cs` fact pins `fullChars = [c0..ck]`.

- 2026-10-20 — **Core `Nat.toDigits base n : List Char`/`Nat.digitChar` are _not_ drop-in replacements for a
  fixed-width base-`N` encoder** — they are LSB-first, variable-width, **zero-un-padded**, run over `Char` (not
  `UInt8`), emit **lowercase** `a-f` for base ≥ 11, and `digitChar` hard-caps at `≥ 16 → '*'`. A fixed-width
  encoder (one byte → exactly `k` MSB-first, zero-padded `List UInt8`, uppercase hex, custom base32/64 alphabets)
  needs `Nat.toDigits 8 1 = ['1']` padded to `['0','0','1']` and its `Char` mapped through `Char.toUInt8` — a
  reverse + left-pad + map that is strictly _more_ allocating than the bespoke `valToX`/`bitAt`/`*BlockUnapply`
  over the same boxed `Nat` div/mod, so adopting it is a slowdown, not a simplification. There is **no**
  `Nat.ofDigits` (parse-back) in core. `Nat.toDigits` is only right as a non-law-bearing _display_ helper
  (`render base n`), kept outside the proven codec surface.

- 2026-10-20 — **The repetition-level _converse_ (`decode … = some v → encode v = some ⟨n, s⟩`) is a two-prime
  machinery, all free of `codec` changes: `relRepeat_functional` + `encodeRepeat_of_rel`.** First prove, by
  induction on the list, that a _list_ value relates to at most one length+bytes pair given the _step_
  relation is functional: `∀ xs n₁ n₂ s₁ s₂, relRepeat R xs n₁ s₁ → relRepeat R xs n₂ s₂ → ⟨n₁,s₁⟩ = ⟨n₂,s₂⟩`
  from `relFunctional R` (the step-level `∀ a s₁ s₂, R a s₁ → R a s₂ → ⟨n₁,s₁⟩ = ⟨n₂,s₂⟩`). The induction's
  cons case closes by `hR x s₁₁ s₂₁ hx₁ hx₂` on the heads (then `cases` on the resulting **Sigma** equality),
  recurse `ih s₁₂ s₂₂`, `congrArg Sigma.fst` to get `n₁-m = n₂-m → n₁ = n₂` via `omega` (add the `m ≤ nᵢ`
  witnesses), `subst`, then `cases hfull; rfl` for the `.snd`. Then `encodeRepeat_of_rel p (hR :
relFunctional (Rel p)) : relRepeat (Rel p) xs n s → encodeRepeat p xs = some ⟨n, s⟩` is
  `encodeRepeat_ne_none` + `cases (encodeRepeat p xs)` + `encodeRepeat_rel` + `relRepeat_functional` — **never**
  hand-roll the `concat`/`splice` reassembly in `encodeRepeat`'s body. `relFunctional (Rel d)` **is**
  `Functional d` definitionally (unfold `Functional`), so providing `Functional elem` is enough.

- 2026-10-20 — **`Functional` (one value → one bytes pair) has free generic lemmas; add them once, don't prove
  per codec.** `Functional (satisfy p)` (two `Rel_satisfy` then `rw [hs₁', hs₂']`), `Functional (count k
(satisfy p))` (induction on `k`; the succ case pins `a₁.1 = a₂.1` and `a₁.2 = a₂.2` from `Iso.cons.apply`
  via `List.cons.inj` of `ha₁.trans ha₂.symm`), and the key `Functional_iso i d hd : Functional (iso i d)`
  closes by `(i.law a b).1` twice (⇒ `i.unapply b = some aᵢ`, a _function_, ⇒ `a₁ = a₂` via `Option.some.inj`)
  then `hd a₁ s₁ s₂`. `Functional (iso blockIso (count k (satisfy p)))` is then `Functional_iso` + `Functional_count_satisfy` — this is what makes each fixed-width element's converse close without any digit math.

- 2026-10-20 — **Canonical-encoding ("output alphabet-only") theorems are a _backward_ forall, not a forward
  relation: `Rel_count_satisfy_forall` + `relRepeat_forall`.** `Rel (count k (satisfy p)) xs s → ∀ i : Fin n,
p (s i) = true` lifts to the whole run via `relRepeat_forall p (hstep)`, where `hstep` passes each `Rel
<elem> x t` through `Rel_iso` to reach `Rel (count k (satisfy p)) a t` and then `Rel_count_satisfy_forall`.
  Combined with `encodeRepeat_rel` (encode → `relRepeat (Rel elem)`), the theorem `encode{X} bs = some ⟨n,s⟩ →
∀ i, digit (s i) = true` is `relRepeat_forall digit (fun x .. => …) bs n s (encodeRepeat_rel …)`. `Rel_count_satisfy_forall`'s succ case walks `Rel_iso`/`Rel_seq`/`Rel_satisfy`, `subst m` (the `Rel_satisfy`
  pins the head length to `1`), then splits `i.val < 1` with `splice_prefix_read` (head) vs `splice_apply` +
  `unfold concat` + `rw [cast_fin_symm]` + `dsimp` + `simp [hi]` (tail — the `cast_fin_symm` leaves a `1 + (n-1)
= n` side-goal closed by `omega`).

- 2026-10-20 — **A _concrete_ rejection `decodeFull p h n s = none` for a fixpoint decoder closes by unfolding
  the `WellFounded.fix` one step and letting `decode p s` compute — no `Rel`/`satisfy` inversion.** When `decode p
s = []` reduces by `rfl` (e.g. the block `Iso.apply` returns `none` for an over-`255`/illegal block), then
  `unfold decodeFull; rw [WellFounded.fix_eq]; simp only; rw [Codec.decodeFullStep.eq_def]; simp; rfl` proves
  `= none` (the `simp only` reduces the `match ⟨n, s⟩` scrutinee to the `succ` branch; `decodeFullStep` on the
  empty `.attach` list is `none`). Do **not** `rw [decodeFullStep]`/`unfold decodeFullStep` (it has `match_3`
  cases with dependent `.attach` motives); use `Codec.decodeFullStep.eq_def` (the auto-generated equation) and
  let `simp` discharge the `.attach`.

- 2026-10-20 — **`simp` applies `or_self` (`p ∨ p ↔ p`), so `rcases` on a _deduplicated_ disjunction after
  `simp` needs fewer patterns than the list length.** `b ∈ [c0, c1, 61, 61]` simplifies to `b = c0 ∨ b = c1 ∨
b = 61` (the duplicate `61` disjuncts merge), so `rcases hb with rfl | rfl | rfl` (3 arms), not 4. This bites
  when a tail builder emits repeated `=` pads of the same literal; count _distinct_ disjuncts after `simp`,
  not input list elements.

- 2026-10-20 — **A plain `decide` on a _closed_ structural-match equality is `[propext]`-only (definitional),
  `native_decide` leaks a `.native`/IO axiom — never use `native_decide` in a gate theorem.** If the goal
  is `someTailTerminalParser [literal, byte list] = none` where the parser is a `def` of `if`/`match` over
  `Bool`/`Nat` and the literals are concrete, `unfold <parser>; decide` closes it and `#print axioms` reports
  only `[propext]` (better than `[propext, Quot.sound]`). The existing "`decodeFull`/`Rel` have no `Decidable`"
  caveat applies to the _fixpoint_ decoder, **not** to a hand-written structural `match` parser over `List
UInt8`/concrete bytes.

- 2026-10-20 — **`l ++ []` is not `rfl`-equal to `l`; in an induction step that emits `chars ++ []` vs the
  lemma's `chars`, `rw [← List.append_nil chars]` first (it rewrites `chars` to `chars ++ []`).** A total
  char-emitter `chars : B → List UInt8` leaves the `full/tail` case goal as `parse (chars)`, while the helper
  lemma is stated as `parse (chars' ++ rest) = …`; for the `rest = []` base, `simpa`/`rw` do not see the `++ []`,
  so insert `rw [← List.append_nil <chars>]` to align, then `rw [helper … []]`. (`List.append_nil : l ++ [] =
l`; the `←` direction is `l = l ++ []`.

- 2026-10-20 — **Make an illegal _run-level_ shape impossible by replacing a homogeneous list type with a
  terminal-maker inductive.** A "blocks + at most one terminal tail" language whose value type is
  `List (List UInt8)` _admits_ "tail-then-full" (`[[b],[b0,b1,b2]]`) by construction; no guard/filter/
  post-condition over that type is "perfect" because they all detect-and-discard an already-built illegal
  value. The fix is a value type whose _tail constructors have no continuation_: `inductive B where | nil
| full (b0 b1 b2) (rest : B) | tail1 (b0) | tail2 (b0 b1)` — `tail1`/`tail2` are terminal, so "data after a
  tail" has no term, and the only way to write "a 1-byte then a 3-byte block" is `full 0 0 0 (tail1 x)` (the
  _valid_ order). The decoder `Bytes/List UInt8 → Option B` is total and returns `none` exactly when no `B`
  term matches; every `some v` _is_ canonical. Rejection is the _absence of an inhabitant_, not a filter.
  This is the honest "types dictate impossibility": the compiler rejects the illegal shape.

- 2026-10-20 — **A "flatten" from a two-part sum/product value to a plain list is usually _non-bijective_,
  so there is no flattening `Iso` — don't plan one.** "`full* (tail)?`" as `List Block × Option Tail` →
  `List Block` via `(bs, t) ↦ bs ++ t.toList` is NOT injective (a full-width `t` collides with it being the
  last _full_ block of `bs` with `t = none`). If you need both shapes, keep the two-part value (or the
  terminal-tail inductive above) as the _proven_ type and drop the flat list from the proven surface; a
  `List`-append that injects an `Option`/tag is a transport, not a law-bearing `Iso`.

- 2026-10-20 — **`open Codec` (or any `open`) makes bare lowercase constructor names parse as _pattern
  variables_, breaking `match`/`induction` arms.** After `open Codec`, `| empty => … | full b0 b1 b2 r => …`
  in a `def/inductive` over your own `inductive B` fails: `empty` resolves to `Codec.empty` (type mismatch)
  and `full`/`nil`/`tail1` are read as lowercase pattern _variables_ ("invalid pattern … `B.full` would be
  valid"). Always qualify your own constructors (`B.full …`, `B.nil`) or use leading-dot notation (`.full`,
  `.nil`), and rename `empty` (→ `nil`) to dodge the `Codec.empty` clash entirely.

- 2026-10-20 — **Reuse an existing lenient block-decoder (with its per-shape identities) to build a strict
  structural parser, instead of re-deriving the digit/`if` math.** A strict whole-input parser over a
  terminal-tail inductive needs each block's `List bytes → Option (List bytes)` (1–N byte shape) and the
  per-shape `decode (encode bs) = some bs` facts; if a _lenient_ block decoder plus `*_unapply_single/pair/
triple/…` theorems already exist, write the strict parser as `match lenientDecode [c0..ck] with | some
[b] => tail1 b | some [b0,b1] => tail2 b0 b1 | some [b0,b1,b2] => full … (recurse) | …`, and prove the
  per-shape lemmas with a single `simp [parser, charEmitters, theUnapplyLemma]` — no `by_cases`/`omega` digit
  re-derivation, no byte-identity reconstruction. The strictness is all in the _value type_ + which patterns
  recurse, not in new digit proofs.
- 2026-10-20 — **`Codec.decodeFull` and `Rel d` have **no** `Decidable` instance, so concrete value-check
  vectors cannot close with `decide`/`by_decide` — only `native_decide`, which leaks a `.native` axiom and
  must stay out of gate theorems.** `decodeFull p h n s` recurses via `WellFounded.fix` and `Rel` is a
  structural `Prop` over the `Codec` AST, so `decide` on `decodeFull … = some […]` gets stuck at the
  `WaitFounded.fix`/`fix_eq` stage and `Rel …` fails to synthesize `Decidable`. The gate-clean (`[propext,
Quot.sound]`-only) route is `decodeFull_spec` + `decodeRepeat_spec` + `relRepeat`/`relRepeat_cons` +
  `encode_rel`, where each _block_-level `Rel elem bs s` fact is obtained **from the encoder**
  (`encode_rel elem bs` gives `encode elem bs = some ⟨k, s⟩ → Rel elem bs s`, and `encode elem bs = some
⟨k, literal⟩` closes by `simp` because the block `Iso`'s `unapply` is a plain `match`, not a fixpoint).
  But `encode elem bs` itself does **not** `rfl`-reduce end-to-end: the inner `encode (count k (satisfy p))`
  leaves the `if p (single-bytes) …` conditions unfolded, and closing them needs `decide` on each concrete
  digit arithmetic (`valToX c = i`, `pred b = true`), which **does** `decide`-close (they are closed `Nat`/
  `Bool` equalities). Keep `native_decide` only in a **bench `example`/`#eval`** (not a proved theorem).

- 2026-10-20 — **The forward direction `Rel (count k (satisfy p)) l s` (from `s = byte-image of l` + `∀ b ∈ l, p b`)
  is a genuinely-needed lemma with a `splice`/`cast`/`(k+1)-1` index-cast gotcha: the succ case must walk down
  via `count (k+1) = iso cons (seq (satisfy p) (count k (satisfy p)))`, splitting `s` at `1`, and the tail is
  `Bytes ((k+1)-1)` which is **not** definitionally `Bytes k`** — so rather than `bdrop 1 s` (type-mismatch
  against the IH's `Bytes k`), define `s' : Bytes k := fun i => s ⟨i.val + 1, by omega⟩` and cast it into the
  `splice` suffix (`cast (congrArg Bytes (by omega : k = (k+1)-1)) s'`), proving the head via `Rel_satisfy`
  and the tail via the IH on `s'`.** The splice equality `s = splice 1 (single b) (cast … s')` closes by
  `Bytes.ext` + `splice_apply` + `by_cases h : i.val < 1` (head) / `simp` + the image hypothesis (tail). This
  `(k+1)-1 = k` (a `Nat.sub` reduction, **not** definitional) is the recurring gotcha behind every
  length-indexed `Bytes n` recursion step.

- 2026-10-20 — **`count k (satisfy p)` fixes the _consumed byte window_ (`k`), NOT the decoded _value_
  length — so a cross-block (run-level) invariant is not expressible as a refinement of the element, it
  needs a run-level guard.** A block codec `iso blockIso (count k (satisfy pred))` consumes exactly `k` bytes
  per element _regardless_ of what the value is; padding/`=`-position affects the _value_ (`1` vs `3` bytes),
  not the window. So an intra-block property (e.g. `=` in a non-terminal position _within_ a `k`-char block) is
  correctly rejected by the block `Iso`'s backward law, but a _cross-block_ property (e.g. "no data after a
  terminal `=`", i.e. a `=`-terminated block must be the _last_ block) is **accepted** by `decodeRepeat`
  (grouping input into fixed `k`-wide blocks) and must be enforced by either (a) splitting the run into a
  full-block `decodeRepeat` prefix + an optional terminal **tail** block via `seq`/`alt`/`empty`, or (b) a
  whole-input post-condition theorem on `decodeFull` — **not** by a length argument (`"padded block has value
length < k so it can't be followed by a full block"`), which is a _false premise_: the window, not the value
  length, is what `count k` fixes.

- 2026-10-20 — **Case-insensitivity is NOT expressible as a `Codec` value over a strict `Iso`.** A
  normalizing map (e.g. hex `A` and `a` → the same nibble) is **not a bijection** (two inputs → one output), so
  it cannot be an `Iso` field and it breaks `Unambiguous` (two distinct inputs relate to one value). If a format
  spec mandates case-insensitive _decoding_ (RFC 4648 §8 for hex), that must live in a **separate
  case-normalizing facade** outside the `Codec` value — a `satisfy`+normalizing-`iso` `Codec` is a category
  error. Record a case-insensitive acceptance as a **non-goal** for the `Codec` value, not a test that the
  `Codec` "should" pass.

- 2026-10-20 — **When re-anchoring a plan to a rewritten surface, verify the _ground truth_ of every "the code
  does X" claim before stating it as fact — a spec-driven plan that asserts "the decoder accepts lowercase /
  rejects trailing padding" against code that provably does the opposite will be caught by a reviewer and
  must be re-derived.** For `decodeFull`/`decodeRepeat`-based surfaces: the whole-input decoder is
  `decodeFull elem consumesByte n s : Option (List α)` (or `List (List α)` for a block element), **not** a
  bespoke `decode : List UInt8 → Option (List UInt8)` facade; and the block vs fixed-width split is element
  `Codec UInt8` (one byte) vs element `Codec (List UInt8)` (a multi-byte block). Write an explicit
  "ground truth the plan must respect" section with the verified signatures and the deterministic outcome of
  the contested case (`decodeFull … "Zg==AAAA" = some […]`), so reviewers re-check claims, not guess.

- 2026-10-19 — **A `Codec`-value rewrite of a _fixed-width_ digit codec (one byte per element) is a
  own template; a _block_ codec that packs bits across bytes is NOT.** The fixed-width recipe —
  element `Codec UInt8 := iso blockIso (count k (satisfy digitPred))` plus the repetition triple
  `decodeRepeat`/`encodeRepeat`/`relRepeat` — works because the block `Iso` (`k` digits ↔ one byte) is a
  clean bijection: both `law` directions close with `omega` on a per-digit `≤ bound` plus `Nat.div_add_mod`.
  A base-N codec whose digits _cross_ byte boundaries (e.g. 40 bits = 8 five-bit chars → 5 bytes) has element
  `Codec (List UInt8)` and a block `Iso` whose **backward** law (`apply cs = bs → unapply bs = cs`) is
  _encode-injectivity_: recover each char `cᵢ = valToX (σᵢ(bs))` from the bytes. The old bespoke code only
  proved `decode ∘ encode = id` (`decode (encode bs) = some bs`); it never proved `encode ∘ decode = id` on
  valid input, which is exactly the missing `Iso.law` direction. Reuse the existing byte-extraction
  identities (`byte0..byte4`) _read in reverse_ for the recover step, and a `char_eq_valToX_of_valid`
  lemma (`c = valToX i` when `valid c ∧ toVal c = i`). Do **not** reach for `by_contra` (it needs
  `Classical.choice` and breaks the `[propext, Quot.sound]` gate): destruct each `char = pad` /
  `valid char` guard with `by_cases`, close the impossible branches with `simp at h` + `omega`.

- 2026-10-19 — **`Unambiguous (iso i d)` only needs `i.apply` to be _functional_ (deterministic), not the
  full `Iso.law` — but `encode_rel`/`encodeRepeat_rel`'s `iso` case _does_ need the **forward** `law`
  (`unapply x = some a → apply a = some x`).** So `Unambiguous` of a `Codec.iso` leaf transfers for free from
  the inner `Unambiguous` (`some x = some y`, `Option.some.inj`) with no bijection proof, yet you still must
  construct the `Iso` with its full `law` field (both directions) before you can write the `Codec.iso`.
  The backward direction is the genuinely-new sharp edge for non-bijective-looking block maps.

- 2026-10-19 — **`Productive (count k (satisfy p))` holds only for `k ≥ 1`:** `count 0` relates the empty list
  to the empty string, so it is _not_ productive (`Rel (count 0 …) xs s → n = 0`, not `n ≠ 0`). State the
  generic `ConsumesByte` witness as `consumesByte_count_satisfy_succ p k : ConsumesByte (count (k+1)
(satisfy p))` (via `Productive_count_satisfy_succ`), never the `k = 0`-inclusive form, and write each base's
  width as `k = m + 1` (`show 8 = 7 + 1 by rfl`) before applying it.

- 2026-10-19 — **Factor the generic per-base proof lemmas into one shared module and `open` it, rather than
  re-deriving them verbatim per base** — when a proof recipe repeats across N sibling modules, the generic
  lemmas (`Productive_iso`/`_seq_left`/`_count_succ`/`_satisfy`, `Unambiguous_satisfy`/`_iso`,
  `Rel_count_satisfy_len`, `count_satisfy_unambiguous`) are parameterized only by a byte predicate `p` and a
  width `k`, so they belong in a `Common` namespace. A left-nested 8-way `&&` (`(… && d7) = true`) decomposes
  cleanly with `simpa only [Bool.and_eq_true_iff] using hv` into a _left-nested_ `∧`, then `.1.1.1.…` /
  `.….2` — do **not** hand-nest `Bool.and_eq_true_iff.mp` (the `.1`/`.2` count is easy to get wrong).

- 2026-10-19 — **Proving a byte-substrate codec's _unambiguity_ (`Unambiguous d := ∀ x y n s, Rel d x s →
Rel d y s → x = y`) is the linchpin that gates the inherited repetition-level roundtrip**
  (`decodeFull_spec` needs `huniq : (x, Suffix.empty n) ∈ decodeRepeat … → (y, …) ∈ … → x = y`). The
  working chain for a fixed-width `iso blockIso (count k (satisfy p))` leaf is: (1) `Rel (count k (satisfy p)) xs s`
  **pins the byte length** `n = k` (prove `Rel_count_len` by induction on `k`: the `satisfy` RHS gives
  `∃ h : m = 1`, `subst` it, then IH on the tail `s₂ : Bytes (n - 1)` gives `n - 1 = k`, close with `omega`);
  (2) `count k (satisfy p)` is unambiguous by induction on `k`, where the succ case peels the head byte via
  `splice_prefix_read` at index `0` and recovers the equal tails via `bdrop_splice`, then the IH on the
  (same-type) tails; (3) `iso` preserves unambiguity (`i.apply a = some x` twice, `a = a'` by the inner
  unambiguity, force `x = y` with `Option.some.inj`).

- 2026-10-19 — **There is **no `norm_num`** in a stdlib-only (no-mathlib) Lean library** — `norm_num` is an
  "unknown tactic" (the AGENTS rule lists it among `ring`/`nlinarith`/`fin_cases`/`interval_cases` as absent).
  Close `Fin`-index arithmetic goals with `omega`/`simp`/`decide` only.

- 2026-10-19 — **`Fin.val` of an anonymous `Fin` literal does **not** reduce for `omega`/`norm_num`/`decide`:**
  the goal `↑⟨0, h0lt⟩ < 1` (from a `splice_prefix_read p … ⟨0, h0lt⟩ hi` call, where `hi : i.val < m` must be
  supplied) sticks — `omega` reports a counterexample on the opaque atom `↑↑⟨0, h0lt⟩`, `decide` rejects the
  free variable, and `norm_num` doesn't exist. The fix is **`by simp`** as the `hi` argument (and for the
  `Fin n` well-formedness use a _named_ `have h0lt : 0 < n := by omega` first), because `simp` reduces
  `Fin.val ⟨0, _⟩` to `0` and closes `0 < 1`. Never leave `by norm_num`/`by omega`/`by decide` for such a goal.

- 2026-10-19 — **Use `splice_prefix_read … ⟨0, hlt⟩ hi` to extract the head byte of a `splice`-split prefix,
  and `bdrop_splice …` to recover the tail as the _same type_ `Bytes (n - m)`** — when two `Rel`/`relRepeat`
  witnesses both split the same `s` at the (productivity-pinned) length `m`, `s₁x = s₁y` follows by `Bytes.ext`
  (read each `i : Fin m` through `splice_prefix_read` twice and `trans`), and `s₂x = s₂y` by `rw [← bdrop_splice
… s₁x s₂x, ← bdrop_splice … s₁y s₂y]` then `congr 1` on the `s` equalities. This is the transport that makes
  an IH applicable over the _tails_.

- 2026-10-19 — **`subst` on a length-equal witness (`hm0 : m = 0`) that contradicts an earlier
  `have hlen : m = 3` hits "No goals to be solved"** — don't `subst` a length to a value that
  contradicts another surviving witness. Instead keep both equalities as `have`s and close the
  contradiction with a single final `omega` (`have hlen : m = 3 := …; have hm0 : m = 0 := by omega;
omega`). This is the relRepeat-`nil`-vs-`cons` productivity asymmetry case.

- 2026-10-19 — **`relRepeat` (the least-fixpoint list relation) is unambiguous for a productive
  `ConsumesByte` step by _list induction with `generalizing b n s`_, cased on `b` inside the cons case** —
  `rw [relRepeat_cons] at hb` does **not** fire when `hb`'s subject is still the variable `b`; you must
  `cases b` (→ `nil` / `cons y ys`) first so `relRepeat_cons` matches the `y :: ys` subject. The `nil`-vs-`cons`
  asymmetry closes by productivity (`Rel octElem _ s₁` forces `m = 3`, but `m ≤ n = 0` forces `m = 0`;
  `omega` on `m = 3` + `m = 0`).

- 2026-10-19 — **The inherited repetition roundtrip law** (`decodeFull (encodeRepeat …) = some bs`) **chains**
  `encodeRepeat_rel` (encoder → `relRepeat` witness) → `decodeRepeat_spec` `.2` (`relRepeat` witness →
  `(bs, Suffix.empty n) ∈ decodeRepeat …`, using `cast (congrArg Bytes (Nat.sub_zero n).symm) s` +
  `prepend_empty_eq` + `relRepeat_cast`) → `decodeFull_spec` `.2` (membership → `some bs`, gated by the
  `huniq` uniqueness fact above). The `huniq` itself is proved via `decodeRepeat_spec` `.1` twice +
  `prepend_prefix_eq` (to pin the two prefix witnesses `s₀x = s₀y` from the shared `t = (Suffix.empty n).prepend s₀`)
  - the list-level unambiguity.

- 2026-10-19 — **Define `Iso` `apply`/`unapply` as _named total functions_ and prove `law` as a _separate
  theorem_ (`octBlockIso_law : octBlockApply cs = some b ↔ octBlockUnapply b = some cs`), then pack with
  `{ apply := …, unapply := …, law := … }` — do **not** write the `law` field inline.** An inline `law := by
…` over a `match cs with | [d0,d1,d2] => …` list-literal pattern fights `simp [isoName]`/`dsimp`
  ("invalid argument: variable `isoName` is not a proposition") because the `structure`'s `law` field is not
  a reducible `simp` target, and `split at h` on the list-literal assigns _surprising_ variable names
  (`d1 d0 rest` from `[d0,d1,d2]`). Named functions let you `unfold octBlockApply`/`rw [octBlockApply]` on a
  _plain `def`_ and `cases cs`-destructure the list yourself with predictable names.

- 2026-10-19 — **`Nat.div_add_mod m n` returns `n * (m / n) + m % n = m` — the _divisor first_.**
  To get the `(m/n) * n + m%n = m` form a digit-sum identity needs, `simpa [Nat.mul_comm] using
Nat.div_add_mod m n`. `omega` does _not_ commute it for you, and an `omega`-only digit reconstruction
  (`(v/64)*64 + ((v/8)%8)*8 + v%8 = v`) closes with just `have h1 := Nat.div_add_mod v 64; have h2 :=
Nat.div_add_mod v 8; omega` — but **only** when the divisor-first form is in the local context; `omega`
  alone does not unfold `(v/8) % 8`.

- 2026-10-19 — **`decide` lemmas:** the iff is `decide_eq_true_eq : (decide p = true) = p`; the one-direction
  forward is `of_decide_eq_true : decide p = true → p`; there is **no** `decide_eq_false_eq` (the mirror is
  `decide_eq_false : ¬ p → decide p = false` / `of_decide_eq_false`). For a _left-associative_ `&&` chain
  `(P && Q && R) = true`, decompose with `(Bool.and_eq_true_iff.mp hv).1 : (P && Q) = true` then
  `(Bool.and_eq_true_iff.mp that).1 : P = true` / `.2 : Q = true`, and `(Bool.and_eq_true_iff.mp hv).2 : R =
true` — `hv.1`/`hv.2.2` on a `Bool` equality is an "invalid projection" (a `Bool` equality has no fields).
  Close a `(true && true && true) = true` residual (the `if (b : Bool)` desugars to `if b = true`) with
  `have hh : (true && true && true) = true := by decide; rw [hh]` — `simp`/`#reduce` do **not** reduce `=
true` on its own.

- 2026-10-19 — **`by_contra` needs `Classical` (or a `[Decidable]`/`Fintype` instance).** In a
  stdlib-only, `[propext, Quot.sound]`-only library (`no mathlib`, no `Classical.choice`), `by_contra` is
  **not** available; proving `octToVal e ≤ 7 ⇒ 48 ≤ e` from `octValid e = true` must be done with `by_cases
hle : e ≤ 55 <;> by_cases hge : 48 ≤ e` and `omega` in each branch (the invalid branches yield
  `octToVal e = 8`, contradicting `≤ 7`). Do not reach for `by_contra`/`classical` in such a library — it
  breaks the axiom gate.

- 2026-10-19 — **A digit-decomposition _uniqueness_ lemma (`d0·64 + d1·8 + d2 = e0·64 + e1·8 + e2`, each ≤ 7
  ⇒ triples equal) closes with `congrArg (fun x => x / 64) h` and `congrArg (fun x => (x % 64) / 8) h`**, not
  raw `omega` on `/`/`%`. After `have hm := congrArg (fun x => x / 64) h`, give `omega` the _bound_
  `have hbc : b * 8 + c < 64 := by omega` (so the `b*8+c` tail is `< 64`, hence `(a*64 + b*8+c)/64 = a`),
  then `rw [hm', hm''] at hm; exact hm` — `omega` proves `(a*64 + b*8 + c) / 64 = a` **given** the tail
  `< 64` bound, but the `%64 / 8` step additionally needs `c < 8` so that `(b*8+c) % 64 = b*8+c` and
  `(b*8+c)/8 = b`.

- 2026-10-19 — **A recursive inductive AST (`Codec α`) _cannot_ carry a constructor whose field is a
  _semantic_ predicate over that same AST's own denotation** — `many : (p : Codec α) → Productive p →
Codec (List α)` with `Productive p := ∀ x n s, Rel p x s → n ≠ 0` forms the definition-order cycle
  `Codec.many → Productive → Rel → Codec`, and Lean rejects both escapes: (a) a mixed `mutual` block
  (`inductive Codec` + `def Rel` + `def Productive`) is illegal — _"invalid mutual block: either all …
  inductive/structure … or all … definitions"_; (b) `mutual inductive Codec + Rel` is illegal on
  _universe_ — _"resulting type `Prop` differs from `Type 1`"_ — and this is irreparable, because
  `Rel : … → Prop` is pinned at `Sort 0` (`Prop`) while `Codec : Type → Type 1` is pinned at `Sort 1`.
  Consequence: **unbounded `many` must stay a _derived_ combinator outside the AST** (its denotation is
  the least-fixpoint `relRepeat`/`decodeRepeat`/`encodeRepeat` triple, each carrying `ConsumesByte p`),
  never a `Codec` constructor — do not propose adding `many` (or any other than `byte`/`satisfy`) to a
  byte-substrate `Codec` and do not budget for converting every `induction d` law to `Codec.rec`.

- 2026-10-19 — _*The paper's `many` (Rendel–Ostermann §3.4) is a *derived* combinator
  `many p = nil $ pure () | cons $ p ∗ many p`, and the F* reference has *no* `many` combinator at all —
  its unbounded-run primitive is `satisfy_many0`/`satisfy_many1` (aliases `many0`/`many1`), a
  `let rec satisfy_run_scan f bs` that scans a maximal leading run of the *finite* input byte list, one
  byte per step; no `Productive`/`ConsumesByte` witness is needed because the recursion is over the finite
  input, not over an arbitrary `p`'s denotation._* So a byte-substrate codec's _variable-width run_ is
  `takeWhile p := many (satisfy p)` realized over the productive repetition triple — exactly the landed
  `relTakeWhile`/`decodeTakeWhile`/`encodeTakeWhile` — and fixed-width base-N blocks are `count k (satisfy
p)` + a grouping `iso`. This is the authoritative resolution when someone asks "add `many` to the AST".

- 2026-10-19 — **`simp [F, hv] at hdec` _consumes_ `hv`** — if `hv : (P && Q && R) = true` is a `simp`
  argument while simplifying `hdec`, the rewrite unfolds `hv`'s `&&` chain and leaves `hv : True`, so a
  later `have hi : P = true := by simp [hv] at *; assumption` fails. Extract each conjunct **first**
  (`have hP : P = true := …; simp [Bool.and_eq_true] at hv; exact hv.1`, then `.2` for the rest), **before**
  the `simp` that _uses_ `hv` as a rewrite. Same failure mode for `by_cases hv : cond` followed by
  `simp [body, hv] at h`: the `by_cases`-introduced `hv` is the very hypothesis `simp` rewrites away.

- 2026-10-19 — **A partial-`Iso`'s `law` for a fixed-`k` digit↔byte grouping needs _two_ directions the
  forward-only `roundtrip` never stated: the converse bijection `valToX (xToVal e) = e` for _valid_ `e`,
  and a digit-decomposition _uniqueness_ lemma** (`d0·64+d1·8+d2 = b`, each `di ≤ 7`, ⇒ `di = b/…`) —
  proved with plain `omega` once the per-digit bounds are in scope (integers `di ∈ [0,7]` force
  `b % 8`, `(b / 8) % 8`, `b / 64`), but only after `omega` is given the bounds as separate `have`s; the
  nested `%`/`/` in `(b / 8) % 8 * 8 + b % 8 = b` needs `Nat.div_add_mod b 8` and `Nat.div_add_mod (b / 8) 8`
  as hypotheses — `omega` alone does not unfold `(b/8) % 8`.

- 2026-10-19 — **`UInt8.toNat_inj` is an `iff` (`a.toNat = b.toNat ↔ a = b`), not a function — `apply
UInt8.toNat_inj` fails "function expected" — and `UInt8.ofNat_toNat` is a _closed_ proposition
  (`UInt8.ofNat x.toNat = x`) that `exact UInt8.ofNat_toNat c` also rejects ("function expected … applied
  to c").** To lift `toByte n = b` (`toByte n := UInt8.ofNat n`) to `n = b.toNat`, use
  `have hb' := congrArg UInt8.toNat hb; simpa [toByte, UInt8.toNat_ofNat', Nat.mod_eq_of_lt hlt] using hb'`
  with `hlt : n < 256`; to close `toByte x.toNat = x` use `by simp [toByte]` (which folds
  `UInt8.ofNat_toNat` internally) rather than naming the theorem.

- 2026-10-18 — **Adding a predicate-guarded byte token (`satisfy : (A → Bool) → Codec A`, decoding
  "first element iff `p` it") to an inductive AST that is exhaustively `match d`ed in `Rel`/`decode`/
  `decodeFast`/`encode` (and every packed/committed mirror) means _every_ match gains a case, and the
  `satisfy` proofs mirror `byte` with one extra conjunct.** Two gotchas: (1) the `¬p` decode branch
  (`by_cases hp : p (s ⟨0, ·⟩)` ) reduces `decode (satisfy p) s` to `[]`, so the `decode_spec`-style
  bidirectional law must prove `¬ Rel (satisfy p) x s₀` by contradiction — `Rel` in the `satisfy` case is
  `p x = true ∧ ∃ h : n = 1, h ▸ s₀ = single x`; extract `p x = true`, then reconstruct `x = s ⟨0, hnpos⟩`
  from the prefix `s = r.prepend s₀` via `prepend_prefix_read r s₀ ⟨0, hnpos⟩ hlt` (not `rw [hs] at hb`,
  which fails because the goal is a _subexpression_ equality, not a whole-buffer occurrence), and close with
  `exact False.elim (hp hpx')` — `exact hp hpx` fails when the residual goal is still a membership `(x,r)∈[]`,
  not a bare `False`. (2) when an earlier `rw [decode]` already unfolded the scrutinee in the goal, a later
  `rw [decode]`/`rw [hdec]` does **not** match; instead `have hdec : decode … = [] := by simp [decode, hn, hp]`
  as a _separate_ goal, then `rw [hdec]` — the `decode` in `hdec`'s proof is a fresh definition, the one in the
  goal is already unfolded. (3) for the `p x = true` forward half and the packed/`decodeArray`/`decodeOne`
  refinement, the predicate on the first byte is `p a[0 + i]` after `bdrop i (·) ⟨0, ·⟩` unfolds — `simpa`
  bridges `p a[i]` (the packed decoder's spelling) to `p a[0 + i]` (the spec `bdrop` spelling).

- 2026-10-18 — **The extensibility primitive of a byte-substrate codec (an inductive `Codec α` over
  `Bytes n := Fin n → UInt8`) is `satisfy : (UInt8 → Bool) → Codec UInt8` (the byte-token-with-guard),
  and variable-length / multibyte / self-delimiting tokens are a _run_ over it (`takeWhile p` = the
  maximal prefix with `p b`), not a lookahead or per-byte-dispatch constructor.** A single-byte
  `satisfy` cannot recognize a varint (LEB128: consume until the high bit clears) or a UTF-8 symbol
  (1–4 contextual bytes) — and it must not try: the run (`many (satisfy p)` / `decRepeat`/
  `encodeRepeat` over `satisfy`) plus a downstream `iso` that folds the run's bytes is what decodes a
  varint (`takeWhile highBitSet` + fold 7-bit groups), a UTF-8 code unit, a base-N alphabet, or a JSON
  string body. Keep the description AST _closed and dumb_ (`byte`, `satisfy`, and the combinators `seq`/
  `alt`/`count`/`iso`); express every concrete format as a `Codec α` value so `decode base64` and
  `decode json` are literally the same `Codec.decode` call — only the codec changes. Do NOT add
  BE/LE/fixed-width/`varint`/`text`/tagged-`sum`/lookahead constructors to the core AST: those are
  _derived_ compositions (`count k byte` + an endianness `iso`) living in downstream packages.

- 2026-10-18 — **"every format is a `Codec α` value" breaks down for _variable-length_ formats:
  a finite `Codec` describes exactly one _fixed-shape_ value, and the only `Codec (List α)`
  producers are `count n p` (exactly `n`) and `manyUpTo n p` (at most `n`) — both _bounded_.**
  There is no unbounded-`many` constructor (`Codec` = `iso | seq | alt | empty | pure | byte |
satisfy`), because `decode` is a **total function** `List (α × Suffix n)`, not the paper's
  relation: a `many : Codec α → Codec (List α)` node is non-total for an empty-matching step
  (`many (pure ())` on `[]`), so repetition was deliberately pushed out of the AST into the
  `decodeRepeat`/`encodeRepeat`/`relRepeat` **triple** (each carrying a `ConsumesByte p`
  productivity witness; `takeWhile p` is the worked example). Consequence: a _whole-list_
  variable-length codec (`base16/base32/base64 : Codec (List UInt8)` over an arbitrary byte list)
  **cannot be a single finite `Codec` value** — `count 2 (satisfy isHex)` ≫ pair-iso gives one
  _byte_, not a list of them. The honest shapes are (a) a `Codec UInt8`/`Codec (List UInt8)` _leaf/block_
  value + a whole-list triple at the repetition layer, or (b) adding an indexed `many`
  constructor carrying `ConsumesByte p` — which means re-deriving every law over a
  productivity-indexed AST (a core change, not a downstream-composition change). Don't
  promise "`decode base64 == decode json == Codec.decode`" for the _whole-list_ case until the
  repetition layer can be a named value; for now only the _per-byte / per-block_ leaf is a `Codec`.

- 2026-10-18 — **Inject a Lake dependency into a Nix flake as a _local path_ dependency so the
  sandboxed `lake build` never `git clone`s it: rewrite `require foo from git "…"` → `require foo from
"./foo-src"` (path form resolves directly, no git/network) and `cp -r` the dependency source into the
  build dir first — a flake input's `.outPath` is a _read-only_ store snapshot, and Lake writes its `.lake`
  into the package dir, so without the copy you hit `permission denied (error code: 13) … .lake`. The
  dependency's own `lake-manifest.json` is gitignored (`No copy is made of local dependencies`), so Lake
  builds the dep from source in place — no pre-built `.olean` needed. (`substituteInPlace` in the buildPhase
  does the `require` rewrite; the source path is relative to the requiring package's dir.)
- 2026-10-18 — **A _private_ GitHub repo as a `github:` flake input is fetched _purely_ by a token, never
  `--impure`.** Anonymous fetch of a private `github:owner/repo` 404s (GitHub hides private repos from the
  API/archive endpoints), while `git clone https://github.com/owner/repo` succeeds _only_ via the macOS
  `osxkeychain` credential helper — that success is a misdirection, not proof the repo is public. The correct
  fix is `access-tokens = github.com=<token>` in `nix.conf` (or `nix --extra-access-tokens
"github.com=$(gh auth token)" …`): the shorthand fetches the private repo with no `--impure` and no
  `path:` workaround. `git+https://…`/`git+ssh://…` are not the answer — the former still needs the keychain
  (impure), the latter needs an SSH key that may not exist.

- 2026-10-18 — **A _block-structured_ encoder/decoder (fixed `k`-element blocks + variable-width
  padding tails, e.g. base32/64 with 5/3-byte blocks and 1/2/3/4-byte pad cases) cannot use plain
  `List` structural induction — its `ih` is on the _immediate_ cons tail while the block recursion
  skips `k` elements. Use strong induction on the length: `Nat.strongRecOn bs.length (motive := fun n =>
∀ ys, ys.length = n → …roundtrip ys…) (fun n ih ys hlen => …)`, giving `ih : ∀ m < n, motive m`; then after
  `rw [decodeN_block b b₁ … bₖ₋₁ … rest]`, recurse with `ih rest.length hlen' rest rfl` where the length
  shrink `hlen' : rest.length < n` is obtained by `rw [hlen] at (a have that rest.length < (cons…).length
proved with `simp only [List.length_cons]; omega`)** — `omega`alone cannot unfold`(x :: …).length`.**
The same shape mirrors at the `UInt8` surface: re-derive the strong induction there (don't transport it).
- 2026-10-18 — **`unfold decodeN` on a block-equal goal unfolds the _RHS_ recursive `decodeN` too,
  leaving a non-definitional residual; the fix is a standalone equational lemma `decodeN_consK (c₀ … cₖ₋₁)
(rest) : decodeN (c₀ :: … :: cₖ₋₁ :: rest) = <the `if`/`match` body>` proved by `rfl`, and `rw
[decodeN_consK]` to reduce only the LHS `k`-cons scrutinee.** (Base64 `k=4`, base32 `k=8`.) The
  `++` in `encodeN [b₀..bₖ₋₁] ++ encodeN rest` must first become a syntactic cons chain via `show … ++ …
= …` + `simp only [List.cons_append, List.nil_append]` (or `List.append_nil` for the `rest = []` whole-block
  case) before `rw [decodeN_consK]` finds the scrutinee.
- 2026-10-18 — **Order `rw` chains so each byte-extraction fact fires only after the vector it
  reconstructs is fully reduced to its encode-form.** A 5-char-to-byte fact like `((vₐ%r)·s + v/q) % r'·… + … = b₃`
  mentions `v₅`/`v₆` (the last two alphabet values), so you must `rw [valToX_valid v₅ h₅]`, `rw
[xToVal_valToX v₅ h₅]` (and the same for `v₆`) to turn them into their encode-form _before_ `rw
[hb₃]`; otherwise `rw` reports "did not find an occurrence" because the target still spells those
  sub-terms as the un-reduced alphabet values. Similarly, end each block lemma with a trailing `simp`
  (or `decide`) — not `rfl` — because the decoder's `if` guards leave `decide False || …`/`¬True` `&&`
  residue that `rfl` won't reduce but `simp`'s `Bool.not_true/false`/`Bool.false_and`/`decide_false` will.

- 2026-10-18 — **`UInt8` is `%256`-truncating in _both_ directions, and the clean `Nat`↔`UInt8`
  bridge is `UInt8.toNat_lt` (`n.toNat < 2^8`), `UInt8.ofNat_toNat` (`UInt8.ofNat x.toNat = x`),
  and `UInt8.toNat_ofNat'` (`(UInt8.ofNat n).toNat = n % 2^8`) — NOT `UInt8.toNat_ofNat`, which is
  only for the `OfNat.ofNat` spelling.** When a byte-level codec's alphabet is ASCII `< 256`, make
  the truncation vanish explicitly with `Nat.mod_eq_of_lt` (`rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt h]`
  where `h : c < 256`), so the `% 256` never leaks into the arithmetic goals. `UInt8.ofNat` unfolds to
  `{ toBitVec := BitVec.ofNat 8 n }`, not `OfNat.ofNat n`, which is why the `'`-primed lemma is the one
  that matches a `def toByte n := UInt8.ofNat n` surface.
- 2026-10-18 — **`omega` does NOT expand `if`/`ite` branches, and a stdlib-only project (no mathlib)
  has no `norm_num`/`nlinarith`/`ring`/`fin_cases`/`interval_cases` — so finite-alphabet bijections and
  closed-range arithmetic must be proved by `by_cases` on each range + `simp only […, ite_true,
ite_false]` + `omega`, never by letting `omega`/`simp` reduce a nested `if` chain on its own.**
  Three concrete patterns for a `valToX`/`xToVal` bijection over a 4-range alphabet: (a) per-range
  `by_cases` with the char as a single arithmetic expression (`65 + i`, `71 + i` instead of `97 + i - 26`),
  then `simp only [h, ite_true, ite_false]` + `omega`; (b) a "never the sentinel" fact (`isPad (valToX i)
= false`) closes with `exact decide_eq_false_iff_not.mpr (by omega)` after the same `by_cases` (the
  `Bool`/`decide` goal is a Prop-negation in disguise); (c) a final finite tail (`i = k ∨ i = k+1` from
  `¬ i ≤ k-1` and `i ≤ 63`) closes with `rcases (show i = k ∨ i = k+1 by omega) with rfl | rfl <;> decide`.
  `decide` is `[propext, Quot.sound]`-safe on closed `Decidable` goals; `native_decide` is NOT (it leaks
  `Lean.ofReduceBool`).
- 2026-10-18 — **A power-of-two bit/quartet-sum identity (`Σ (v / 2^k % r) * 2^k = v` for `v < 256`)
  is `omega`-provable — but only after `simp only [Nat.reducePow, Nat.reduceSub]` turns the symbolic
  `2^(7-i)` into a concrete `128`/`64`/…** With `bitAt v i := (v / 2^(7-i)) % 2`, `omega` alone leaves
  `2^(7-i)` as exponentiation and fails; `simp only [Nat.reducePow, Nat.reduceSub]` (evaluating `2^(7-0)`,
  `2^(7-1)`, … to literals) then `omega` closes it. The bound `v < 256` is load-bearing (makes each
  `v/2^k % 2` the actual bit); `omega` needs it stated via `have : v < 256 := …`/`UInt8.toNat_lt`.
  Same pattern for radix-4 (`(v / 4^(3-i)) % 4`).
- 2026-10-18 — **A `roundtrip` proved over a `Nat`-level core (`encodeN`/`decodeN : List Nat → …`)
  lifts to a `UInt8` surface by _re-deriving_ the induction with `toNat`/`ofNat` transparency at each
  step, not by a separate transport lemma — and `simp [encode, decode]` on the `UInt8` surface
  over-splits the decoder's `&&`/`if` into `true = true ∧ …` residue that obscures the `rw` target.**
  Write the `UInt8` decoder with a single `if cond₁ && cond₂ then …` (not nested `if cond₁ then if cond₂`),
  and drive the roundtrip with `rw`-chains (`toByte_valTo*`, `valTo*_valid`, `*ToVal_valTo*`, the digit-sum
  equality) rather than a big `simp`, finishing with one `omega`/`simp` on the reduced arithmetic.
  is proved cleanly via the _pointwise_ genuine-suffix invariant (`decode_genuine_suffix_pointwise`),
  not the `bdrop`-form: read each side at one `Fin` index, unpack one `bdrop`, `congr 1; apply Fin.ext;
dsimp; omega`, with `t.consumed = n - t.remaining` making equal `remaining` give equal `consumed`.**
  The tempting `bdrop_consumedAbs_eq` route instead rewrites the consumed count into a lemma whose
  _other_ hypothesis (`consumedAbs_remaining`-style, `a.size - consumedAbs = remaining`) is _dependent_
  on that count — `rw [hc] at E` then fails "motive is not type correct" because the count appears both
  in the `bdrop` index and inside the `congrArg Bytes` of the cast. Avoid rewriting a `Nat` into a term
  that mentions a dependent-equality hypothesis over that same `Nat`; reach for the pointwise invariant and
  close the one remaining `Fin`-index equality (a proof-irrelevance + `omega` step) instead.
- 2026-10-18 — **To turn "`t.prepend s₀₁ = t.prepend s₀₂`" into `s₀₁ = s₀₂` (injectivity of a
  length-indexed `splice`/`prepend` in its _prefix_), state and use three lemmas, not `simp`:**
  `splice_prefix_read (hm : m ≤ n) (s₁ : Bytes m) (s₂ : Bytes (n-m)) (i : Fin n) (hi : i.val < m) :
splice hm s₁ s₂ i = s₁ ⟨i.val, hi⟩` (unfold `splice_apply` → `concat` → `rw [cast_fin_symm (e := splice_add hm)]`
  → `dsimp` → `simp [hi]`); `prepend_prefix_read` (the same at `Suffix.prepend`, the prefix is `s₀` and `hi :
i.val < n - t.remaining`); and `prepend_prefix_eq t s₀₁ s₀₂ : t.prepend s₀₁ = t.prepend s₀₂ → s₀₁ = s₀₂`
  (apply `Bytes.ext; intro i`, `congrFun` the equality at `⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.sub_le n t.remaining)⟩`,
  then two `rw [prepend_prefix_read … i.isLt]`). The _same-type_ `prepend_prefix_eq` is the cast-free half:
  first prove `t₁ = t₂` (via `Suffix.ext` + the pointwise invariant) so `subst t₁` makes `s₀₁`/`s₀₂` share one
  type, then this lemma closes with no cross-length cast.
- 2026-10-18 — **An `@[extern]` trust seam whose Lean body is an `Array.extract`+`append` _composition_
  is NOT a window replacement on out-of-range inputs: `extract 0 off ++ src.extract s (s+len) ++
dst.extract (off+len) n` yields _variable-length_ results (appends `src` past `n` when `off > n`, drops
  bytes when `src` is short), while the C `memcpy`-into-full-`dst` returns exactly `n` bytes.** The two match
  only in-range; the body and the C drifted silently because the bench value-check exercised only mid-buffer
  inputs. Fix the _body_ to the clamped full-`dst` semantics (`dc := min off n`, `sc := min srcOff slen`,
  `lc := min len (min (n-dc) (slen-sc))`, result `dst[0,dc) ++ src[sc,sc+lc) ++ dst[dc+lc,n)`), which is `rfl`-spec-able
  _and_ matches a single-`memcpy` C; make the C's clamps **overflow-stable** (`copyLen > n - dstOff`, not
  `dstOff + copyLen > n`, since the Lean `Nat` never wraps but `size_t` can). Always add an out-of-range
  boundary value-check (empty source, `off` at/past end, `len` past end, `len = 0`) — it is the only check that
  catches a wrong clamp; a mid-buffer lane cannot.
- 2026-10-18 — **Proving a monotonicity/bound law for a definition is _not_ interchangeable with the
  "never overruns" bound you might want: an unconditional `decodeArray … → i ≤ c` (cursor never moves
  backward) is provable, but `c ≤ a.size` needs a `i ≤ a.size` precondition, because `pure x` returns
  `(x, i)` for _any_ `i` (a cursor already past the end is a legal result).** Before "fixing" a docstring that
  overclaims a bound, check the _base constructors_ (`pure`/`empty`) for the counterexample; the honest fix is
  either to reword to the proved fact or to state the bound _with_ the precondition and document why it is
  load-bearing (it is not a style choice — the unconditional form is false).

- 2026-10-18 — **Pure-Lean _parsing_ (not just bulk codecs) has a hard ~20-40x-off-C ceiling,
  and it is a _toolchain_ limit, not a code-quality one: `Nat`/`UInt8`/`UInt64` all box, and
  `USize` only unboxes as an `@[extern]` _argument_, never as a `Prod`/`Option` _field_.**
  Chasing a "very fast" RFC 3339 timestamp parser, three independent confirmations: (a) IR shows
  `acc*10+digit` lowers to `lean_nat_mul`/`lean_nat_add`/`lean_nat_sub` (bignum `lean_object*` calls) and
  byte loads to `lean_uint8_to_nat`; (b) a pure-Lean `sum64` `while` loop over `UInt64` lowers to
  `instAddUInt64`/`instMulUInt64`/`instLTUInt64` (boxed `lean_object*`) with **no** `uint64_t` anywhere;
  (c) rewriting the parser to a `USize` cursor made it _slower_ (~206→~440 ns) because `baGetU`'s
  `off.toNat < a.size` does a `USize→Nat` bignum conversion + `get_elem_tactic` proof per read and the
  `USize` field re-boxes (`lean_box_usize`). There is **no** pure-Lean escape: `@[implemented_by]`/
  `@[csimp]` still emit through the same boxed LCNF→EmitC pipeline; `native_decide`/`bv_decide` are
  `Prop`-reflection, not runtime `Nat` arithmetic. **Corrects §7 point 2** — "type it `USize` in source
  and get unboxed indices" is true only for an `@[extern]` _argument_, false once the value is _returned_
  in a product/option; a result-returning interpreter cannot stay unboxed this way.

  > **Partly superseded (reading note, not a retraction of the measurements).**
  > The measurements above stand. But the parenthetical at (b) — that
  > `instAddUInt64` proves `UInt64` arithmetic is boxed — is **wrong**: on 4.34
  > `def sum64 (n : UInt64) : UInt64 := n + 1` emits
  > `LEAN_EXPORT uint64_t l_sum64(uint64_t);` with `lean_uint64_add`, plus a
  > separate `l_sum64___boxed` for the polymorphic boundary. `UInt64` is the one
  > fixed-width type that stays scalar through arithmetic. §7 point 2 now states
  > this; see it for the corrected rule. The lesson that _survives_ is the
  > measured one: a `USize` **cursor** was slower, because a returned `USize`
  > re-boxes and `toNat` at each boundary is a bignum conversion.

  The `~20-40x C` figure in the paragraph below is **withdrawn** — `memcpy` is
  the wrong yardstick for a per-element parser, and the figure had no bench lane
  behind it. Quote measured ns/element against a measured pure-Lean floor
  instead.

- 2026-10-18 — **Benchmark numbers here are noisy by ±2x with machine load/thermal; cross-check
  against a `calib memcpy`/`memchr` baseline before believing any single `[measured]` figure, and do
  not micro-optimize against an unstable baseline.** A `calib memcpy` lane measured 66↔300 ns across
  runs on the _same_ binary (load average ~2.4), and a committed "302→206 ns improvement" was later
  revealed to be largely that noise (the reverted code re-measured 412 ns). Corollaries: (1) take the
  _best-of-N_ or check `uptime`/load before comparing two versions; (2) a "regression" vs "win" verdict
  needs the noisy baseline measured in the _same_ window, not recalled from an earlier session; (3) record
  the baseline value _in the result line_, never report a bare ns/op that the reader can't sanity-check.
- 2026-10-18 — **A `ByteArray`-vs-C comparison against a semantic parser must be apples-to-apples;
  C `strptime`/`date`-style parsing is ~10 ns/op on a 23-byte record, vs ~200-400 ns for the boxed
  pure-Lean equivalent.** When someone asks "can Lean parse as fast as C", the concrete answer is a
  head-to-head: a hand-written `clang -O2` RFC 3339 parser (uint32 registers, no alloc) is ~10 ns/op,
  and no pure-Lean reshaping gets under ~20x that because the per-digit `acc*10+d` is bignum-boxed.
  The honest framing is a _ratio to the same-machine C baseline_, not an absolute MiB/s number.
- 2026-10-17 — **A `Prod Nat USize` in `@[extern]` C is `lean_alloc_ctor(0, 2, 0)` with two
  _object_ fields — `Nat` via `lean_usize_to_nat`, `USize` via `lean_box_usize`; both box as
  objects (a `USize` is NOT a raw scalar once it is a field, only as an argument).** Returning
  `some (n : Nat, k : USize)` (the result of a varint/decimal seam): build the pair with
  `lean_alloc_ctor(0, 2, 0)`, `lean_ctor_set(pair, 0, lean_usize_to_nat(n))` (small-`Nat`
  immediate; `lean_unbox` on a bignum/mpz would be wrong, so document small-`Nat`-only), then
  `lean_ctor_set(pair, 1, lean_box_usize(k))`, then wrap in `some`'s tag-1 ctor
  `lean_alloc_ctor(1, 1, 0); lean_ctor_set(opt, 0, pair)`. The authoritative reference is the
  way the _Lean-generated_ C constructs the same type (in `.lake/build/ir/*.c`): the generator's
  `Prod`-of-`Nat`-and-`USize` is `lean_alloc_ctor(0,2,0)` with the `Nat` as `lean_usize_to_nat(…)`,
  not the `lean_alloc_ctor(0,1,sizeof(size_t))`+`lean_ctor_set_usize` you might guess from the
  scalar-argument lowering. (Generalizes the earlier `Option USize` entry: every _field_ whose
  runtime rep is an unboxed scalar is still re-boxed via `lean_box_*` when stored in a constructor.)
- 2026-10-17 — **`String` is a `Classical.choice`-leaky substrate for a proof gate: every
  accessor (`String.toList`, `.data`, `.get`, `.length`, `toNat?`) is `@[extern]` UTF-8-backed and
  leaks `Classical.choice`; a clean parser/reference over text must take raw `ByteArray`/`Array
UInt8` instead.** `#print axioms String.toList`/`String.data`/`String.get`/`String.length` all
  report `[propext, Classical.choice, Quot.sound]`, so a `String`-typed seam's Lean body (a spec
  pinned to `[propext, Quot.sound]`-only) cannot use any of them. `Array.get`/`Array.extract`/
  `ByteArray.mk`/`ByteArray.data`/`UInt8.toNat`/`Char.toNat` are axiom-clean (`[propext,
Quot.sound]`-only), so write the reference over bytes (e.g. an ASCII-decimal scanner folding
  `acc · 10 + (b.toNat - 48)`). `Char.isDigit`/`Char.ofNat` are also clean, but a `List Char` from
  `String.toList`/`.data` is not. Rule: text-processing seams that must stay in the axiom-clean
  gate take `ByteArray`, never `String`.
- 2026-10-17 — **A "committed" structural decoder (`Option`-threading `orElse` on `Alternative`,
  first-branch `bind` on `seq`) is NOT `= (backtracking decoder).head?` in general — the `seq`
  commitment is strictly stronger than "first result".** If `d₁`'s first result is a dead end for
  `d₂` (its `bind` yields `none`) but a _later_ `d₁` result succeeds, the committed `decodeOne (seq …)`
  returns `none` while `(decodeArray (seq …)).head?` skips the dead-end and returns the later
  result's pair. So the "committed result = first backtracking result" identity holds only for the
  `alt` node, not `seq`; the honest uncontradictable facts are (a) **soundness** — every committed
  result is a member of the backtracking list (provable by induction, `[propext, Quot.sound]`), and
  (b) the **gated** completeness — pair-level uniqueness (value+count) makes the committed decoder
  equal to the (unique) backtracking result. Do not assert the naive `head?`-equality; it is false,
  and the gate that makes the fast path sound is "backtracking result is unique", not "commit = first".

- 2026-10-17 — **The boxing of a scalar-payload `Option` (`Option USize`/`Option UInt64`) in
  hand-written `@[extern]` C is a _constructor with a scalar field_, not a small-int box — and
  getting it wrong only _appears_ to work, so value-check against the IR, never by reasoning.**
  Returning `some (v : USize)` from a `@[extern]` symbol is **not** `lean_box(v.toNat+1)` (that is the
  small-`Nat`/`Int` encoding) and **not** `lean_box_usize(v)` alone: the `Option` sum type is
  `none = lean_box(0)` (tag 0) and `some v` = a **tag-1 constructor object holding one _scalar_
  field** — allocate `lean_alloc_ctor(1, 1, 0)` (tag 1, `numObjs=0`, `scalarSize=1`) and set the field
  with `lean_ctor_set(r, 0, lean_box_usize(v))`. A `lean_box_usize(v)` returned bare has tag 0 and is
  read back as `none`; a `lean_box(v+1)` is a small-int box with the wrong scalar tag. The
  generated-code reference is authoritative: in the emitted `.c`, `some (off + i)` on a `USize` compiles
  to `lean_alloc_ctor(1,1,0); lean_ctor_set(_, 0, lean_box_usize(usize_add off i))`, and the _consumer_
  reads it as `lean_ctor_get(x,0)` → `lean_unbox_usize(...)`. Grep `.lake/build/ir/*.c` for how the same
  type is _constructed_ in Lean's own output and mirror it exactly; a semantically-right `memchr` with a
  wrong return-box ships garbage that only the byte-for-byte value check catches.

- 2026-10-17 — **Generalize a suffix `byteSlice` seam into `blitBytes` (buffer-to-buffer `memcpy`) and
  `findByte` (`memchr`); keep every seam `USize`-indexed and its Lean body the `Array` (not `ByteArray`)
  spelling so the spec law is `rfl`.** A `blitBytes dst dstOff src srcOff len` body is the
  `Array.extract`+`append` composition over `.data` (reducible; `blitBytes_spec` closes with **no axioms**
  at all), while the `findByte` body is `Array.findIdx?` over `Array.extract` of the suffix re-offset by
  `off` (`Array.findIdx?` returns a `Nat` relative to the extract, so add `off` to get the absolute `USize`;
  `findByte_spec` is `[propext]` from the `==`/`Bool` reflection in the predicate). Both C symbols are a
  single `memcpy`/`memchr`, clamps mirroring `Array.extract`'s truncation. The bench value-check compares
  the C result against the Lean body byte-for-byte (constructed from the _same_ `Array.extract`+`append`/
  `findIdx?` expression), never a length check, and a mid-buffer window/sentinel (not the prefix/suffix
  edge) is what actually catches a wrong offset/length/byte in the C.
- 2026-10-17 — **"Make the shipped C fast, make the pure spec slow" is the honest end-state, and it
  cuts the whole speed plan to two obligations.** When the _pure_ `Bytes`/`List` interpreter is
  accepted as a _specification_ (the denotation every law is proved against) rather than the run
  model, the perf question stops being "make the generic interpreter fast" — which is a dead end
  (a pure immutable value can't be built by `memcpy`; unboxed `UInt8` + scalar `USize` cursor +
  committed `|` choice are, respectively, trusted-only, proof-obstacle, and conditional-on-`Unambiguous`
  inside a `[propext, Quot.sound]`/zero-`sorry` gate). The plan reduces to exactly two layers:
  (a) **`@[extern]` C seams** (shape 2, elaborating body) for each irreducible raw-byte op — a
  generalized `blitBytes` (superset of a suffix `byteSlice`), a `memchr`/`findByte` scanner, a
  varint encode/decode-into-buffer, a `strtod`/numeric-parse, a zlib `deflate`/`inflate`; each is
  ~20 lines of C + a reducible Lean `def` whose body is the _spec_, matching the already-shipped
  `byteSlice` template; and (b) **per-format specialized decoders/encoders** (WAV header + one PCM
  `memcpy`, protobuf varint/tag loop + length-delimited blit, PNG zlib seam) each proved _equal to
  the generic spec once_ by `decodeArray_eq`-style refinement lemmas. The key realization that
  makes this sound: `@[extern]` only swaps the emitted C, so `#print axioms` sees the pure body
  regardless — the fast C is _invisible to the gate_, and the only new proof work is law-level
  (pure spec = pure seam body), never C-level. "No axiom" stays honest as "spec ≡ seam-body
  proven; seam-C trusted, bench-value-checked."

- 2026-10-17 — **An `@[extern]` trust seam with an elaborating body (shape 2) is _invisible to
  Lean's reduction_ — the trusted C is a runtime contract that can never appear in a law.
  `@[extern "sym"]` swaps only the _emitted_ C; the Lean `def` body still reduces under
  `simp`/`rfl`, so `#print axioms f` reports the _body's_ axioms (`[propext, Quot.sound]`-clean
  or none) **regardless** of what the C does — no Lean proof can even see the C symbol. Two
  consequences, both earned this session: (a) it is a **category error** to call a trust seam
  "the single unproven step of a law"; there is no such proof step — the trust lives in prose
  (F\*-vs-KaRaMeL posture: "declare the primitive, hand-write the C, name the seam"), orthogonal
  to the axiom gate. (b) To _prove_ `wrapper_spec` for a `wrapper b i := byteSlice b i`, you do
  **not** need the seam at all — you unfold the body; the only real proof obligation is whatever
  the _web_ of `Nat`/`USize` indices forces (see next entry). Preserving this distinction is what
  keeps "no axiom" from being misread as "no trust" and vice versa.

- 2026-10-17 — **The `Nat ↔ USize` roundtrip is the platform-fact leak — give the extern-adjacent
  wrapper a `USize` index, keep `Nat` _only_ on the proof/spec side.** Refines the earlier
  "keep the cursor on `Nat`" entry: split the decision in two. The _spec/cursor_ stays `Nat` (as
  before). But the _wrapper over an `@[extern]` whose C takes `USize`_ must itself be
  `USize`-indexed, or its refinement law inherits `(c.toUSize).toNat = c`, which needs
  `c < 2^System.Platform.numBits` — the exact unproven platform fact the repo refuses.
  Concretely: `f (b : ByteArray) (i : USize) : ByteArray := byteSlice b i` has `f b i =
ByteArray.mk (b.data.extract i.toNat b.data.size)` as an `rfl` (unfold `byteSlice`'s body;
  `(ByteArray.mk a).data = a` and the `.size` coincidence are `rfl`); a `Nat`-indexed variant
  would instead need `(i.toUSize).toNat = i`. The `Nat → USize` conversion is fine **at the call
  site** (where the caller holds the `Nat` cursor and does `c.toUSize` once); it must not be
  _baked into_ the wrapper's own sigma/index, or it poisons every lemma built on it.

- 2026-10-17 — **`USize` in an `@[extern]`'s _argument_ lowers to an unboxed `size_t` scalar;
  confirm it in the emitted IR, don't assert it.** `lean_byte_array_uset`'s C is
  `..._uset(lean_obj_arg, size_t, uint8_t)` — i.e. a `USize` parameter compiles to a raw `size_t`
  (`lean_unbox_usize` in the emitted wrapper), while `ByteArray` stays a borrowed `lean_object *`.
  This is the one place the "`USize` is a scalar" claim is _actually_ true (the carrier `Nat`
  cursor is NOT — it boxes to bignum, per the task-3.1 IR finding). Verify by grepping
  `.lake/build/ir/<Module>.c` for the symbol's declaration (`lean_object* sym(lean_object*, size_t)`)
  and the call site (`lean_unbox_usize`), never by assertion.

- 2026-10-17 — **How the genuine-suffix invariant actually closes (four exact tactics).**
  (Resolves the previous entry — the blocker is now proved.) (a) Prove the invariant
  **pointwise first** (`t.bytes i = s ⟨i.val + t.consumed, ·⟩` by induction on the description,
  with a shared `i.val + t.consumed < n` bound lemma), then **lift** to the `Bytes`-level
  `bdrop` form by `apply Bytes.ext; intro i; rw [cast_bytes_val' e …]` — the pointwise form
  has a clean `seq` induction (nested consumed counts close by `omega` over `sub_sub_add`),
  the `bdrop`/cast form does not. (b) **`subst e; simp` collapses "interpreter insensitive
  to a length cast"** (`decode d (cast (congrArg Bytes e) s) = (decode d s).map …`): the cast
  is along a `Nat` length equality, so `subst` reduces it to `rfl`; do **not** prove it by
  induction (the membership-bound spelling thrashes). (c) **`List.map_inj_left` threads the
  membership hypothesis** a pointwise-lemma needs: a `flatMap f l = flatMap g l` with the same
  `l` becomes `congrArg (·.flatten) (List.map_inj_left.mpr (fun a ha => …))`, and `ha : a ∈ l`
  is exactly the input a membership-parameterized lemma (`bdrop … = cast … t.bytes` for
  `(x,t) ∈ decode d s`) requires — bare `congr 1; funext` _loses_ `ha`. (d) **`rw [cast_cast]`
  closes composed length casts** via proof irrelevance: after bridging `bdrop (i+(n-t)) =
bdrop t ∘ bdrop i` and `t.bytes = cast … (bdrop t s)`, the remaining `cast e₁ (cast e₂ X)`
  equalities collapse by `rw [cast_cast]` (the `Nat` equality proofs are `Nat.eq_irrel`).

- 2026-10-17 — **A `Suffix`-returning spec vs a cursor-returning fast path refinement is
  blocked by `decode`'s own "genuine suffix" invariant, not by any general `Suffix` fact.**
  To equate `decodeArray d a (consumed c)` with `decode d t.bytes` (where `t : Suffix n` came
  from `decode d s`), the `seq` case needs `t.bytes = bdrop (n - t.remaining) s` — i.e. the
  fact that `decode` _returns genuine suffixes of its input_, `∀ (x, t) ∈ decode d s,
t.bytes = bdrop (n - t.remaining) s` (proved by induction on the description `d`). The
  tempting `bdrop c s = cast … t.bytes` equality is **false for an arbitrary `Suffix t`** — it
  only holds because `t` was _produced by `decode`_. So a two-level refinement (spec returns
  `Suffix`, fast path threads a consumed count) does **not** close by library-transport alone:
  you first prove the spec function's _own_ "suffix is a suffix" invariant, then compose the
  transport lemmas (`bdrop (i+m) = bdrop m ∘ bdrop i`, the cast-insensitive `.remaining`, the
  consumed-count transitivity). Discover the missing invariant and prove it before wiring the
  `seq`/`bind` case — otherwise you thrash on an unprovable arbitrary-`t` lemma.

- 2026-10-17 — **`List.foldl` over `ByteArray.push`/`Array.push` is proved via `.data`/
  `Array` projection, not by `simp` (which _loops_ on the recursion equation, and the `ByteArray`
  ops are FFI-opaque).** `ByteArray.push`, `ByteArray.empty`, `ByteArray.mk` do not unfold, but
  `(bs.push b).data = bs.data.push b` is `rfl`, and `ByteArray.ext : x.data = y.data → x = y`
  reduces a `ByteArray` goal to an `Array` goal. The projection lemma
  `(List.foldl (fun a b => a.push b) acc xs).data = List.foldl (fun a b => a.push b) acc.data xs`
  is proved by induction + `bpush_data` (axiom-free); the `Array`-level
  `List.foldl (fun a b => a.push b) acc xs = acc ++ xs.toArray` closes by `Array.ext'` +
  `Array.toList_append`/`toList_push` + `List.append_assoc` (`[propext, Quot.sound]`-only). Use
  `rw [List.foldl_cons, ih (acc.push b)]` (never `simp [foldlDef]`, which loops); `Array.toList_singleton`
  does not exist — `#[b].toList = [b]` is `rfl`/`dsimp`.

- 2026-10-17 — **An `Option`-returning refinement's `bind`/`map`/`orElse` skeleton bridges via a
  "`none`-iff" derived from the `map`-equality, not by `rw` on the bare scrutinee.** Proving
  `(f d x).map toList = (g d x).map ofFn` by induction, the `seq`/`alt` cases need to know
  `f d x = none ↔ g d x = none`; derive it once as `map_none_iff (h : (f d x).map p = (g d x).map q)`
  — `constructor <;> intro hne <;> cases the other option; rw [hne, the-other-cases-lem] at h;
simp only [Option.map] at h; cases h`. Then `cases ha : f d₁ x₁` and `rw [none_iff.mp/mpr ha]`
  to line up the `bind`/`orElse` structure (use `Option.orElse.eq_def` only via `simp only
[Option.orElse]` — bare `rw [Option.orElse]` fails). In the `some`/`some` leaf, extract the
  pointwise equalities with `Option.some.inj h` after `simp only [Option.map] at h`, and lift the
  leaf (`ofFn_concat`, `Array.toList_append`) with `congrArg some`.

- 2026-10-17 — **`Array.toList_ofFn`/`List.toArray_ofFn` round-trips leak `Classical.choice`;
  the clean encode readback is the List-level form `(·.toList)` vs `List.ofFn ∘ snd`, and the
  `Fin`-index head/`bdrop` reductions are `omega`- or `simp`-driven, not `rfl`.** `Array.ofFn` can't
  appear on the refinement RHS (`Array.toList_ofFn` is `[Classical.choice]`); instead prove
  `(encodeArray d x).map (fun a : Array UInt8 => a.toList) = (encode d x).map (fun e => List.ofFn e.2)`
  with the `seq` leaf `Array.toList_append` + `ofFn_concat` (both `[propext, Quot.sound]`). For a
  `byte`-style `bdrop i s ⟨0, h⟩ = s ⟨i, ·⟩` value equality, `unfold bdrop; congr 1; apply Fin.ext;
dsimp; omega` closes the `Fin`-proof-transparent goal (bare `rfl`/`congr` leaves `↑⟨↑⟨0, ⋯⟩+i, ⋯⟩`);
  and a `consumedAbs`-style `.remaining` identity needs `dsimp only [Suffix.drop]` (not `unfold`,
  which also breaks type-correct cast proof terms elsewhere in the goal) before `omega`.

- 2026-10-17 — **`USize` is a _proof_ obstacle even when it is the _right_ runtime scalar:
  its `+` is `Nat`-addition modulo `2^64` and its size is a platform fact — keep the spec/cursor
  on `Nat`, and treat `USize` as an IR-inspection question, not a refinement invariant.**
  `USize.toNat_add : (a + b).toNat = (a.toNat + b.toNat) % 2^64` and
  `USize.size = 2^64` (which needs the unprovable `System.Platform.numBits = 64`) mean a
  refinement law threading a `USize` cursor (`(x,c) ∈ f a i`) contracts the modulo into every
  step: `c.toNat` of `i+1` is `(i.toNat+1) % 2^64`, not `i.toNat+1`, so no induction closes
  `[propext, Quot.sound]`-only without an extra "the buffer is < 2^64" platform premise. The
  clean split: **`Nat` is the proof/runtime carrier** (same choice a `pushBytesFrom`/bignum-fold
  already makes); "does `USize` lower to `size_t`, no `lean_alloc`/box per node?" is answered
  by _inspecting the emitted `.c`_ (`size_t`, `lean_object *`), never by asserting it — if it
  does not, record that and mark the "scalar index" premise false rather than forcing a `USize`
  type that breaks the axiom gate. Decide the cursor's _type_ before writing the refinement,
  because it is a proof-budget decision, not a perf-tuning decision you can flip later.

- 2026-10-17 — **RESOLVED the `ofFn`-bridge `Classical.choice` leak: the _plain_ `Array`↔`List`
  primitives are axiom-free; only the `ofFn`-_specialized_ bridges leak.** Chasing a
  `Fin n → T`-carrier fast-path refinement that refused to close `[propext, Quot.sound]`-only,
  the clean/leaky split turned out to be sharper than "`List` clean, `Array` leaky": `Array.toList`,
  `List.toArray`, `Array.push`, `Array.append`, `Array.foldl`, and `Array.getElem_toList` are **all
  axiom-free** (`#print axioms` ⇒ none), and `List.append_toArray`/`Array.toList_append`/`Array.size_append`/
  `Array.append_assoc` are `[propext, Quot.sound]`; the leak lives **only** in `Array.getElem_ofFn`,
  `List.toArray_ofFn`, `Array.toList_ofFn`, and `List.getElem_ofFn`'s output (all `[Classical.choice]`).
  So a readback `xs[i] = f ⟨i,·⟩` must route through `Array.getElem_toList` (axiom-free) + a hand-proved
  clean `(List.ofFn f)[i] = f ⟨i, Nat.lt_of_lt_of_eq h List.length_ofFn⟩` (induct on `n`; `rfl` after the
  `Fin.succ` `rfl`), and substitute the list-level equality `arr.toList = List.ofFn s` **before** any
  `[i]` via `simpa only [h, List.length_ofFn]` — never `rw [h]` inside the `i < length` dependent motive.
  Also: bare `simp`/`simpa` the _whole_ way auto-fire classical lemmas; `simp only [hr, Option.map]` is
  needed even in base `none`/`nil` cases of an `Option`-returning accumulator (unfold `Option.bind`/`Option.map`
  explicitly so `none.bind`/`Option.map _ none` reduce).
- 2026-10-17 — **`Classical.choice` in refinement proofs leaks from _specific_ stdlib
  `GetElem` round-trips and from bare `simp` (not `simp only`) — bisect with minimal
  `#print axioms` repros, don't guess.** Proving `fastEncode p xs = encode p xs` over a
  `Fin n → T` carrier, three _surprising_ clean/leaky splits were pin-pointed: (1)
  `(List.ofFn s)[i.val]` (a pure `List` read at a `Fin` index) is `[propext]`-clean, but
  `(List.ofFn s).toArray.toList[i.val]` — the **same** term through a
  `List.toArray`/`Array.toList` round-trip — leaks `[Classical.choice]` **even for the
  trivial `x = x` `rfl`**. The `.toArray.toList` `[i.val]` re-enters the classical `GetElem`
  instance during elaboration; `Fin.cast`/`Nat.lt_of_lt_of_eq` transport is _not_ the culprit
  (both are `[propext]`/no-axioms). (2) bare `simp [X]` auto-fires other `[simp]` lemmas
  (classical ones included), while `simp only [X]` restricts to `X` — an
  `@[extern]`/`ByteArray`-adjacent equality that leaked as `simp [Array.toList_append, …]`
  closed `[propext, Quot.sound]`-clean as `simp only [Array.toList_append, …]`. (3)
  `rw [htoList]` rewriting a `toList` equality _inside_ a `[i.val]` access fails
  "motive is not type correct" — the `GetElem`'s `i < length` bound is a dependent motive on
  the rewritten length, so substitute the list equality _before_ applying `[i.val]` (via
  `funext`/`congrArg` on the list), never `rw` through the index. Also: `List.getElem_ofFn`
  is `[propext]`-clean **as a theorem** but its _output_ term carries a `by simp_all` index
  proof that leaks `Classical.choice` when `rw`'d — prove your own clean variant
  (`(List.ofFn f)[i] = f ⟨i, Nat.lt_of_lt_of_eq h List.length_ofFn⟩` by `induction n` +
  `Fin.foldr_succ`/`getElem_cons_zero`/`getElem_cons_succ`).
