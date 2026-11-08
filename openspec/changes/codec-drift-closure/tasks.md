# Tasks — `codec-drift-closure`

> **START HERE — read this before task 1.**
>
> **Status at hand-off:** authored and validating; **nothing implemented**. Zero tasks
> checked, and that is correct.
>
> **This change closes round nine's residue and attacks the one defect class the gate
> arms cannot see.** Round nine's own five-pass review ended its gate axis with _"NO
> FURTHER MUSTS FOUND"_ and its prose axis with _six_ findings, five of which share one
> shape: **a claim whose stated method is not its code's method.** Read
> `openspec/changes/codec-audit-round-nine/reviews/round-ten.md` before starting — it is
> the evidence base, in-repo, with every finding id resolvable.
>
> **Group A is blocked on the host, not on the work.** The re-run needs an idle machine.
> The owner deferred it once (`codec-audit-round-nine` tasks 2.1/2.3); **if the host is
> loaded again, do Group B/C/D and leave Group A open — do not restamp from a loaded
> run.** The reasoning is in `design.md` D1 and is not re-litigated here.
>
> **`basen-uppercase-prepass` and `basen-nat-iso` are PARKED by the owner.** Not in
> scope. Do not start them.
>
> Legend: **[M]** MUST, **[S]** SHOULD, **[N]** NITPICK.

## 0. Preconditions

- [ ] 0.1 Confirm the tree is clean and every gate is green **before** any edit:
      `git status --porcelain` empty, then `lake build`, `openspec validate --all`,
      `checks.formatting`, `checks.reviews`, `checks.mirror`, `checks.bench`. Record the
      numbers this session actually sees — **do not copy the block below**: it is
      `codec-audit-round-nine`'s closing state, not this change's starting state.
- [ ] 0.2 Re-read `AGENTS.md`'s "Pause signal" and play the alarm on every pause.
- [ ] 0.3 **Read `design.md` D2/D3 before writing an arm.** Both groups have a
      "prefer this mechanism, fall back to that" decision that is meant to be settled by
      measurement, not by preference.
- [ ] 0.4 **Do not** `git stash` / `git reset` / `git checkout -- <file>`. Commit per
      group.

## 1. [M] Group A — the benchmark re-run and the restamp

Findings: `codec-audit-round-nine` 2.1, 2.3, and `P4-N3` (the open range).

- [ ] 1.1 Confirm the host is **idle** before running anything: `uptime` and
      `ps -A -o %cpu,comm -r | head -5`, recorded in the commit message. If load is
      above ~1 per 4 cores, or the top consumer is not this session, **stop and do
      Group B instead**; leave 1.1–1.6 open with a note saying why.
- [ ] 1.2 `lake build bench`, then two runs of `.lake/build/bin/bench 4096 4096`. Save
      both logs. Do not run anything else concurrently.
- [ ] 1.3 Re-derive **every** cell with `python3` from the printed `ns` and
      `steps/burst` — not by eye, and not from `codec-audit-round-nine`'s recipe copied:
      read the span the lane prints (`512` for the window rows, `4096` otherwise).
- [ ] 1.4 Derive **every** interval twice — once from the medians (which is what this
      document quotes) and once from the full cell range — and state which is which. The
      padded-range defect has fired four times; the defence is to derive both and say
      which one the sentence is.
- [ ] 1.5 Update the three performance tables and **move the vintage stamp**. Delete the
      old medians; do not caveat them.
- [ ] 1.6 Close `P4-N3`: the `26.97–28.56` cross-table splice is replaced by whatever
      the run produces, and the sentence that made the claim is re-read against it.

## 2. [M] Group B — numbers become generated or deleted

Findings: the header-cell (`769` vs `427`) confusion, the stale gate-output block, and
the four padded ranges.

- [ ] 2.1 **Decide the mechanism for the generated gate-output block by trying both**
      (`design.md` D2): (a) a marked region + generator, (b) a check that regenerates
      and diffs. Prefer (b). Record which worked and what broke.
- [ ] 2.2 Implement it so that the README's quoted block cannot drift from the gate.
      Mutation-test: change one asserted count in `Axioms.lean` without regenerating, and
      confirm the build fails **naming the block**.
- [ ] 2.3 Audit every remaining hand-written count in `Axioms.lean`'s header, `README`'s
      law/table prose, and `flake.nix`. For each, choose **generate**, **assert**, or
      **delete in favour of a pointer**. List them in this file with the choice, because
      the list is the completeness claim.
- [ ] 2.4 Apply the same to `AGENTS.md`. It is full of numbers ("13 gate lines", "65–67
      ns/call"). Either they are generated, or they are pointers to the file that holds
      the authority, or — where `AGENTS.md` is deliberately a _lessons_ document — they
      are deleted and replaced by the rule.

## 3. [M] Group C — the "method sentence" audit

Findings: the five stated-method defects (`round-ten.md`: scope word, ordering,
comparison, path, and the census-vs-partition cell).

- [ ] 3.1 Build the **enumeration** of method sentences by command (`design.md` D3
      step 1), and **report the denominator**: how many comment/prose lines were scanned
      and how many matched. An audit whose vocabulary is silent about its own coverage is
      §5.3a one level up.
- [ ] 3.2 For each candidate, classify: **assertable property** / **scope claim** /
      **unassertable**. Record the count of each — again, a denominator.
- [ ] 3.3 For every **assertable property**, add an effect-level assertion (the
      `classifyFootprintClaim` pattern), and mutation-test it by breaking the property.
- [ ] 3.4 For every **scope claim**, assert the scope from the environment the check
      walks, or delete the scope word. A `grep -rn … <dir>` in a comment is a scope claim
      and its path is part of it.
- [ ] 3.5 For every **unassertable** one, record the reason in place. Do not leave a
      method sentence that is merely believed.

## 4. [S] Group D — round nine's residue

- [ ] 4.1 Re-read `codec-audit-round-nine/tasks.md` for any box still open that this
      change's groups do not close, and either close it or record why it stays open.
- [ ] 4.2 Update `codec-audit-round-nine/reviews/round-ten.md` if any finding id moves.
      `checks.reviews` reconciles the ids in **both** directions, so a stale row is a
      build failure — the file must stay true.
- [ ] 4.3 **Archive-ordering check** (`design.md` D5): `codec-audit-round-nine` archives
      **first**, because both changes modify the same two `codec/axiom-gate`
      requirements. Before syncing this delta, re-run the scenario-count comparison
      against the then-live spec and record it here. Do not trust D5's authoring-time
      numbers.

## 5. [S] Gates and docs

- [ ] 5.1 `lake build` — record the line count and every asserted count.
- [ ] 5.2 `openspec validate --all`.
- [ ] 5.3 `checks.formatting` (treefmt + sandboxed prettier — **not** `nix fmt`, and note
      that `--clear-cache` is not a flag this `nix` accepts; use
      `--no-link --print-build-logs`).
- [ ] 5.4 `checks.reviews`, `checks.mirror`, and the new generator check from 2.2.
- [ ] 5.5 `checks.bench` — builds **and runs**; note it needs `lean4` + `stdenv.cc`, not
      just `git`, and `set -euo pipefail`, or its greps cannot fail the build.
- [ ] 5.6 `checks.lean` sandboxed, detached with `nohup`, polled.
- [ ] 5.7 Spot-check `#print axioms` on anything this change touches. Expect
      `[propext, Quot.sound]` or empty, never `Classical.choice`.
- [ ] 5.8 `CHANGELOG.md` — one entry in the register of a **correction**, and
      `AGENTS.md`'s lessons section gains the two new shapes (**padded range**,
      **scope word**).

## 6. Recorded, deliberately not in this change

- [ ] 6.1 A tenth review round. This change closes the ninth's residue; it does not
      commission another.
- [ ] 6.2 `basen-nat-iso` and `basen-uppercase-prepass` — PARKED by the owner pending
      the library-division decision. Do not touch.
- [ ] 6.3 Cross-repo (`lean-basen`) consistency — out of scope by owner instruction.
