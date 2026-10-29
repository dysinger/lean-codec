/-
# WORK IN PROGRESS — `decodeFullFastRoot = decodeFull` (tasks.md 6.1a)

This is a probe, not library code. Check it with:

    nix develop --command lake env lean \
      openspec/changes/codec-review-remediation/bridge-wip.lean

**Proven and `[propext, Quot.sound]`-clean (copy into `Codec/Decode.lean` as-is):**
  * `decodeFull_at_zero`   — `decodeFull` at a root numerically `0`
  * `decodeFull_succ'`     — `decodeFull`'s recursion equation at a succ root
  * `decodeFullStep_step`  — `decodeFullStep` over an attached cons
  * `attach_eq_cons`       — `attach` of a cons starts with that head
  * `attach_pair_eq`       — two heads of the same attached list are the same pair
  * `decodeFullFast_eq_core`'s statement, and `decodeFullFast.induct` cases 1
    (`n - m = 0`) and 2 (`decode` returns `[]`) closed completely.

**One `sorry` remains**, in `induct` case 3, at the reassembly commented in place:
the specification side reads `decodeFull h t.remaining t.bytes`, the induction
hypothesis reads `decodeFull h (n - m') (bdrop m' s)`, and connecting them needs
`decode_genuine_suffix` composed with `bdrop_bdrop` (a `bdrop`-composition lemma
re-rooting `bdrop (n - t.remaining) s` at `bdrop m' s`). See `tasks.md` 6.1a.
-/
import Codec
open Codec

theorem decodeFull_at_zero {α : Type} (p : Codec α) (h : ConsumesByte p) :
    ∀ (k : Nat) (t : Bytes k), k = 0 → decodeFull p h k t = some [] := by
  intro k t hk
  subst hk
  exact decodeFull_zero p h t

theorem decodeFull_succ' {α : Type} (p : Codec α) (h : ConsumesByte p)
    (k j : Nat) (hk : k = j + 1) (s : Bytes k) :
    decodeFull p h k s =
      decodeFullStep p h s (fun m s' _hm => decodeFull p h m s') (decode p s).attach := by
  subst hk
  rw [decodeFull, WellFounded.fix_eq]
  simp only [Nat.add_one]
  congr 2

theorem decodeFullStep_step {α : Type} (p : Codec α) (h : ConsumesByte p)
    {n : Nat} (s : Bytes n)
    (ih : (m : Nat) → (s' : Bytes m) → m < n → Option (List α))
    (x : α) (t : Suffix n) (hm : (x,t) ∈ p.decode s)
    (rest : List {pr : α × Suffix n // pr ∈ p.decode s}) :
    decodeFullStep p h s ih (⟨(x,t), hm⟩ :: rest) =
      (match ih t.remaining t.bytes (h x s t hm) with
       | none => decodeFullStep p h s ih rest
       | some xs => some (x :: xs)) := by
  rw [decodeFullStep]
  cases ih t.remaining t.bytes (h x s t hm) <;> rfl

/-- **The two step pairs agree.** Both the fast decoder's head `(x, t)` and the
specification's attached head `(x', t')` come from `decode` of the *same* byte
string, so they are the same pair. Stated with the candidate list as a
*parameter* (not derived from `.attach`), because rewriting `p.decode s` inside
a term whose type mentions `(x',t') ∈ p.decode s` fails on the dependent motive —
the same reason `decodeFullStep_some` inducts on the list rather than rewriting
under `.attach`. `[propext, Quot.sound]`-only. -/
theorem attach_pair_eq {α : Type} (n : Nat) :
    ∀ (d : List (α × Suffix n)) (x x' : α) (t t' : Suffix n)
      (h1 : (x,t) ∈ d) (h2 : (x',t') ∈ d)
      (l l' : List {y // y ∈ d}),
      d.attach = ⟨(x,t), h1⟩ :: l → d.attach = ⟨(x',t'), h2⟩ :: l' →
      x' = x ∧ t' = t := by
  intro d x x' t t' h1 h2 l l' e1 e2
  cases d with
  | nil => simp at h1
  | cons hd tl =>
      simp only [List.attach_cons, List.cons.injEq, Subtype.mk.injEq] at e1 e2
      have hpair : ((x,t) : α × Suffix n) = ((x',t') : α × Suffix n) := e1.1.symm.trans e2.1
      exact ⟨congrArg Prod.fst hpair.symm, congrArg Prod.snd hpair.symm⟩

/-- `attach` of a list known to be a cons starts with that cons's head. Stated
existentially, with the membership witness and the tail both produced, because
naming them before the `subst` is impossible and `rw` is blocked by the dependent
motive `_a.attach = …`. -/
theorem attach_eq_cons {α : Type} (n : Nat) :
    ∀ (d : List (α × Suffix n)) (x : α) (t : Suffix n) (rest : List (α × Suffix n)),
      d = (x, t) :: rest →
      ∃ (hm : (x,t) ∈ d) (l : List {y // y ∈ d}), d.attach = ⟨(x,t), hm⟩ :: l := by
  intro d x t rest _h
  subst _h
  exact ⟨List.mem_cons_self .., _, rfl⟩

theorem decodeFullFast_eq_core {α : Type} (p : Codec α) (h : ConsumesByte p) :
    ∀ (n : Nat) (s : Bytes n) (m : Nat) (acc : List α), m ≤ n →
      decodeFullFast p h s m acc =
        (decodeFull p h (n - m) (bdrop m s)).map (fun tail => acc.reverse ++ tail) := by
  intro n s m acc hmle
  revert hmle
  refine decodeFullFast.induct p h
    (motive := fun n s m acc => m ≤ n →
      decodeFullFast p h s m acc =
        (decodeFull p h (n - m) (bdrop m s)).map (fun tail => acc.reverse ++ tail)) ?_ ?_ ?_ n s m acc
  case refine_1 =>
    intro n m acc h0 s hmle
    have hm : m = n := Nat.le_antisymm hmle (Nat.sub_eq_zero_iff_le.mp h0)
    rw [decodeFullFast]
    split
    next => rw [hm, decodeFull_at_zero p h (n - n) (bdrop n s) (Nat.sub_self n)]; simp
    next k hk => omega
  case refine_2 =>
    intro n m acc j hj s hnil hmle
    rw [decodeFullFast]
    split
    next h0 =>
      -- `n - m = 0` and `n - m = j + 1` are contradictory
      rw [h0] at hj
      exact absurd hj (by omega)
    next k hk =>
      -- second `split`: the `match` on `decode`'s result
      rw [decodeFull_succ' p h (n - m) j hj]
      split
      next hz =>
        -- `decode` returned `[]`: its `.attach` is empty, and `decodeFullStep` of
        -- the empty candidate list is `none`.
        have hz2 : p.decode (bdrop m s) = [] := hz
        have hatt : (p.decode (bdrop m s)).attach = [] := by
          rw [hz2]; exact List.attach_nil
        rw [hatt, decodeFullStep]
        rfl
      next x t rest hx => rw [hnil] at hx; simp at hx
  case refine_3 =>
    intro n m acc j hj x s t rest hcons hmem ihrec IH
    -- both sides match on the same `decode` result: split *both* at once by
    -- recording the equation, then the goal is a plain `Option` equation
    rw [decodeFullFast]
    split
    next h0 =>
      -- `n - m = 0` and `n - m = j + 1` are contradictory
      rw [h0] at hj
      exact absurd hj (by omega)
    next k hk =>
      rw [decodeFull_succ' p h (n - m) j hj]
      have hhead : p.decode (bdrop m s) = (x, t) :: rest := hcons
      -- unfold `decodeFullStep` at the attached cons and reduce both sides to a
      -- single `match` on the recursive call
      rw [decodeFullStep.eq_def]
      intro _
      -- fast side: `decode` gives a cons, so the head branch is taken
      split
      next hx => rw [hx] at hcons; simp at hcons
      next x0 t0 r0 hx =>
      -- spec side: case on the attached list
      split
      · rename_i heqnil
        -- `(decode (bdrop m s)).attach = []`, but `decode` gives a cons
        have hne : ((x, t) :: rest).attach ≠ [] := by simp
        rw [hhead] at heqnil
        exact absurd heqnil hne
      · rename_i x' t' hp' lst' heqd
        -- `heqd : (decode (bdrop m s)).attach = ⟨(x',t'), hp'⟩ :: lst'`
        -- both heads come from `decode` of the same `Bytes`: they are the same pair
        -- `bdrop m s` and `(Suffix.drop m s).bytes` are the same `Bytes`, so the
        -- attached list is literally the cons from `hhead`
        obtain ⟨hmx, lx, e1⟩ := attach_eq_cons (n := (Suffix.drop m s).remaining)
          (p.decode (Suffix.drop m s).bytes) x t rest hcons
        have heqd' : (p.decode (Suffix.drop m s).bytes).attach =
            ⟨(x', t'), hp'⟩ :: lst' := heqd
        obtain ⟨hx', ht'⟩ := attach_pair_eq (n := (Suffix.drop m s).remaining)
          (p.decode (Suffix.drop m s).bytes) x x' t t' hmx hp' _ lst' e1 heqd'
        subst hx'
        subst ht'
        -- `hx` and `hcons` head the same decode, so the step suffixes agree
        have hpair : ((x0, t0) : α × _) = (x', t') := by
          have e2 := hcons
          rw [hx] at e2
          exact List.cons.inj e2 |>.1

        -- unify the specification's bound names with the fast side's
        have htt : t' = t0 := (congrArg Prod.snd hpair).symm
        have hxx : x' = x0 := (congrArg Prod.fst hpair).symm
        rw [hxx, htt]
        -- the only numeric fact needed: how far the cursor advanced
        have hrem : t0.remaining ≤ (Suffix.drop m s).remaining := t0.hle
        have hcursor : (m + (k + 1 - t0.remaining)) = m + (j + 1 - t0.remaining) := by
          omega
        rw [hcursor]
        -- `ihm` (the `have m' :=`) shadows the induction hypothesis; bind it first

        -- REMAINING: the specification side is
        --   decodeFull h t0.remaining t0.bytes
        -- while the induction hypothesis gives
        --   decodeFull h (n - m') (bdrop m' s),  m' = m + (j+1 - t0.remaining)
        -- These agree because `n - m' = t0.remaining` (omega, from `t0.hle`) and
        -- `t0.bytes = bdrop (n - t0.remaining) s` — but with the `bdrop` re-rooted
        -- at `s`, that is *exactly* `decode_genuine_suffix`'s conclusion, which is
        -- stated for `n - t.remaining` from the root `s`, not for `m'`. Bridging
        -- the two needs `Suffix.drop`'s `remaining` (`(Suffix.drop m s).remaining
        -- = n - m`, definitional) composed with `bdrop_bdrop` — i.e. one more
        -- `bdrop`-composition lemma, then this case closes.
        cases hd : decodeFull p h t0.remaining t0.bytes with
        | none =>
            -- the fast side's recursive call is also `none` (IH, at `t'.remaining`)
            have : ihrec ≤ n := by
              have h0 := t0.hle; simp only [Suffix.drop] at h0; omega
            have IH' : p.decodeFullFast h s (m + (j + 1 - t0.remaining)) (x0 :: acc) =
                Option.map (fun tail => (x0 :: acc).reverse ++ tail)
                  (p.decodeFull h (n - (m + (j + 1 - t0.remaining))) (bdrop (m + (j + 1 - t0.remaining)) s)) :=
              IH this
            rw [IH', hd]
            rfl
        | some ys =>
            have : ihrec ≤ n := by
              have h0 := t0.hle; simp only [Suffix.drop] at h0; omega
            have IH' : p.decodeFullFast h s (m + (j + 1 - t0.remaining)) (x0 :: acc) =
                Option.map (fun tail => (x0 :: acc).reverse ++ tail)
                  (p.decodeFull h (n - (m + (j + 1 - t0.remaining))) (bdrop (m + (j + 1 - t0.remaining)) s)) :=
              IH this
            rw [IH', hd]
            simp
            sorry

end Codec
