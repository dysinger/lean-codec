import Codec
open Codec

theorem decodeFull_at_zero {α : Type} (p : Codec α) (h : ConsumesByte p) :
    ∀ (k : Nat) (t : Bytes k), k = 0 → decodeFull p h k t = some [] := by
  intro k t hk; subst hk; exact decodeFull_zero p h t

theorem decodeFull_succ' {α : Type} (p : Codec α) (h : ConsumesByte p)
    (k j : Nat) (hk : k = j + 1) (s : Bytes k) :
    decodeFull p h k s =
      decodeFullStep p h s (fun m s' _hm => decodeFull p h m s') (decode p s).attach := by
  subst hk; rw [decodeFull, WellFounded.fix_eq]; simp only [Nat.add_one]; congr 2

theorem decodeFull_step_att {α : Type} (p : Codec α) (h : ConsumesByte p)
    {n : Nat} (s : Bytes n)
    (ih : (m : Nat) → (s' : Bytes m) → m < n → Option (List α))
    (x : α) (t : Suffix n) (hm : (x,t) ∈ p.decode s)
    (rest : List {pr : α × Suffix n // pr ∈ p.decode s}) :
    decodeFullStep p h s ih (⟨(x,t), hm⟩ :: rest) =
      (match ih t.remaining t.bytes (h x s t hm) with
       | none => decodeFullStep p h s ih rest
       | some xs => some (x :: xs)) := by
  rw [decodeFullStep]; cases ih t.remaining t.bytes (h x s t hm) <;> rfl

theorem attach_eq_cons {α : Type} (n : Nat) :
    ∀ (d : List (α × Suffix n)) (x : α) (t : Suffix n) (rest : List (α × Suffix n)),
      d = (x, t) :: rest →
      ∃ (hm : (x,t) ∈ d) (l : List {y // y ∈ d}), d.attach = ⟨(x,t), hm⟩ :: l := by
  intro d x t rest _h; subst _h; exact ⟨List.mem_cons_self .., _, rfl⟩

theorem attach_pair_eq {α : Type} (n : Nat) :
    ∀ (d : List (α × Suffix n)) (x x' : α) (t t' : Suffix n)
      (h1 : (x,t) ∈ d) (h2 : (x',t') ∈ d) (l l' : List {y // y ∈ d}),
      d.attach = ⟨(x,t), h1⟩ :: l → d.attach = ⟨(x',t'), h2⟩ :: l' → x' = x ∧ t' = t := by
  intro d x x' t t' h1 h2 l l' e1 e2
  cases d with
  | nil => simp at h1
  | cons hd tl =>
      simp only [List.attach_cons, List.cons.injEq, Subtype.mk.injEq] at e1 e2
      have hpair : ((x,t) : α × Suffix n) = ((x',t') : α × Suffix n) := e1.1.symm.trans e2.1
      exact ⟨congrArg Prod.fst hpair.symm, congrArg Prod.snd hpair.symm⟩

theorem decodeFullFast_eq_core {α : Type} (p : Codec α) (h : ConsumesByte p) :
    ∀ (n : Nat) (s : Bytes n) (m : Nat) (acc : List α), m ≤ n →
      decodeFullFast p h s m acc =
        (decodeFull p h (Suffix.drop m s).remaining (Suffix.drop m s).bytes).map
          (fun tail => acc.reverse ++ tail) := by
  intro n s m acc hmle
  revert hmle
  refine decodeFullFast.induct p h
    (motive := fun n s m acc => m ≤ n →
      decodeFullFast p h s m acc =
        (decodeFull p h (Suffix.drop m s).remaining (Suffix.drop m s).bytes).map
          (fun tail => acc.reverse ++ tail)) ?_ ?_ ?_ n s m acc
  case refine_1 =>
    intro n m acc h0 s hmle
    have hm : m = n := Nat.le_antisymm hmle (Nat.sub_eq_zero_iff_le.mp h0)
    rw [decodeFullFast]
    split
    next =>
      rw [hm]
      rw [decodeFull_at_zero p h (Suffix.drop n s).remaining (Suffix.drop n s).bytes
            (by simp [Suffix.drop])]
      simp
    next k hk => rw [hk] at h0; omega
  case refine_2 =>
    intro n m acc j hj s hnil hmle
    rw [decodeFullFast]
    split
    next h0 => rw [h0] at hj; omega
    next k hk =>
      -- the fast side's `match` on a `nil` decode is `none`, definitionally
      simp only [hnil]
      -- the spec side: `decodeFull` at a succ root, whose attached list is empty
      have hk' : (Suffix.drop m s).remaining = j + 1 := by
        have := hj; simp only [Suffix.drop] at this ⊢; omega
      conv => rhs; rw [decodeFull_succ' p h ((Suffix.drop m s).remaining) j hk']
      split
      next hz =>
        -- both sides are `none` at the empty candidate list
        have hatt : (p.decode (Suffix.drop m s).bytes).attach = [] := by
          rw [hz]; exact List.attach_nil
        rw [hatt, decodeFullStep]
  case refine_3 =>
    intro n m acc j hj x s t rest hcons hmem ihrec IH hmle
    rw [decodeFullFast]
    split
    next h0 => rw [h0] at hj; omega
    next k hk =>
      sorry
