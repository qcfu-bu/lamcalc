import Lamcalc.Substitution
open ARS

theorem Typed.pi_inv :
    Typed Γ (.pi a b) c ->
    ∃ i j, Typed (a :: Γ) b (.srt i) ∧ c === .srt j := by
  generalize e: Tm.pi a b = m
  intro ty
  induction ty using Typed.rec (motive_2 := fun _ _ => True)
  generalizing a b
  all_goals try trivial
  case pi i _ j _ _ _ _ =>
    cases e
    exists j, (max i j)
    constructor
    . assumption
    . constructor
  case conv eq1 _ _ ih _ =>
    have ⟨i, j, tyb, eq2⟩ := ih e
    exists i, j
    constructor
    . assumption
    . apply Conv.trans
      apply Conv.sym eq1
      apply eq2
