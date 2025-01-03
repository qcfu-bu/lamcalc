import Lamcalc.Syntax

abbrev Ctx := List Tm

inductive Has : Ctx -> Var -> Tm -> Prop where
  | zero :
    Has (a :: Γ) 0 a.[shift]
  | succ :
    Has Γ x a ->
    Has (b :: Γ) x.succ a.[shift]

theorem has_sized : Has Γ x a -> x < Γ.length := by
  intro h
  induction h with
  | zero => simp
  | succ => simp; assumption
