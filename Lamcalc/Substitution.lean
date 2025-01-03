import Lamcalc.Weakening

inductive AgreeSubst : (Var -> Tm) -> Ctx -> Ctx -> Prop where
  | nil :
    AgreeSubst σ [] []
  | cons :
    Typed Γ a (.srt i) ->
    AgreeSubst σ Γ Γ' ->
    AgreeSubst (up σ) (a :: Γ) (a.[σ] :: Γ')
  | wk :
    Typed Γ' m  a.[σ] ->
    AgreeSubst σ Γ Γ' ->
    AgreeSubst (m .: σ) (a :: Γ) Γ'
  | conv :
    a === b ->
    Typed Γ' b.[shift].[σ] (.srt i) ->
    Typed Γ b (.srt i) ->
    AgreeSubst σ (a :: Γ) Γ' ->
    AgreeSubst σ (b :: Γ) Γ'
