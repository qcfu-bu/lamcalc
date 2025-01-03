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
    Typed Γ b (.srt i) ->
    Typed Γ' b.[ren .succ].[σ] (.srt i) ->
    AgreeSubst σ (a :: Γ) Γ' ->
    AgreeSubst σ (b :: Γ) Γ'

theorem AgreeSubst.rfl : Wf Γ -> AgreeSubst ids Γ Γ := by
  intro wf
  induction wf using Wf.rec (motive_1 := fun _ _ _  _ => True)
  all_goals try trivial
  case nil =>
    constructor
  case cons ty agr _ =>
    replace agr := AgreeSubst.cons ty agr
    asimp at agr
    assumption

theorem AgreeSubst.has :
    AgreeSubst σ Γ Γ' -> Wf Γ' -> Has Γ x a -> Typed Γ' (σ x) a.[σ]  := by
  intro agr
  induction agr generalizing x a with
  | nil => intro _ hs; cases hs
  | @cons _ a _ σ _ ty agr ih =>
    intro wf hs
    cases wf; case cons wf ty =>
    cases hs with
    | zero =>
      asimp
      constructor
      . constructor <;> assumption
      . have : a.[σ >> ren .succ] = a.[σ].[ren .succ] := by asimp
        rw[this]; constructor
    | @succ _ _ a _ hs =>
      asimp
      have : a.[σ >> ren .succ] = a.[σ].[ren .succ] := by asimp
      rw[this]; clear this
      apply Typed.eweaken <;> try first | rfl | assumption
      apply ih <;> assumption
  | wk ty agr ih  =>
    intro wf hs
    cases hs with
    | zero => asimp; assumption
    | succ => asimp; apply ih <;> assumption
  | @conv a b _ _ _ σ eq ty ty' agr ih =>
    intro wf hs
    cases hs with
    | zero =>
      apply Typed.conv
      . apply Conv.subst
        apply Conv.subst
        exact eq
      . apply ih
        assumption
        constructor
      . assumption
    | succ =>
      apply ih
      . assumption
      . constructor; assumption

theorem AgreeSubst.wf_nil : AgreeSubst σ [] Γ -> Wf Γ := by
  intro agr
  cases agr with
  | nil => constructor

theorem AgreeSubst.wf_cons :
    AgreeSubst σ (a :: Γ) Γ' -> Wf Γ ->
    (∀ Γ' σ, AgreeSubst σ Γ Γ' -> Wf Γ') ->
    (∀ Γ' σ, AgreeSubst σ Γ Γ' -> ∃ i, Typed Γ' a.[σ] (.srt i)) ->
    Wf Γ' := by
  intro agr
  cases agr with
  | cons _ agr =>
    intro _ h1 h2
    have wf := h1 _ _ agr
    have ⟨_, ty⟩ := h2 _ _ agr
    constructor
    . apply h1; assumption
    . exact ty
  | wk =>
    intro _ h1 h2
    apply h1; assumption
  | conv _ _ ty' =>
    intro wf h1 h2
    apply ty'.wf
