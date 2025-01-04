import Lamcalc.Renaming

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
  induction wf
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
      . apply Conv.subst (Conv.subst eq)
      . apply ih; assumption; constructor
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

theorem Typed.substitution :
    Typed Γ m a -> AgreeSubst σ Γ Γ' -> Typed Γ' m.[σ] a.[σ] := by
  intro ty
  induction ty
  using Typed.rec (motive_2 := fun Γ _ => ∀ Γ' σ, AgreeSubst σ Γ Γ' -> Wf Γ')
  generalizing Γ' σ with
  | srt wf ih =>
    intro agr; asimp
    constructor
    apply ih; assumption
  | var _ _ ih =>
    intro agr; asimp
    apply AgreeSubst.has
    . assumption
    . apply ih; assumption
    . assumption
  | pi tya tyb iha ihb =>
    intro agr; asimp
    constructor
    . apply iha; assumption
    . apply ihb; constructor <;> assumption
  | lam tya tym iha ihm =>
    intro agr; asimp
    constructor
    . apply iha; assumption
    . apply ihm;
      constructor <;> assumption
  | app tym tyn ihm ihn =>
    intro agr; asimp
    replace ihm := ihm agr; asimp at ihm
    replace ihn := ihn agr
    have ty := Typed.app ihm ihn
    asimp at ty
    assumption
  | conv eq tym tyb ihm ihb =>
    intro agr
    apply Typed.conv
    . apply Conv.subst eq
    . apply ihm; assumption
    . apply ihb; assumption
  | nil _ _ agr =>
    cases agr; constructor
  | @cons _ _ i wf ty ih1 ih2 Γ' σ agr =>
    apply AgreeSubst.wf_cons
    . exact agr
    . exact ty.wf
    . exact ih1
    . intros; exists i
      apply ih2; assumption

theorem Typed.subst :
    Typed (a :: Γ) m b ->
    Typed Γ n a ->
    Typed Γ m.[n/] b.[n/] := by
  intro tym tyn
  apply Typed.substitution
  . assumption
  . apply AgreeSubst.wk
    asimp; assumption
    exact AgreeSubst.rfl tyn.wf

theorem Typed.esubst :
    m' = m.[n/] ->
    b' = b.[n/] ->
    Typed (a :: Γ) m b ->
    Typed Γ n a ->
    Typed Γ m' b' := by
  intros
  subst_vars
  apply Typed.subst <;> assumption

theorem Typed.conv_ctx :
    b === a ->
    Typed Γ b (.srt i) ->
    Typed (a :: Γ) m c ->
    Typed (b :: Γ) m c := by
  intro eq tyb tym
  replace tym : Typed (b :: Γ) m.[ids] c.[ids] := by
    have wf := tym.wf
    cases wf; case cons wf tya =>
    apply Typed.substitution
    . assumption
    . apply AgreeSubst.conv <;> try assumption
      . asimp
        apply Typed.eweaken <;> try first | rfl | assumption
        asimp
      . apply AgreeSubst.rfl <;> constructor <;>
        assumption
  asimp at tym
  exact tym
