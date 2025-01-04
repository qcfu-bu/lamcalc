import Lamcalc.Typed

inductive AgreeRen : (Var -> Var) -> Ctx -> Ctx -> Prop where
  | nil :
    AgreeRen ξ  [] []
  | cons :
    Typed Γ a (Tm.srt i) ->
    AgreeRen ξ Γ Γ' ->
    AgreeRen (upren ξ) (a :: Γ) (a.[ren ξ] :: Γ')
  | wk :
    Typed Γ' a (Tm.srt i) ->
    AgreeRen ξ Γ Γ' ->
    AgreeRen (ξ !>> .succ) Γ (a :: Γ')

theorem AgreeRen.rfl : Wf Γ -> AgreeRen id Γ Γ := by
  intro wf
  induction wf
  all_goals try trivial
  case nil => constructor
  case cons Γ a i ty ih _ =>
    have h := AgreeRen.cons ty ih
    asimp at h
    assumption

theorem AgreeRen.has :
    AgreeRen ξ Γ Γ' -> Has Γ x a -> Has Γ' (ξ x) a.[ren ξ] := by
  intro agr
  induction agr generalizing x a with
  | nil => intro h; cases h
  | @cons _ a _ ξ _ _ _ ih =>
    intro h
    cases h <;> asimp
    case zero =>
      have : a.[@ren Tm _ ξ >> ren .succ] = a.[ren ξ].[ren .succ] := by asimp
      rw[this]; constructor
    case succ x a hs =>
      have : a.[@ren Tm _ ξ >> ren .succ] = a.[ren ξ].[ren .succ] := by asimp
      rw[this]; constructor
      apply ih; assumption
  | @wk _ a _ ξ _ _ _ ih =>
    intro h; asimp
    have : a.[@ren Tm _ (ξ !>> .succ)] = a.[ren ξ].[ren .succ] := by asimp; rfl
    rw[this]; constructor
    apply ih; assumption

theorem AgreeRen.wf_nil : AgreeRen ξ [] Γ' -> Wf Γ' := by
  intro agr
  cases agr with
  | nil => constructor
  | wk ty agr =>
    constructor
    . apply ty.wf
    . assumption

theorem AgreeRen.wf_cons :
    AgreeRen ξ (a :: Γ) Γ' -> Wf Γ ->
    (∀ Γ' ξ, AgreeRen ξ Γ Γ' → Wf Γ') ->
    (∀ Γ' ξ, AgreeRen ξ Γ Γ' → ∃ i, Typed Γ' a.[ren ξ] (.srt i)) ->
    Wf Γ' := by
  intro agr
  cases agr with
  | cons ty agr =>
    intro wf h1 h2
    have ⟨i, ty⟩ := h2 _ _ agr
    constructor
    . apply h1; assumption
    . assumption
  | wk ty agr =>
    intros
    constructor
    . exact ty.wf
    . assumption

theorem Typed.renaming :
    Typed Γ m A -> AgreeRen ξ Γ Γ' -> Typed Γ' m.[ren ξ] A.[ren ξ] := by
  intro ty
  induction ty
  using Typed.rec (motive_2 := fun Γ _ => ∀ Γ' ξ, AgreeRen ξ Γ Γ' -> Wf Γ')
  generalizing Γ' ξ with
  | srt wf ih =>
    intro; asimp; constructor
    apply ih; assumption
  | var wf hs ih =>
    intro; asimp; constructor
    . apply ih; assumption
    . apply AgreeRen.has <;> assumption
  | pi tya tyb iha ihb =>
    intro agr; asimp; constructor
    . apply iha; assumption
    . have ty := ihb (AgreeRen.cons tya agr)
      asimp at ty; assumption
  | lam tya tym iha ihm =>
    intro agr; asimp; constructor
    . apply iha; assumption
    . have ty := ihm (AgreeRen.cons tya agr)
      asimp at ty; assumption
  | @app _ m a b n tym tyn ihm ihn =>
    intro agr; asimp
    replace tym := ihm agr; asimp at tym
    replace tyn := ihn agr; asimp at tyn
    have ty := Typed.app tym tyn; asimp at ty
    assumption
  | conv eq tym tyb iha ihb =>
    intro agr
    apply Typed.conv
    . apply Conv.subst; assumption
    . apply iha; assumption
    . asimp at ihb; apply ihb; assumption
  | nil Γ' ξ agr =>
    exact agr.wf_nil
  | @cons _ _ i _ _ _ ih _ _ agr =>
    apply agr.wf_cons
    . assumption
    . assumption
    . intros
      exists i
      apply ih; assumption

theorem Wf.has_typed : Wf Γ -> Has Γ x a -> ∃ i, Typed Γ a (.srt i) := by
  intro wf
  induction wf
  generalizing x a
  all_goals try trivial
  case nil => intro h; cases h
  case cons _ i wf ty ih _ =>
    intro h
    cases h with
    | zero =>
      exists i
      apply ty.renaming
      constructor
      . assumption
      . exact AgreeRen.rfl wf
    | succ hs =>
      have ⟨i, ty⟩ := ih hs
      exists i
      apply ty.renaming
      constructor
      . assumption
      . exact AgreeRen.rfl wf

theorem Typed.weaken :
    Typed Γ m a ->
    Typed Γ b (.srt i) ->
    Typed (b :: Γ) m.[ren .succ] a.[ren .succ] := by
  intro tym tyb
  apply tym.renaming
  constructor
  . assumption
  . exact AgreeRen.rfl tym.wf

theorem Typed.eweaken :
    Γ' = (b :: Γ) ->
    m' = m.[ren .succ] ->
    a' = a.[ren .succ] ->
    Typed Γ m a ->
    Typed Γ b (.srt i) ->
    Typed Γ' m' a' := by
  intros
  subst_vars
  apply Typed.weaken <;> assumption
