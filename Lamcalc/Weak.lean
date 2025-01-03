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
    AgreeRen (ξ >>> Nat.succ) Γ (a :: Γ')

theorem AgreeRen.refl : Wf Γ -> AgreeRen id Γ Γ := by
  intro wf
  induction wf using Wf.rec (motive_1 := fun Γ _ _ _ => True)
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
      have e : a.[@ren Tm _ ξ >> shift] = a.[ren ξ].[shift] := by asimp
      rw[e]; constructor
    case succ x a hs =>
      have e : a.[@ren Tm _ ξ >> shift] = a.[ren ξ].[shift] := by asimp
      rw[e]; constructor
      apply ih; assumption
  | @wk _ a _ ξ _ _ _ ih =>
    intro h; asimp
    have e : a.[@ren Tm _ (ξ >>> Nat.succ)] = a.[ren ξ].[shift] := by asimp; rfl
    rw[e]; constructor
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

theorem Typed.rename :
  Typed Γ m A -> AgreeRen ξ Γ Γ' -> Typed Γ' m.[ren ξ] A.[ren ξ] := by
  intro ty
  induction ty
  using Typed.rec (motive_2 := fun Γ _ => ∀ Γ' ξ, AgreeRen ξ Γ Γ' -> Wf Γ')
  generalizing ξ Γ'
  with
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
