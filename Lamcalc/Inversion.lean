import Lamcalc.Substitution
open ARS

theorem Typed.pi_inv :
    Typed Γ (.pi a b) c ->
    ∃ i j, Typed (a :: Γ) b (.srt i) ∧ c === .srt j := by
  generalize e: Tm.pi a b = x
  intro ty; induction ty generalizing a b
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

theorem Typed.lam_inv' :
    Typed Γ (.lam a m) c ->
    c === .pi a' b ->
    Typed (a' :: Γ) b (.srt i) ->
    Typed (a' :: Γ) m b := by
  generalize e: Tm.lam a m = x
  intro ty; induction ty generalizing a m
  all_goals try trivial
  case lam =>
    cases e; intro eq ty
    have wf := ty.wf; cases wf
    have ⟨eqa, eqb⟩ := Conv.pi_inj eq; clear eq
    apply Typed.conv
    . apply eqb
    . apply Typed.conv_ctx
      apply Conv.sym eqa
      assumption
      assumption
    . assumption
  case conv ih _ =>
    cases e; intro eq ty
    apply ih
    . rfl
    . apply Conv.trans <;> assumption
    . assumption

theorem Typed.validity : Typed Γ m a -> ∃ i, Typed Γ a (.srt i) := by
  intro ty; induction ty
  all_goals try trivial
  case srt i _ _ =>
    exists i.succ.succ
    constructor
    assumption
  case var wf hs _ =>
    have ⟨i, _⟩ := wf.has_typed hs
    exists i
  case pi i _ j tya _ iha ihb =>
    exists (max i j).succ
    constructor
    exact tya.wf
  case lam tym iha ihm =>
    have wf := tym.wf
    cases wf; case cons i _ _ =>
    have ⟨j, _⟩ := ihm
    exists (max i j)
    constructor <;> assumption
  case app _ tyn ihm _ =>
    replace ⟨i, ihm⟩ := ihm
    replace ⟨i, j, tyb, eq⟩ := ihm.pi_inv
    exists i
    apply Typed.esubst <;> try first | rfl | assumption
    asimp
  case conv i _ _ _ _ _ =>
    exists i

theorem Typed.lam_inv :
    Typed Γ (.lam a m) (.pi a' b) -> Typed (a' :: Γ) m b := by
  intro ty
  have ⟨_, ty⟩ := ty.validity
  have ⟨_, _, ty, _⟩ := ty.pi_inv
  apply Typed.lam_inv'
  . assumption
  . constructor
  . assumption
