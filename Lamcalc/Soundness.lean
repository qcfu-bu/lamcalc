import Lamcalc.Inversion
open ARS

theorem Typed.preservation :
    Typed Γ m a -> m ~> n -> Typed Γ n a := by
  intro ty
  induction ty generalizing n
  all_goals try trivial
  case srt => intro st; cases st
  case var => intro st; cases st
  case pi _ _ iha ihb =>
    intro st; cases st with
    | piA _ st =>
      constructor
      . apply iha st
      . apply Typed.conv_ctx
        apply Conv.singletoni st
        apply iha st
        assumption
    | piB _ st =>
      constructor
      . assumption
      . apply ihb st
  case lam tya tym iha ihm =>
    have ⟨i, tyb⟩ := tym.validity
    intro st; cases st with
    | lamA _ st =>
      apply Typed.conv
      . apply Conv.pi
        apply Conv.singletoni st
        constructor
      . constructor
        apply iha st
        apply Typed.conv_ctx
        apply Conv.singletoni st
        apply iha st
        assumption
      . constructor <;> assumption
    | lamM _ st =>
      constructor
      . assumption
      . apply ihm st
  case app tym tyn ihm ihn =>
    have ⟨_, ty⟩ := tym.validity
    have ⟨_, _, tyb, _⟩ := ty.pi_inv
    intro st; cases st with
    | appM _ st =>
      constructor
      . apply ihm st
      . assumption
    | appN _ st =>
      apply Typed.conv
      . apply Conv.subst1
        apply Conv.singletoni st
      . constructor
        assumption
        apply ihn st
      . apply tyb.subst tyn
    | beta =>
      replace tym := tym.lam_inv
      apply tym.subst tyn
  case conv eq tym tyb ihm ihb =>
    intro st
    apply Typed.conv
    . assumption
    . apply ihm st
    . assumption
