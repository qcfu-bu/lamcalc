import Lamcalc.Semantics

@[aesop safe]
lemma pstep_refl {m} : m ≈> m := by
  induction m <;> aesop

lemma pstep_subst {m n} σ : m ≈> n -> m.[σ] ≈> n.[σ] := by
  intro ps
  induction ps generalizing σ <;> clear m n
  case pstep_var x => aesop
  case pstep_lam a m m' _ ih =>
    simp; constructor; aesop
  case pstep_app m m' n n' _ _ ih1 ih2 =>
    simp; constructor <;> aesop
  case pstep_beta a m m' n n' _ _ ih1 ih2 =>
    have h := pstep.pstep_beta a (ih1 (up σ)) (ih2 σ)
    aesop
  case pstep_unit => aesop

def psstep (σ τ : Nat -> tm) : Prop := forall x, (σ x) ≈> (τ x)

lemma psstep_refl {σ} : psstep σ σ := by
  intro x; induction x <;> aesop

lemma psstep_up {σ τ} : psstep σ τ -> psstep (up σ) (up τ) := by
  intro h x
  cases x with
  | zero => simp; constructor
  | succ n =>
    simp [up, scons]
    apply pstep_subst; apply h

lemma pstep_compat {m n σ τ} :
  m ≈> n -> psstep σ τ -> m.[σ] ≈> n.[τ] := by
  intro ps; induction ps generalizing σ τ <;> clear m n
  case pstep_var x => aesop
  case pstep_lam a m m' _ ih =>
    intro pss; simp; constructor
    apply ih; apply psstep_up; assumption
  case pstep_app m m' n n' _ _ ih1 ih2 =>
    intro pss; simp; constructor <;> aesop
  case pstep_beta a m m' n n' _ _ ih1 ih2 =>
    intro pss; simp
    have h := pstep.pstep_beta a (ih1 (psstep_up pss)) (ih2 pss)
    aesop
  case pstep_unit => aesop

lemma psstep_compat {m n σ τ} :
  psstep σ τ -> m ≈> n -> psstep (m .: σ) (n .: τ) := by
  intros pss ps x
  cases x with
  | zero => assumption
  | succ n => simp [scons]; apply pss

lemma pstep_subst_term {m n n'} : n ≈> n' -> m.[n/] ≈> m.[n'/] := by
  intro ps
  apply pstep_compat pstep_refl
  apply psstep_compat psstep_refl ps

lemma pstep_compat_beta {m m' n n'} :
  m ≈> m' -> n ≈> n' -> m.[n/] ≈> m'.[n'/] := by
  intro ps1 ps2
  apply pstep_compat
  . assumption
  . apply psstep_compat psstep_refl ps2

lemma pstep_diamond {m m1 m2} :
  m ≈> m1 -> m ≈> m2 -> ∃ m', m1 ≈> m' ∧ m2 ≈> m' := by
  intro ps; induction ps generalizing m2 <;> clear m m1
  case pstep_var x =>
    intro ps; exists m2; aesop
  case pstep_lam a m m' _ ih =>
    intro ps0
    cases ps0
    case pstep_lam m0 p =>
    have ⟨n, ⟨ps1, ps2⟩⟩ := ih p
    exists (tm.lam a n)
    constructor
    . constructor; assumption
    . constructor; assumption
  case pstep_app m m' n n' ps1 _ ih1 ih2 =>
    intro ps0; cases ps0
    case pstep_app m1 m2 p1 p2 =>
      have ⟨n1, ⟨ps11, ps12⟩⟩ := ih1 p1
      have ⟨n2, ⟨ps21, ps22⟩⟩ := ih2 p2
      exists (tm.app n1 n2)
      constructor
      . constructor <;> assumption
      . constructor <;> assumption
    case pstep_beta a m1 m2 n1 p1 p2 =>
      cases ps1; case pstep_lam m3 ps1 =>
      have ⟨m4, ⟨p3, p4⟩⟩ := ih1 (pstep.pstep_lam a p1)
      have ⟨Z, ⟨p5, p6⟩⟩ := ih2 p2
      cases p3; case pstep_lam X pX =>
      cases p4; case pstep_lam pY =>
        exists X.[Z/]
        constructor
        . apply pstep.pstep_beta <;> assumption
        . apply pstep_compat_beta <;> assumption
  case pstep_beta a m m' n n' _ _ ih1 ih2 =>
    intro ps0; cases ps0
    case pstep_app m1 m2 p1 p2 =>
      cases p1; case pstep_lam m3 p3 =>
      have ⟨X, ⟨p4, p5⟩⟩ := ih1 p3
      have ⟨Y, ⟨p6, p7⟩⟩ := ih2 p2
      exists (X.[Y/])
      constructor
      . apply pstep_compat_beta <;> assumption
      . apply pstep.pstep_beta <;> assumption
    case pstep_beta m1 m2 p1 p2 =>
      have ⟨X, ⟨p3, p4⟩⟩ := ih1 p1
      have ⟨Y, ⟨p5, p6⟩⟩ := ih2 p2
      exists (X.[Y/])
      constructor
      . apply pstep_compat_beta <;> assumption
      . apply pstep_compat_beta <;> assumption
  case pstep_unit =>
    intro ps0; cases ps0
    exists tm.unit
    aesop
