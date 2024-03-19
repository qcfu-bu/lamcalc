import Lamcalc.Semantics
open ARS

@[aesop safe [constructors, cases]]
inductive pstep : tm -> tm -> Prop where
| pstep_var x :
  pstep (ids x) (ids x)
| pstep_lam a {m m'} :
  pstep m m' ->
  pstep (.lam a m) (.lam a m')
| pstep_app {m m' n n'} :
  pstep m m' ->
  pstep n n' ->
  pstep (.app m n) (.app m' n')
| pstep_beta a {m m' n n'} :
  pstep m m' ->
  pstep n n' ->
  pstep (.app (.lam a m) n) (m'.[n'/])
| pstep_unit :
  pstep .unit .unit

infix:50 " ≈> " => pstep

def sred (σ τ : Nat -> tm) := ∀ x, (σ x) ~>* (τ x)

lemma step_subst σ {m n} : m ~> n -> m.[σ] ~> n.[σ] := by
  intro st
  induction st generalizing σ <;> clear m n
  case step_lam a m m' _ ih =>
    simp; constructor
    apply ih
  case step_appM m m' n _ ih =>
    simp; constructor
    apply ih
  case step_appN m n n' _ ih =>
    simp; constructor
    apply ih
  case step_beta a m n =>
    simp
    rw [<-up_comp_subst]
    rw [<-subst_comp]
    apply step.step_beta

lemma red_lam {a m m'} :
  m ~>* m' -> .lam a m ~>* .lam a m' := by
  intro r
  apply star.hom (tm.lam a) _ r
  intros x y
  apply step.step_lam

lemma red_app {m m' n n'} :
  m ~>* m' -> n ~>* n' -> .app m n ~>* .app m' n' := by
  intros r1 r2
  apply (@star.trans _ _ (tm.app m' n))
  . apply star.hom (tm.app · n) _ r1
    intros x y; simp
    apply step.step_appM
  . apply star.hom _ _ r2
    intros x y
    apply step.step_appN

lemma red_subst {m n} σ : m ~>* n -> m.[σ] ~>* n.[σ] := by
  intro r
  induction r with
  | R => aesop
  | SE _ st ih =>
    apply star.trans ih
    apply star.singleton
    apply step_subst _ st

lemma sred_up {σ τ} : sred σ τ -> sred (up σ) (up τ) := by
  intros h x
  cases x with
  | zero => simp; aesop
  | succ n =>
    simp [up, funcomp, scons]
    apply red_subst _ (h n)

lemma red_compat {σ τ} m : sred σ τ -> m.[σ] ~>* m.[τ] := by
  induction m generalizing σ τ with
  | var x =>
    simp; intro h
    apply h
  | lam a m ih =>
    simp; intro h
    apply red_lam (ih (sred_up h))
  | app m n ihm ihn =>
    simp; intro h
    apply red_app (ihm h) (ihn h)
  | unit => intro _; aesop

def sconv (σ τ : Nat -> tm) := ∀ x, σ x === τ x

lemma conv_lam {a m m'} :
  m === m' -> tm.lam a m === tm.lam a m' := by
  intros r; apply conv.hom _ _ r
  intros x y; apply step.step_lam

lemma conv_app {m m' n n'} :
  m === m' -> n === n' -> tm.app m n === tm.app m' n' := by
  intros r1 r2
  apply @conv.trans _ _ (tm.app m' n)
  . apply conv.hom (tm.app · n) _ r1
    intros x y; simp
    apply step.step_appM
  . apply conv.hom _ _ r2
    intros x y
    apply step.step_appN

lemma conv_subst σ {m n} : m === n -> m.[σ] === n.[σ] := by
  intros r
  apply conv.hom _ _ r
  apply step_subst

lemma sconv_up {σ τ} : sconv σ τ -> sconv (up σ) (up τ) := by
  intros h x
  cases x with
  | zero => simp; aesop
  | succ n =>
    simp [up, funcomp, scons]
    apply conv_subst _ (h n)

lemma conv_compat {σ τ} m : sconv σ τ -> m.[σ] === m.[τ] := by
  induction m generalizing σ τ with
  | var x =>
    simp; intro h; apply h
  | lam a m ih =>
    simp; intro h
    apply conv_lam (ih (sconv_up h))
  | app m n ihm ihn =>
    simp; intro h
    apply conv_app (ihm h) (ihn h)
  | unit => simp; aesop

lemma conv_beta {m n1 n2} : n1 === n2 -> m.[n1/] === m.[n2/] := by
  intro h; apply conv_compat
  intro x
  cases x with
  | zero => simp [scons]; assumption
  | succ n => simp [scons]; aesop

@[aesop safe]
lemma pstep_refl {m} : m ≈> m := by
  induction m <;> aesop

lemma step_pstep {m m'} : m ~> m' -> m ≈> m' := by
  intro st
  induction st with
  | step_lam a _ ih => constructor; assumption
  | step_appM _ ih => constructor <;> aesop
  | step_appN _ ih => constructor <;> aesop
  | step_beta a => constructor <;> aesop

lemma pstep_red {m n} : m ≈> n -> m ~>* n := by
  intro ps
  induction ps <;> clear m n
  case pstep_var x => aesop
  case pstep_lam a m m' _ ih =>
    apply red_lam ih
  case pstep_app m m' n n' _ _ ihm ihn =>
    apply red_app ihm ihn
  case pstep_beta a m m' n n' _ _ ihm ihn =>
    apply star.trans
    . apply red_app (red_lam ihm) ihn
    . apply star.singleton
      apply step.step_beta
  case pstep_unit => aesop

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
    simp [up, scons, funcomp]
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

lemma pstep_diamond : diamond pstep := by
  intros m m1 m2 ps; induction ps generalizing m2 <;> clear m m1
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

lemma pstep_strip {m m1 m2} :
  m ≈> m1 -> m ~>* m2 -> ∃ m', m1 ~>* m' ∧ m2 ≈> m' := by
  intros p r
  induction r generalizing m1 p <;> clear m2
  case R =>
    exists m1; constructor
    . apply star.R
    . assumption
  case SE _ s1 ih =>
    rcases ih p with ⟨m2, ⟨r, s2⟩⟩
    rcases pstep_diamond (step_pstep s1) s2 with ⟨m3, ⟨p1, p2⟩⟩
    exists m3; constructor
    . apply star.trans r (pstep_red p2)
    . assumption

theorem step_confluent : confluent step := by
  intros x y z r
  induction r generalizing z <;> clear y
  case R =>
    intro h; exists z
    constructor <;> aesop
  case SE _ s ih =>
    intro h
    rcases ih h with ⟨z1, ⟨s1 , s2⟩⟩
    rcases pstep_strip (step_pstep s) s1 with ⟨z2, ⟨s3, s4⟩⟩
    exists z2; constructor
    . assumption
    . apply star.trans s2 (pstep_red s4)
