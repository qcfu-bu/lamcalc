import Lean
import Lamcalc.Semantics
open ARS

inductive PStep : Tm -> Tm -> Prop where
| var x :
  PStep (ids x) (ids x)
| srt i :
  PStep (.srt i) (.srt i)
| pi {a a' b b'} :
  PStep a a' ->
  PStep b b' ->
  PStep (.pi a b) (.pi a' b')
| lam {a a' m m'} :
  PStep a a' ->
  PStep m m' ->
  PStep (.lam a m) (.lam a' m')
| app {m m' n n'} :
  PStep m m' ->
  PStep n n' ->
  PStep (.app m n) (.app m' n')
| beta a {m m' n n'} :
  PStep m m' ->
  PStep n n' ->
  PStep (.app (.lam a m) n) (m'.[n'/])

infix:50 " ≈> " => PStep

def SRed (σ τ : Nat -> Tm) := ∀ x, (σ x) ~>* (τ x)

theorem Step.subst : m ~> n -> m.[σ] ~> n.[σ] := by
  intro st
  induction st generalizing σ with
  | piA b st ih =>
    asimp; constructor; apply ih
  | piB a st ih =>
    asimp; constructor; apply ih
  | lamA m st ih =>
    asimp; constructor; apply ih
  | lamM a st ih =>
    asimp; constructor; apply ih
  | appM n st ih =>
    asimp; constructor; apply ih
  | appN m st ih =>
    asimp; constructor; apply ih
  | beta a m n =>
    asimp
    have h := Step.beta a.[σ] m.[up σ] n.[σ]
    asimp at h
    assumption

theorem Red.pi : a ~>* a' -> b ~>* b' -> .pi a b ~>* .pi a' b' := by
  intro ra rb
  apply (@Star.trans _ _ (Tm.pi a' b))
  . apply Star.hom _ _ ra
    intro x y
    apply Step.piA
  . apply Star.hom _ _ rb
    intro x y
    apply Step.piB

theorem Red.lam : a ~>* a' -> m ~>* m' -> .lam a m ~>* .lam a' m' := by
  intro ra rm
  apply (@Star.trans _ _ (Tm.lam a' m))
  . apply Star.hom _ _ ra
    intro x y
    apply Step.lamA
  . apply Star.hom _ _ rm
    intro x y
    apply Step.lamM

theorem Red.app : m ~>* m' -> n ~>* n' -> .app m n ~>* .app m' n' := by
  intros r1 r2
  apply (@Star.trans _ _ (Tm.app m' n))
  . apply Star.hom _ _ r1
    intros x y
    apply Step.appM
  . apply Star.hom _ _ r2
    intros x y
    apply Step.appN

theorem Red.subst : m ~>* n -> m.[σ] ~>* n.[σ] := by
  intro r
  induction r with
  | R => constructor
  | SE _ st ih =>
    apply Star.trans ih
    apply Star.singleton
    apply Step.subst st

theorem SRed.up {σ τ} : SRed σ τ -> SRed (up σ) (up τ) := by
  intros h x
  cases x with
  | zero => asimp; constructor
  | succ n =>
    asimp
    apply Red.subst (h n)

theorem Red.compat : SRed σ τ -> m.[σ] ~>* m.[τ] := by
  induction m generalizing σ τ with
  | var x =>
    asimp; intro h
    apply h
  | srt i =>
    asimp; intro h
    constructor
  | pi a b iha ihb =>
    asimp; intro h
    apply Red.pi
    . apply iha; assumption
    . apply ihb
      apply SRed.up
      assumption
  | lam a m iha ihm =>
    asimp; intro h
    apply Red.lam
    . apply iha; assumption
    . apply ihm
      apply SRed.up
      assumption
  | app m n ihm ihn =>
    asimp; intro h
    apply Red.app (ihm h) (ihn h)

def SConv (σ τ : Nat -> Tm) := ∀ x, σ x === τ x

theorem Conv.pi : a === a' -> b === b' -> .pi a b === .pi a' b' := by
  intros ra rb
  apply @Conv.trans _ _ (Tm.pi a' b)
  . apply Conv.hom _ _ ra
    intro x y
    apply Step.piA
  . apply Conv.hom _ _ rb
    intro x y
    apply Step.piB

theorem Conv.lam : a === a' -> m === m' -> .lam a m === .lam a' m' := by
  intros ra rm
  apply @Conv.trans _ _ (Tm.lam a' m)
  . apply Conv.hom _ _ ra
    intro x y
    apply Step.lamA
  . apply Conv.hom _ _ rm
    intro x y
    apply Step.lamM

theorem Conv.app : m === m' -> n === n' -> .app m n === .app m' n' := by
  intros r1 r2
  apply @Conv.trans _ _ (Tm.app m' n)
  . apply Conv.hom _ _ r1
    intros x y
    apply Step.appM
  . apply Conv.hom _ _ r2
    intros x y
    apply Step.appN

theorem Conv.subst : m === n -> m.[σ] === n.[σ] := by
  intros r
  apply Conv.hom _ _ r
  intros x y
  apply Step.subst

theorem SConv.up : SConv σ τ -> SConv (up σ) (up τ) := by
  intros h x
  cases x with
  | zero => asimp; constructor
  | succ n =>
    asimp
    apply Conv.subst (h n)

theorem Conv.compat : SConv σ τ -> m.[σ] === m.[τ] := by
  induction m generalizing σ τ with
  | var x =>
    asimp; intro h; apply h
  | srt i =>
    asimp; intro h; constructor
  | pi a b iha ihb =>
    asimp; intro h
    apply Conv.pi
    . apply iha; assumption
    . apply ihb
      apply SConv.up
      assumption
  | lam a m iha ihm =>
    asimp; intro h
    apply Conv.lam
    . apply iha; assumption
    . apply ihm
      apply SConv.up
      assumption
  | app m n ihm ihn =>
    asimp; intro h
    apply Conv.app (ihm h) (ihn h)

theorem Conv.subst1 : n1 === n2 -> m.[n1/] === m.[n2/] := by
  intro h; apply Conv.compat
  intro x
  cases x with
  | zero => asimp; assumption
  | succ => asimp; constructor

theorem PStep.rfl : m ≈> m := by
  induction m with
  | var => constructor
  | srt => constructor
  | pi  => constructor <;> assumption
  | lam => constructor <;> assumption
  | app => constructor <;> assumption

theorem Step.pstep : m ~> m' -> m ≈> m' := by
  intro st
  induction st with
  | piA =>
    constructor
    . assumption
    . exact PStep.rfl
  | piB =>
    constructor
    . exact PStep.rfl
    . assumption
  | lamA =>
    constructor
    . assumption
    . exact PStep.rfl
  | lamM =>
    constructor
    . exact PStep.rfl
    . assumption
  | appM =>
    constructor
    . assumption
    . exact PStep.rfl
  | appN =>
    constructor
    . exact PStep.rfl
    . assumption
  | beta =>
    constructor
    . exact PStep.rfl
    . exact PStep.rfl

theorem PStep.red : m ≈> n -> m ~>* n := by
  intro ps
  induction ps with
  | var => constructor
  | srt => constructor
  | pi => apply Red.pi <;> assumption
  | lam => apply Red.lam <;> assumption
  | app => apply Red.app <;> assumption
  | @beta _ _ _ _ a stm stn ihm ihn =>
    apply Star.trans
    . apply Red.app (Red.lam Star.R ihm) ihn
    . apply Star.singleton
      apply Step.beta

theorem PStep.subst : m ≈> n -> m.[σ] ≈> n.[σ] := by
  intro ps
  induction ps generalizing σ with
  | var => exact PStep.rfl
  | srt => exact PStep.rfl
  | pi sta stb iha ihb =>
    asimp; constructor
    . exact iha
    . exact ihb
  | lam sta stm iha ihm =>
    asimp; constructor
    . exact iha
    . exact ihm
  | app stm stn ihm ihn =>
    asimp; constructor
    . exact ihm
    . exact ihn
  | beta a _ _ ihm ihn =>
    have h := PStep.beta a.[σ] (@ihm (up σ)) (@ihn σ)
    asimp
    asimp at h
    assumption

def PSStep (σ τ : Nat -> Tm) : Prop := forall x, (σ x) ≈> (τ x)

theorem PSStep.rfl : PSStep σ σ := by
  intro x; induction x <;>
  apply PStep.rfl

theorem PSStep.up : PSStep σ τ -> PSStep (up σ) (up τ) := by
  intro h x
  cases x with
  | zero => asimp; constructor
  | succ n =>
    asimp
    apply PStep.subst; apply h

theorem PStep.compat : m ≈> n -> PSStep σ τ -> m.[σ] ≈> n.[τ] := by
  intro ps; induction ps generalizing σ τ with
  | var => intro pss; apply pss
  | srt => intro; asimp; apply PStep.rfl
  | pi sta stb iha ihb =>
    intro; asimp
    constructor
    . apply iha; assumption
    . apply ihb; apply PSStep.up; assumption
  | lam sta stm iha ihm =>
    intro; asimp
    constructor
    . apply iha; assumption
    . apply ihm; apply PSStep.up; assumption
  | app stm stn ihm ihn =>
    intro; asimp
    constructor
    . apply ihm; assumption
    . apply ihn; assumption
  | beta a _ _ ihm ihn =>
    intro pss; asimp
    have h := PStep.beta a.[σ] (ihm (PSStep.up pss)) (ihn pss)
    asimp at h
    assumption

theorem PSStep.compat : PSStep σ τ -> m ≈> n -> PSStep (m .: σ) (n .: τ) := by
  intros pss ps x
  cases x with
  | zero => assumption
  | succ n => simp [scons]; apply pss

theorem PStep.subst1 : n ≈> n' -> m.[n/] ≈> m.[n'/] := by
  intro ps
  apply PStep.compat PStep.rfl
  apply PSStep.compat PSStep.rfl ps

theorem PStep.compat_subst1 : m ≈> m' -> n ≈> n' -> m.[n/] ≈> m'.[n'/] := by
  intro ps1 ps2
  apply PStep.compat
  . assumption
  . apply PSStep.compat PSStep.rfl ps2

theorem PStep.diamond : Diamond PStep := by
  intros m m1 m2 ps
  induction ps generalizing m2 with
  | var =>
    intro ps; exists m2
    constructor
    . assumption
    . exact PStep.rfl
  | srt i =>
    intro ps; exists m2
    constructor
    . assumption
    . exact PStep.rfl
  | pi _ _ iha ihb =>
    intro ps
    cases ps with
    | pi psa psb =>
      have ⟨a, psa1, psa2⟩ := iha psa
      have ⟨b, psb1, psb2⟩ := ihb psb
      exists .pi a b
      constructor
      . constructor <;> assumption
      . constructor <;> assumption
  | lam _ _ iha ihm =>
    intro ps
    cases ps with
    | lam psa psm =>
      have ⟨a, psa1, psa2⟩ := iha psa
      have ⟨m, psm1, psm2⟩ := ihm psm
      exists .lam a m
      constructor
      . constructor <;> assumption
      . constructor <;> assumption
  | app psm psn ihm ihn =>
    intro ps
    cases ps with
    | app psm psn =>
      have ⟨m, psm1, psm2⟩ := ihm psm
      have ⟨n, psn1, psn2⟩ := ihn psn
      exists .app m n
      constructor
      . constructor <;> assumption
      . constructor <;> assumption
    | beta a psm' psn' =>
      cases psm; case lam _ _ psa psm  =>
      have ⟨_, psm1, psm2⟩ := ihm (PStep.lam PStep.rfl psm')
      have ⟨n, psn1, psn2⟩ := ihn psn'
      cases psm1; case lam m _ psm1 =>
      cases psm2; case lam _ psm2 =>
      exists m.[n/]
      constructor
      . apply PStep.beta <;> assumption
      . apply PStep.compat_subst1 <;> assumption
  | beta _ _ _ ihm ihn =>
    intro ps
    cases ps with
    | app psm psn =>
      cases psm; case lam _ psm =>
      have ⟨m, psm1, psm2⟩ := ihm psm
      have ⟨n, psn1, psn2⟩ := ihn psn
      exists m.[n/]
      constructor
      . apply PStep.compat_subst1 <;> assumption
      . apply PStep.beta <;> assumption
    | beta _ psm psn =>
      have ⟨m, psm1, psm2⟩ := ihm psm
      have ⟨n, psn1, psn2⟩ := ihn psn
      exists m.[n/]
      constructor
      . apply PStep.compat_subst1 <;> assumption
      . apply PStep.compat_subst1 <;> assumption

theorem PStep.strip : m ≈> m1 -> m ~>* m2 -> ∃ m', m1 ~>* m' ∧ m2 ≈> m' := by
  intros p r
  induction r generalizing m1 p with
  | R =>
    exists m1; constructor
    . apply Star.R
    . assumption
  | SE _ s1 ih =>
    have ⟨m2, r, s2⟩ := ih p
    have ⟨m3, p1, p2⟩ := PStep.diamond (s1.pstep) s2
    exists m3; constructor
    . apply Star.trans r (p2.red)
    . assumption

theorem Step.confluent : Confluent Step := by
  intros x y z r
  induction r generalizing z with
  | R =>
    intro h; exists z
    constructor
    assumption
    constructor
  | SE _ s ih =>
    intro h
    have ⟨z1, s1, s2⟩ := ih h
    have ⟨z2, s3, s4⟩ := PStep.strip (s.pstep) s1
    exists z2; constructor
    . assumption
    . apply Star.trans s2 (s4.red)

theorem Step.cr : CR Step := by
  rw[<-Confluent.cr]
  apply Step.confluent

theorem Red.var_inv : .var x ~>* y -> y = .var x := by
  intro r
  induction r with
  | R => rfl
  | SE r st ih =>
    subst ih; cases st

theorem Red.srt_inv : .srt i ~>* x -> x = .srt i := by
  intro r
  induction r with
  | R => rfl
  | SE r st ih =>
    subst ih; cases st

theorem Red.pi_inv : .pi a b ~>* x ->
    ∃ a' b', a ~>* a' ∧ b ~>* b' ∧ x = .pi a' b' := by
  intro r
  induction r with
  | R =>
    exists a, b
    repeat constructor
  | SE r st ih =>
    have ⟨a1, b1, ra1, rb1, e⟩ := ih
    subst e
    cases st with
    | @piA _ a2 _ ra2 =>
      exists a2, b1
      repeat' apply And.intro
      . apply Star.SE
        apply ra1
        apply ra2
      . apply rb1
      . rfl
    | @piB _ _ b2 rb2 =>
      exists a1, b2
      repeat' apply And.intro
      . apply ra1
      . apply Star.SE
        apply rb1
        apply rb2
      . rfl

theorem Red.lam_inv : .lam a m ~>* x ->
    ∃ a' m', a ~>* a' ∧ m ~>* m' ∧ x = .lam a' m' := by
  intro r
  induction r with
  | R =>
    exists a, m
    repeat constructor
  | SE r st ih =>
    have ⟨a1, m1, ra1, rm1, e⟩ := ih
    subst e
    cases st with
    | @lamA _ a2 _ ra2 =>
      exists a2, m1
      repeat' apply And.intro
      . apply Star.SE
        apply ra1
        apply ra2
      . apply rm1
      . rfl
    | @lamM _ _ m2 rm2 =>
      exists a1, m2
      repeat' apply And.intro
      . apply ra1
      . apply Star.SE
        apply rm1
        apply rm2
      . rfl

namespace Tactic
open Lean Elab Meta

-- Eliminate an `Exists` proof `m` using `elim`.
def existsElim (m : Expr) (elim : Expr -> Expr -> MetaM Expr) : MetaM Expr := do
  let mType <- whnf $ <-inferType m
  match mType.getAppFnArgs with
  | (``Exists, #[a, p]) =>
    withLocalDecl `x BinderInfo.default a fun x =>
    withLocalDecl `y BinderInfo.default (.app p x) fun y => do
      let body <- mkLambdaFVars #[x, y] (<-elim x y)
      mkAppOptM ``Exists.elim #[none, none, none, m, body]
  | _ => throwError "existsElim {mType}"

-- Eliminate an `And` proof `m` using `elim`.
def andElim (m : Expr) (elim : Expr -> Expr -> MetaM Expr) : MetaM Expr := do
  let mType <- whnf $ <-inferType m
  match mType.and? with
  | some (a, b) =>
    withLocalDecl `x BinderInfo.default a fun x =>
    withLocalDecl `y BinderInfo.default b fun y => do
      let body <- mkLambdaFVars #[x, y] (<-elim x y)
      mkAppM ``And.elim #[body, m]
  | none => throwError f!"andElim {mType}"

-- Given a proposition consisting of `Exists` and `And`, find all `Eq`s among the conjuncts.
partial def projEqs (m : Expr) (elim : Array Expr -> MetaM Expr) : MetaM Expr := do
  let mType <- whnf $ <-inferType m
  match mType.getAppFn.constName? with
  | some ``Exists =>
    existsElim m fun x y => do
      projEqs x fun eqs1 =>
      projEqs y fun eqs2 =>
      elim (eqs1 ++ eqs2)
  | some ``And =>
    andElim m fun x y =>
      projEqs x fun eqs1 =>
      projEqs y fun eqs2 =>
      elim (eqs1 ++ eqs2)
  | some ``Eq => elim #[m]
  | _ => elim #[]

-- Assuming `id : a === b`, get the associated expression of `id` and the inversion lemmas of `a` and `b`.
def getConv (goal : MVarId) (id : Name) : MetaM (Expr × Expr × Expr) := do
  goal.withContext do
    let lctx <- getLCtx
    match lctx.findFromUserName? id with
    | some ldecl =>
      let declExpr := ldecl.toExpr
      let declType <- inferType declExpr
      match declType.app2? ``conv_step with
      | some (a, b) => return (declExpr, a, b)
      | _ => throwTacticEx `getConv goal
    | none => throwTacticEx `getConv goal

-- Apply `church_rosser` theorem to refute impossible conversion.
def applyCR (goal : MVarId) (m l1 l2 : Expr) : MetaM Expr := do
  let cr <- mkAppM ``Step.cr #[m]
  existsElim cr fun _ h =>
  andElim h fun h1 h2 => do
    let h1 <- mkAppM' l1 #[h1]
    let h2 <- mkAppM' l2 #[h2]
    projEqs h1 fun es1 =>
    projEqs h2 fun es2 => do
      let e1 <- mkAppM ``Eq.symm #[es1[0]!]
      let e2 <- mkAppM ``Eq.trans #[e1, es2[0]!]
      mkAppOptM ``Tm.noConfusion #[<-goal.getType, none, none, e2]

/-
  Get the associated inversion lemma for `m`. For more complex languages, the
  list of inversion lemmas need to be extended. -/
def getInvLemma (m : Expr) : MetaM Expr := do
  match m.getAppFn.constName! with
  | ``Tm.var => return .const ``Red.var_inv []
  | ``Tm.srt => return .const ``Red.srt_inv []
  | ``Tm.pi  => return .const ``Red.pi_inv  []
  | ``Tm.lam => return .const ``Red.lam_inv []
  | _ => throwError `getInvLemma

open Lean Elab Tactic in
/--
  `false_conv h` refutes impossible conversion proof `h`.  -/
elab "false_conv" h:ident : tactic =>
  withMainContext do
    let goal <- getMainGoal
    let (m, a, b) <- getConv goal h.getId
    let lemma_a <- getInvLemma a
    let lemma_b <- getInvLemma b
    let pf <- applyCR goal m lemma_a lemma_b
    closeMainGoal `false_conv pf

end Tactic

example (h : Tm.lam a b === Tm.pi a b) : False := by
  false_conv h
