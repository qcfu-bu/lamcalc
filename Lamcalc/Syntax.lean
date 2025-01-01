import Lamcalc.Basics

inductive ty where
| arrow : ty -> ty -> ty
| unit

inductive tm where
| var : Var -> tm
| lam : ty -> tm -> tm
| app : tm -> tm -> tm
| unit : tm

instance : Ids tm where
  ids := tm.var

@[asimp]theorem ids_var x : tm.var x = ids x := rfl

@[asimp]
def tm.rename (ξ : Var -> Var) (m : tm) : tm :=
  match m with
  | var x => var (ξ x)
  | lam a m => lam a (rename (upren ξ) m)
  | app m n => app (rename ξ m) (rename ξ n)
  | unit => unit

instance : Rename tm where
  rename := tm.rename

@[asimp]theorem rename_ids ξ x : rename ξ (ids x) = @ids tm _ (ξ x) := rfl
@[asimp]theorem rename_lam ξ a m : rename ξ (tm.lam a m) = tm.lam a (rename (upren ξ) m) := rfl
@[asimp]theorem rename_app ξ m n : rename ξ (tm.app m n) = tm.app (rename ξ m) (rename ξ n) := rfl
@[asimp]theorem rename_unit ξ : rename ξ (tm.unit) = tm.unit := rfl

def tm.subst (σ : Var -> tm) (m : tm) : tm :=
  match m with
  | var x => σ x
  | lam a m => lam a (subst (up σ) m)
  | app m n => app (subst σ m) (subst σ n)
  | unit => unit

instance : Subst tm where
  subst := tm.subst

@[asimp]theorem subst_ids (σ : Var -> tm) x : subst σ (ids x) = σ x := by rfl
@[asimp]theorem subst_lam σ a m : subst σ (tm.lam a m) = tm.lam a (subst (up σ) m) := by rfl
@[asimp]theorem subst_app σ m n : subst σ (tm.app m n) = tm.app (subst σ m) (subst σ n) := by rfl
@[asimp]theorem subst_unit σ : subst σ tm.unit = tm.unit := rfl

theorem up_upren (ξ : Var -> Var) :
  @up tm _ _ (ren ξ) = ren (upren ξ) := by
  funext x; cases x <;> asimp

theorem up_upren_n (ξ : Var -> Var) (n : Var) :
  @upn tm _ _ n (ren ξ ) = ren (n.repeat upren ξ) := by
  induction n generalizing ξ with
  | zero =>
    asimp[Nat.repeat]
  | succ n ih =>
    asimp[Nat.repeat]
    rw [<-up_upren]
    rw [<-ih]

theorem tm.rename_subst ξ (m : tm) : rename ξ m = m.[ren ξ] := by
  induction m generalizing ξ with
  | var x => simp[asimp]
  | lam a m ih =>
    asimp[up_upren]; rw[ih]
  | app m n ihm ihn =>
    asimp
    constructor
    . apply ihm
    . apply ihn
  | _ => asimp

theorem up_ids : up ids = @ids tm _ := by
  funext x
  cases x with
  | zero => asimp
  | succ => asimp

theorem tm.subst_id (m : tm) :
  m.[ids] = m := by
  induction m with
  | var x => asimp
  | lam a m ih =>
    asimp[up_ids]
    assumption
  | app m n ih1 ih2 =>
    asimp
    constructor <;> assumption
  | unit => asimp

theorem up_comp_ren_subst {T} [Ids T] [Rename T] (ξ : Var -> Var) (σ : Var -> T) :
  up (ξ >>> σ) = upren ξ >>> up σ := by
  funext x
  cases x with
  | zero => rfl
  | succ => asimp

theorem ren_subst_comp ξ σ (m : tm) : m.[ren ξ].[σ] = m.[ξ >>> σ] := by
  induction m generalizing ξ σ with
  | var x => rfl
  | lam a m ih =>
    asimp[up_comp_ren_subst]
    rw [<- ih]
    simp [up_upren]
  | app m n ihm ihn =>
    asimp; constructor
    . rw [<- ihm]
    . rw [<- ihn]
  | unit => asimp

theorem up_comp_subst_ren (σ : Var -> tm) (ξ : Var -> Var) :
  up (σ >>> rename ξ) = up σ >>> rename (upren ξ) := by
  funext x
  cases x with
  | zero => asimp
  | succ n =>
    asimp[rename, tm.rename_subst]
    have h1 := ren_subst_comp Nat.succ (ren (upren ξ)) (σ n); asimp at h1
    have h2 := ren_subst_comp ξ (ren Nat.succ) (σ n); asimp at h2
    rw [h1, h2]; rfl

theorem subst_ren_comp σ ξ (m : tm) : m.[σ].[ren ξ] = m.[σ >>> rename ξ] := by
  induction m generalizing σ ξ with
  | var x =>
    asimp[rename, tm.rename_subst]
  | lam a m ih =>
    asimp;
    rw [up_upren]
    rw [ih]
    rw [<- up_comp_subst_ren]
  | app m n ihm ihn =>
    asimp; constructor
    . rw [<- ihm]
    . rw [<- ihn]
  | unit => rfl

theorem up_comp (σ τ : Var -> tm) : up (σ >> τ) = up σ >> up τ := by
  apply funext
  intro x
  cases x with
  | zero =>
    asimp
  | succ n =>
    asimp[rename, tm.rename_subst]
    have h1 := subst_ren_comp τ Nat.succ (σ n)
    have h2 := ren_subst_comp Nat.succ (up τ) (σ n)
    rw [h1, h2]
    rfl

theorem tm.subst_comp (σ τ : Var -> tm) m : m.[σ].[τ] = m.[σ >> τ] := by
  induction m generalizing σ τ with
  | var x => asimp
  | lam a m ih =>
    asimp
    rw [ih]
    rw [<-up_comp]
  | app m n ihm ihn =>
    asimp; constructor
    . apply ihm
    . apply ihn
  | unit => rfl

instance : SubstLemmas tm where
  rename_subst := tm.rename_subst
  subst_id := tm.subst_id
  id_subst := by intros; asimp
  subst_comp := tm.subst_comp
