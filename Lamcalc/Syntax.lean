import Lamcalc.Basics

inductive Tm where
  | var : Var -> Tm
  | srt : Nat -> Tm
  | pi  : Tm -> Tm -> Tm
  | lam : Tm -> Tm -> Tm
  | app : Tm -> Tm -> Tm

namespace Tm

instance : Ids Tm where
  ids := var

@[asimp]theorem ids_var x : var x = ids x := rfl

def rename_rec (ξ : Var -> Var) (m : Tm) : Tm :=
  match m with
  | var x => var (ξ x)
  | srt i => srt i
  | pi a b => pi (rename_rec ξ a) (rename_rec (upren ξ) b)
  | lam a m => lam (rename_rec ξ a) (rename_rec (upren ξ) m)
  | app m n => app (rename_rec ξ m) (rename_rec ξ n)

instance : Rename Tm where
  rename := rename_rec

@[asimp]theorem rename_ids : rename ξ (ids x)   = @ids Tm _ (ξ x) := rfl
@[asimp]theorem rename_srt : rename ξ (srt i)   = srt i := rfl
@[asimp]theorem rename_pi  : rename ξ (pi a b)  = pi (rename ξ a) (rename (upren ξ) b) := rfl
@[asimp]theorem rename_lam : rename ξ (lam a m) = lam (rename ξ a) (rename (upren ξ) m) := rfl
@[asimp]theorem rename_app : rename ξ (app m n) = app (rename ξ m) (rename ξ n) := rfl

def subst_rec (σ : Var -> Tm) (m : Tm) : Tm :=
  match m with
  | var x => σ x
  | srt i => srt i
  | pi a b => pi (subst_rec σ a) (subst_rec (up σ) b)
  | lam a m => lam (subst_rec σ a) (subst_rec (up σ) m)
  | app m n => app (subst_rec σ m) (subst_rec σ n)

instance : Subst Tm where
  subst := subst_rec

@[asimp]theorem subst_ids : @subst Tm _ σ (ids x) = σ x := rfl
@[asimp]theorem subst_srt : subst σ (srt i)    = srt i := rfl
@[asimp]theorem subst_pi  : subst σ (pi a b)   = pi (subst σ a) (subst (up σ) b) := rfl
@[asimp]theorem subst_lam : subst σ (lam a m)  = lam (subst σ a) (subst (up σ) m) := rfl
@[asimp]theorem subst_app : subst σ (app m n)  = app (subst σ m) (subst σ n) := rfl

theorem up_upren (ξ : Var -> Var) :
  @up Tm _ _ (ren ξ) = ren (upren ξ) := by
  funext x; cases x <;> asimp

theorem rename_subst ξ (m : Tm) : rename ξ m = m.[ren ξ] := by
  induction m generalizing ξ with
  | var => asimp
  | srt => asimp
  | pi a b iha ihb =>
    asimp[up_upren, iha, ihb]
  | lam a m iha ihm =>
    asimp[up_upren, iha, ihm]
  | app m n ihm ihn =>
    asimp
    constructor
    . apply ihm
    . apply ihn

theorem up_ids : up ids = @ids Tm _ := by
  funext x
  cases x with
  | zero => asimp
  | succ => asimp

theorem subst_id (m : Tm) : m.[ids] = m := by
  induction m with
  | var => asimp
  | srt => asimp
  | pi a b iha ihb =>
    asimp[up_ids, iha, ihb]
  | lam a m iha ihm =>
    asimp[up_ids, iha, ihm]
  | app m n ih1 ih2 =>
    asimp
    constructor <;> assumption

theorem up_comp_ren_subst {T} [Ids T] [Rename T] (ξ : Var -> Var) (σ : Var -> T) :
  up (ξ >>> σ) = upren ξ >>> up σ := by
  funext x
  cases x with
  | zero => rfl
  | succ => asimp

theorem ren_subst_comp ξ σ (m : Tm) : m.[ren ξ].[σ] = m.[ξ >>> σ] := by
  induction m generalizing ξ σ with
  | var => rfl
  | srt => rfl
  | pi a b iha ihb =>
    asimp[up_upren, up_comp_ren_subst, iha, ihb]
  | lam a m iha ihm =>
    asimp[up_upren, up_comp_ren_subst, iha, ihm]
  | app m n ihm ihn =>
    asimp; constructor
    . rw[<-ihm]
    . rw[<-ihn]

theorem up_comp_subst_ren (σ : Var -> Tm) (ξ : Var -> Var) :
  up σ >>> rename (upren ξ) = up (σ >>> rename ξ)  := by
  funext x
  cases x with
  | zero => asimp
  | succ n =>
    asimp[rename_subst]
    have h1 := ren_subst_comp Nat.succ (ren (upren ξ)) (σ n); asimp at h1
    have h2 := ren_subst_comp ξ (ren Nat.succ) (σ n); asimp at h2
    rw[h1, h2]; rfl

theorem subst_ren_comp σ ξ (m : Tm) : m.[σ].[ren ξ] = m.[σ >>> rename ξ] := by
  induction m generalizing σ ξ with
  | var => asimp[rename_subst]
  | srt => asimp
  | pi a b iha ihb =>
    asimp[up_upren, up_comp_subst_ren, iha, ihb]
  | lam a m iha ihm =>
    asimp[up_upren, up_comp_subst_ren, iha, ihm]
  | app m n ihm ihn =>
    asimp; constructor
    . rw[<-ihm]
    . rw[<-ihn]

theorem up_comp (σ τ : Var -> Tm) :  up σ >> up τ = up (σ >> τ) := by
  apply funext
  intro x
  cases x with
  | zero =>
    asimp
  | succ n =>
    asimp[rename_subst]
    have h1 := subst_ren_comp τ Nat.succ (σ n)
    have h2 := ren_subst_comp Nat.succ (up τ) (σ n)
    rw[h1, h2]
    rfl

theorem subst_comp (σ τ : Var -> Tm) m : m.[σ].[τ] = m.[σ >> τ] := by
  induction m generalizing σ τ with
  | var => asimp
  | srt => asimp
  | pi a b iha ihb =>
    asimp[up_comp, iha, ihb]
  | lam a m iha ihm =>
    asimp[up_comp, iha, ihm]
  | app m n ihm ihn =>
    asimp; constructor
    . apply ihm
    . apply ihn

instance : SubstLemmas Tm where
  rename_subst := rename_subst
  subst_id := subst_id
  id_subst := by intros; asimp
  subst_comp := subst_comp

end Tm
