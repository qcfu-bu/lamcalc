import Lamcalc.Basics

inductive ty where
| arrow : ty -> ty -> ty
| unit

inductive tm where
| var : Nat -> tm
| lam : ty -> tm -> tm
| app : tm -> tm -> tm
| unit : tm

instance : Ids tm where
  ids := tm.var

@[simp] theorem ids_var x : tm.var x = ids x := rfl

def tm.rename (ξ : Nat -> Nat) (m : tm) : tm :=
  match m with
  | var x => var (ξ x)
  | lam a m => lam a (rename (upren ξ) m)
  | app m n => app (rename ξ m) (rename ξ n)
  | unit => unit

instance : Rename tm where
  rename := tm.rename

@[simp] theorem rename_ids ξ x : rename ξ (ids x) = @ids tm _ (ξ x) := rfl
@[simp] theorem rename_lam ξ a m : rename ξ (tm.lam a m) = tm.lam a (rename (upren ξ) m) := rfl
@[simp] theorem rename_app ξ m n : rename ξ (tm.app m n) = tm.app (rename ξ m) (rename ξ n) := rfl
@[simp] theorem rename_unit ξ : rename ξ (tm.unit) = tm.unit := rfl

def tm.subst (σ : Nat -> tm) (m : tm) : tm :=
  match m with
  | var x => σ x
  | lam a m => lam a (subst (up σ) m)
  | app m n => app (subst σ m) (subst σ n)
  | unit => unit

instance : Subst tm where
  subst := tm.subst

@[simp] theorem subst_ids (σ : Nat -> tm) x : subst σ (ids x) = σ x := by rfl
@[simp] theorem subst_lam σ a m : subst σ (tm.lam a m) = tm.lam a (subst (up σ) m) := by rfl
@[simp] theorem subst_app σ m n : subst σ (tm.app m n) = tm.app (subst σ m) (subst σ n) := by rfl
@[simp] theorem subst_unit σ : subst σ tm.unit = tm.unit := rfl

theorem up_upren (ξ : Nat -> Nat) :
  @up tm _ _ (ren ξ) = ren (upren ξ) := by
  apply funext
  intro x
  cases x with
  | zero => simp [upren, up, ren, scons, funcomp]
  | succ => simp [upren, up, ren, scons, funcomp]

theorem up_upren_n (ξ : Nat -> Nat) (n : Nat) :
  @upn tm _ _ n (ren ξ ) = ren (n.repeat upren ξ) := by
  induction n generalizing ξ with
  | zero => simp [upn, Nat.repeat]
  | succ n ih =>
    simp[upn, Nat.repeat];
    rw [<-up_upren]
    rw [<-ih, <-upn]

@[simp] theorem rename_subst ξ (m : tm) : rename ξ m = m.[ren ξ] := by
  induction m generalizing ξ with
  | var x => simp [ren, funcomp]
  | lam a m ih =>
    simp[up_upren]; rw[ih]
  | app m n ihm ihn =>
    simp
    constructor
    . apply ihm
    . apply ihn
  | _ => simp

@[simp] theorem up_shift (σ : Nat -> tm) :
  up σ = ids 0 .: (σ @@ shift) := by
  simp [up, scomp]
  apply funext
  intro x
  cases x with
  | zero => simp[scons]
  | succ x =>
    simp [scons, funcomp]
    simp [rename_subst, shift]

open Lean Elab Macro
syntax "asimp" : tactic
syntax "asimp" "at" ident : tactic
macro_rules
| `(tactic| asimp) =>
  `(tactic| simp; repeat rw [<-up_shift])
| `(tactic| asimp at $x:ident) =>
  `(tactic| simp at $x:ident; repeat rw [<-up_shift] at $x:ident)

@[simp] theorem ids_comp (σ : Nat -> tm) : ids @@ σ = σ := by rfl
@[simp] theorem ids_shift : (@ids tm _ 0) .: shift = ids := by
  apply funext
  intro x
  cases x with
  | zero => simp[scons]
  | succ x => simp[scons, shift, ren, funcomp]

@[simp] theorem shift_scomp (m : tm) (σ : Nat -> tm) :
  shift @@ (m .: σ) = σ := by
  apply funext
  intro x
  simp[shift, ren]
  simp[funcomp, scomp, scons]

@[simp] theorem ids0_scons (σ : Nat -> tm) :
  (ids 0).[σ] .: (shift @@ σ) = σ := by
  apply funext
  intro x
  simp[scons]
  cases x with
  | zero => simp
  | succ => simp[scomp, funcomp, shift, ren]

@[simp] theorem subst_id (m : tm) :
  m.[ids] = m := by
  induction m with
  | var x => simp
  | lam a m ih =>
    simp
    assumption
  | app m n ih1 ih2 =>
    simp
    constructor <;> assumption
  | unit => simp

@[simp] theorem comp_ids (σ : Nat -> tm) : σ @@ ids = σ := by
  apply funext
  intro x
  simp[scomp, funcomp]

@[simp] theorem scons_scomp m (σ τ : Nat -> tm) :
  (m .: σ) @@ τ = m.[τ] .: σ @@ τ := by
  apply funext
  intro x
  cases x with
  | zero => simp[scomp, funcomp, scons]
  | succ => simp[scomp, funcomp, scons]

theorem up_comp_ren_subst {T} [Ids T] [Rename T] (ξ : Nat -> Nat) (σ : Nat -> T) :
  up (ξ @@@ σ) = upren ξ @@@ up σ := by
  apply funext
  intro x
  cases x with
  | zero => rfl
  | succ n => simp [up, scons, upren, funcomp]

theorem ren_subst_comp ξ σ (m : tm) : m.[ren ξ].[σ] = m.[ξ @@@ σ] := by
  induction m generalizing ξ σ with
  | var x => rfl
  | lam a m ih =>
    simp [up_comp_ren_subst]
    rw [<- ih]
    simp [<- up_upren]
  | app m n ihm ihn =>
    simp; constructor
    . rw [<- ihm]
    . rw [<- ihn]
  | unit => simp

theorem up_comp_subst_ren (σ : Nat -> tm) (ξ : Nat -> Nat) :
  up (σ @@@ rename ξ) = up σ @@@ rename (upren ξ) := by
  apply funext
  intro x
  cases x with
  | zero => simp [ren, funcomp]
  | succ n =>
    simp [up, scons, funcomp]
    have h1 := ren_subst_comp Nat.succ (ren (upren ξ)) (σ n); simp at h1
    have h2 := ren_subst_comp ξ (ren Nat.succ) (σ n); simp at h2
    rw [h1, h2]; rfl

theorem subst_ren_comp σ ξ (m : tm) : m.[σ].[ren ξ] = m.[σ @@@ rename ξ] := by
  induction m generalizing σ ξ with
  | var x => simp
  | lam a m ih =>
    asimp;
    rw [up_upren]
    rw [ih]
    rw [<- up_comp_subst_ren]
  | app m n ihm ihn =>
    simp; constructor
    . rw [<- ihm]
    . rw [<- ihn]
  | unit => rfl

theorem up_comp (σ τ : Nat -> tm) : up (σ @@ τ) = up σ @@ up τ := by
  apply funext
  intro x
  cases x with
  | zero =>
    simp [up, scons, scomp, funcomp]
  | succ n =>
    simp [up, scons, scomp, funcomp]
    rw[<-up]
    have h1 := subst_ren_comp τ Nat.succ (σ n)
    have h2 := ren_subst_comp Nat.succ (up τ) (σ n)
    rw [h1, h2]
    rfl

@[simp] theorem subst_comp (σ τ : Nat -> tm) m : m.[σ].[τ] = m.[σ @@ τ] := by
  induction m generalizing σ τ with
  | var x => simp [scomp, funcomp]
  | lam a m ih =>
    asimp
    rw [ih]
    rw [up_comp]
  | app m n ihm ihn =>
    simp; constructor
    . apply ihm
    . apply ihn
  | unit => rfl

@[simp] theorem scomp_assoc (σ τ θ : Nat -> tm) :
  (σ @@ τ) @@ θ = σ @@ (τ @@ θ) := by
  apply funext
  intro x
  simp[scomp, funcomp]
