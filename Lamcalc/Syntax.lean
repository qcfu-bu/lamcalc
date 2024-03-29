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

@[simp]
lemma ids_var x : tm.var x = ids x := rfl

def tm.rename (ξ : Nat -> Nat) (m : tm) : tm :=
  match m with
  | var x => var (ξ x)
  | lam a m => lam a (rename (upren ξ) m)
  | app m n => app (rename ξ m) (rename ξ n)
  | unit => unit

instance : Rename tm where
  rename := tm.rename

lemma rename_ids ξ x : rename ξ (ids x) = @ids tm _ (ξ x) := rfl
lemma rename_lam ξ a m : rename ξ (tm.lam a m) = tm.lam a (rename (upren ξ) m) := rfl
lemma rename_app ξ m n : rename ξ (tm.app m n) = tm.app (rename ξ m) (rename ξ n) := rfl
lemma rename_unit ξ : rename ξ (tm.unit) = tm.unit := rfl
attribute [simp] rename_ids rename_lam rename_app rename_unit

def tm.subst (σ : Nat -> tm) (m : tm) : tm :=
  match m with
  | var x => σ x
  | lam a m => lam a (subst (up σ) m)
  | app m n => app (subst σ m) (subst σ n)
  | unit => unit

instance : Subst tm where
  subst := tm.subst

lemma subst_ids (σ : Nat -> tm) x : subst σ (ids x) = σ x := rfl
lemma subst_lam σ a m : subst σ (tm.lam a m) = tm.lam a (subst (up σ) m) := rfl
lemma subst_app σ m n : subst σ (tm.app m n) = tm.app (subst σ m) (subst σ n) := rfl
lemma subst_unit σ : subst σ tm.unit = tm.unit := rfl
attribute [simp] subst_ids subst_lam subst_app subst_unit

@[simp]
lemma up_upren (ξ : Nat -> Nat) :
  @up tm _ _ (ren ξ) = ren (upren ξ) := by
  apply funext
  intro x
  cases x with
  | zero => simp [upren, up, ren, scons, funcomp]
  | succ n => simp [upren, up, ren, scons, funcomp]

@[simp]
lemma up_upren_n (ξ : Nat -> Nat) (n : Nat) :
  @upn tm _ _ n (ren ξ ) = ren (upren^[n] ξ) := by
  induction n generalizing ξ with
  | zero => simp [upn]
  | succ n ih => simp; rw [ih]

@[simp]
lemma rename_subst ξ (m : tm) : rename ξ m = m.[ren ξ] := by
  induction m generalizing ξ with
  | var x => simp [ren, funcomp]
  | lam a m ih => simp; rw[ih]
  | app m n ihm ihn =>
    simp
    constructor
    . apply ihm
    . apply ihn
  | _ => simp

@[simp]
lemma up_id : @up tm _ _ ids = ids := by
  apply funext
  intro x
  cases x with
  | zero => simp [up, scons]
  | succ n => simp [up, scons, ren, funcomp]

@[simp]
lemma up_id_n n : @upn tm _ _ n ids = ids := by
  induction n with
  | zero => simp
  | succ n ihn => simp; exact ihn

@[simp]
lemma subst_id (m : tm) : m.[ids] = m := by
  induction m <;> simp
  case lam a m ih => exact ih
  case app m n ihm ihn =>
    constructor <;> aesop

@[simp]
lemma id_subst (σ : Nat -> tm) x : (ids x).[σ] = σ x := rfl

@[simp]
lemma up_comp_ren_subst {T} [Ids T] [Rename T] (ξ : Nat -> Nat) (σ : Nat -> T) :
  up (ξ @@@ σ) = upren ξ @@@ up σ := by
  apply funext
  intro x
  cases x with
  | zero => rfl
  | succ n => simp [up, scons, upren, funcomp]

@[simp]
lemma ren_subst_comp ξ σ (m : tm) : (rename ξ m).[σ] = m.[ξ @@@ σ] := by
  induction m generalizing ξ σ with
  | var x => rfl
  | lam a m ih => simp; rw [<- ih]; simp
  | app m n ihm ihn =>
    simp; constructor
    . rw [<- ihm]; simp
    . rw [<- ihn]; simp
  | unit => simp

@[simp]
lemma up_comp_subst_ren (σ : Nat -> tm) (ξ : Nat -> Nat) :
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

@[simp]
lemma subst_ren_comp σ ξ (m : tm) : rename ξ m.[σ] = m.[σ @@@ rename ξ] := by
  induction m generalizing σ ξ with
  | var x => rfl
  | lam a m ih => simp; rw [<- ih]; simp
  | app m n ihm ihn =>
    simp; constructor
    . rw [<- ihm]; simp
    . rw [<- ihn]; simp
  | unit => rfl

@[simp]
lemma up_comp (σ τ : Nat -> tm) : up (σ @@ τ) = up σ @@ up τ := by
  apply funext
  intro x
  cases x with
  | zero => simp [scomp, funcomp]
  | succ n =>
    simp [up, scons, scomp, funcomp]
    rw [<- up]
    have h1 := subst_ren_comp τ Nat.succ (σ n); simp at h1
    have h2 := ren_subst_comp Nat.succ (up τ) (σ n); simp at h2
    rw [h1, h2]; rfl

@[simp]
lemma subst_comp (σ τ : Nat -> tm) m : m.[σ].[τ] = m.[σ @@ τ] := by
  induction m generalizing σ τ with
  | var x => simp [scomp, funcomp]
  | lam a m ih => simp; rw [ih]
  | app m n ihm ihn =>
    simp; constructor
    . apply ihm
    . apply ihn
  | unit => rfl

@[simp]
lemma up_comp_subst (m : tm) (σ : Nat -> tm) :
  up σ @@ (m.[σ] .: ids) = (m .: ids) @@ σ := by
  apply funext; intro x
  cases x with
  | zero => simp [scomp, funcomp, scons]
  | succ n =>
    simp [scomp, funcomp, scons, up]
    have h : ren Nat.succ @@@ subst (m.[σ] .: ids) = ids := rfl
    rw [h]; simp
