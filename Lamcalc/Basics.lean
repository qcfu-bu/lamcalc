import Lamcalc.Attr

-------------------------------------------------------------------------------------------------

section Definitions

abbrev Var := Nat

class Ids (T : Type) where
  ids : Var -> T

class Rename (T : Type) where
  rename : (Var -> Var) -> T -> T

class Subst (T : Type) where
  subst : (Var -> T) -> T -> T

export Ids (ids)
export Rename (rename)
export Subst (subst)

@[asimp]def scons {T} (s : T) (σ : Var -> T) : Var -> T
  | 0 => s
  | x+1 => σ x

@[asimp]def funcomp {A B C} (f : A -> B) (g : B -> C) : A -> C :=
  fun x => g (f x)

def scomp {T} [Subst T] (f g : Var -> T) : Var -> T :=
  funcomp f (subst g)

infixl:56 " >>> " => funcomp
infixl:56 " >> " => scomp
infixr:55 " .: " => scons
notation:max s:2 ".[" σ:2 "]" => subst σ s
notation:max s:2 ".[" t:2 "/]" => subst (t .: ids) s

def ren {T} [Ids T] (ξ : Var -> Var) : Var -> T :=
  ξ >>> ids

def shift {T} [Ids T] : Var -> T :=
  ren Nat.succ

def upren (ξ : Var -> Var) : Var -> Var :=
  0 .: ξ >>> Nat.succ

def up {T} [Ids T] [Rename T] (σ : Var -> T) : Var -> T :=
  ids 0 .: (σ >>> rename Nat.succ)

def upn {T} [Ids T] [Rename T] (n : Var) : (Var -> T) -> Var -> T :=
  n.repeat up

@[asimp]theorem scomp0 {T} [Subst T] (f g : Var -> T) (x : Var) :
  (f >> g) x = (f x).[g] := by rfl
@[asimp]theorem scons0 {T} (s : T) (σ : Var -> T) : (s .: σ) 0 = s := by rfl
@[asimp]theorem scons1 {T} (s : T) (σ : Var -> T) (x : Var) : (s .: σ) x.succ = σ x := by rfl
@[asimp]theorem ren0 {T} [Ids T] (x : Var) (ξ : Var -> Var) : ren ξ x = @ids T _ (ξ x) := by rfl
@[asimp]theorem upren0 (ξ : Var -> Var) : upren ξ 0 = 0 := by rfl
@[asimp]theorem upren1 (ξ : Var -> Var) : upren ξ (n + 1) = (ξ >>> Nat.succ) n := by
  simp[upren, scons]
@[asimp]theorem up0 {T} [Ids T] [Rename T] (σ : Var -> T) : up σ 0 = ids 0 := by rfl
@[asimp]theorem up1 {T} [Ids T] [Rename T] (σ : Var -> T) : up σ (n + 1) = rename Nat.succ (σ n) := by rfl
@[asimp]theorem upn0 {T} [Ids T] [Rename T] (σ : Var -> T) : upn 0 σ = σ := by rfl
@[asimp]theorem upn1 {T} [Ids T] [Rename T] (n : Var) σ : @upn T _ _ (n + 1) σ = up (upn n σ) := by
  simp[upn, Nat.repeat]

@[asimp]theorem id_comp (f : A -> B) : id >>> f = f := by rfl
@[asimp]theorem comp_id (f : A -> B) : f >>> id = f := by rfl
@[asimp]theorem comp_assoc (f : A -> B) (g : B -> C) (h : C -> D) :
  (f >>> g) >>> h = f >>> (g >>> h) := by rfl

@[asimp]theorem lift0 : (.+0) = id := by rfl
@[asimp]theorem lift_scons x (f : Var -> T) (n : Var) :
  (.+n.succ) >>> (x .: f) = (.+n) >>> f := by
  funext x0; simp[scons, asimp]

section Definitions

-------------------------------------------------------------------------------------------------

section Lemmas

class SubstLemmas (T : Type) [Ids T] [Rename T] [Subst T] where
  rename_subst (ξ : Var -> Var) (m : T) : rename ξ m = m.[ren ξ]
  subst_id (m : T) : m.[ids] = m
  id_subst (σ : Var -> T) (x : Var) : (ids x).[σ] = σ x
  subst_comp (σ τ : Var -> T) (s : T) : s.[σ].[τ] = s.[σ >> τ]

set_option linter.unusedSectionVars false
variable {T : Type} [Ids T] [Rename T] [Subst T] [lemmas: SubstLemmas T]

@[asimp]theorem rename_subst :
  ∀ (ξ : Var -> Var) (m : T), rename ξ m = m.[ren ξ] := lemmas.rename_subst

@[asimp]theorem subst_id :
  ∀ (m : T), m.[ids] = m := lemmas.subst_id

@[asimp]theorem id_subst :
  ∀ (σ : Var -> T) (x : Var), (ids x).[σ] = σ x := lemmas.id_subst

@[asimp]theorem subst_comp :
  ∀ (σ τ : Var -> T) (s : T), s.[σ].[τ] = s.[σ >> τ] := lemmas.subst_comp

@[asimp]theorem up_shift (σ : Var -> T) :
  up σ = ids 0 .: (σ >> shift) := by
  simp[up, asimp]
  funext x
  cases x with
  | zero => simp[asimp]
  | succ => simp[shift, scomp, asimp]

@[asimp]theorem ids_comp (σ : Var -> T) : ids >> σ = σ := by
  funext x
  simp[scomp, asimp]

@[asimp]theorem ids_shift : (@ids T _ 0) .: shift = ids := by
  funext x
  cases x with
  | zero => simp[asimp]
  | succ => simp[scons, shift, ren, funcomp]

@[asimp]theorem shift_scomp (m : T) (σ : Var -> T) :
  shift >> (m .: σ) = σ := by
  funext x
  simp[scomp, shift, ren, asimp]

@[asimp]theorem ids0_scons (σ : Var -> T) :
  (ids 0).[σ] .: (shift >> σ) = σ := by
  funext x
  simp[scons]
  cases x with
  | zero => simp[asimp]
  | succ => simp[scomp, shift, ren, asimp]

@[asimp]theorem comp_ids (σ : Var -> T) : σ >> ids = σ := by
  funext x
  simp[scomp, funcomp, asimp]

@[asimp]theorem scons_scomp m (σ τ : Var -> T) :
  (m .: σ) >> τ = m.[τ] .: σ >> τ := by
  funext x
  cases x with
  | zero => simp[scomp, funcomp, scons]
  | succ => simp[scomp, funcomp, scons]

@[asimp]theorem scomp_assoc (σ τ θ : Var -> T) :
  (σ >> τ) >> θ = σ >> (τ >> θ) := by
  funext x
  simp[scomp, funcomp, asimp]

end Lemmas

syntax "asimp" ("[" ident,+ "]")? ("at" ident)? : tactic
macro_rules
| `(tactic| asimp) =>
  `(tactic| simp[asimp]; repeat rw [<-up_shift])
| `(tactic| asimp[$[$x:ident],*]) =>
  `(tactic| simp[$[$x:ident],*, asimp]; repeat rw [<-up_shift])
| `(tactic| asimp at $h:ident) =>
  `(tactic| simp[asimp] at $h:ident; repeat rw [<-up_shift] at $h:ident)
| `(tactic| asimp[$[$x:ident],*] at $h:ident) =>
  `(tactic| simp[$[$x:ident],*, asimp] at $h:ident; repeat rw [<-up_shift] at $h:ident)
