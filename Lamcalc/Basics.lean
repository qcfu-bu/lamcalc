import Mathlib.Tactic

class Ids (t : Type) where
  ids : Nat -> t

class Rename (t : Type) where
  rename : (Nat -> Nat) -> t -> t

class Subst (t : Type) where
  subst : (Nat -> t) -> t -> t

export Ids (ids)
export Rename (rename)
export Subst (subst)

def scons {T} (s : T) (σ : Nat -> T) : Nat -> T
  | 0 => s
  | x+1 => σ x

def funcomp {A B C} (f : A -> B) (g : B -> C) : A -> C :=
  fun x => g (f x)

def scomp {T} [Subst T] (f g : Nat -> T) : Nat -> T :=
  funcomp f (subst g)

infixl:56 " @@@ " => funcomp
infixl:56 " @@ " => scomp
infixr:55 " .: " => scons
notation:max s:2 ".[" σ:2 "]" => subst σ s
notation:max s:2 ".[" t:2 "/]" => subst (t .: ids) s

def upren (ξ : Nat -> Nat) : Nat -> Nat :=
  0 .: ξ @@@ Nat.succ

def ren {T} [Ids T] (ξ : Nat -> Nat) : Nat -> T :=
  ξ @@@ ids

def up {T} [Ids T] [Rename T] (σ : Nat -> T) : Nat -> T :=
  ids 0 .: σ @@@ rename Nat.succ

def upn {T} [Ids T] [Rename T] (n : Nat) : (Nat -> T) -> Nat -> T :=
  up^[n]

lemma upren0 (ξ : Nat -> Nat) : upren ξ 0 = 0 := rfl
lemma up0 {T} [Ids T] [Rename T] (σ : Nat -> T) : up σ 0 = ids 0 := rfl
lemma upn0 {T} [Ids T] [Rename T] σ : @upn T _ _ 0 σ = σ := rfl
lemma upn1 {T} [Ids T] [Rename T] (n : Nat) σ : @upn T _ _ (n + 1) σ = upn n (up σ) := rfl
attribute [simp] upren0 up0 upn0 upn1

lemma id_comp {A B} (f : A -> B) : f @@@ id = f := by rfl
lemma comp_id {A B} (f : A -> B) : id @@@ f = f := by rfl
lemma comp_assoc {A B C D} (f : A -> B) (g : B -> C) (h : C -> D) :
  f @@@ (g @@@ h) = (f @@@ g) @@@ h := by rfl
