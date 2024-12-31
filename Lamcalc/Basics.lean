class Ids (t : Type) where
  ids : Nat -> t

class Rename (t : Type) where
  rename : (Nat -> Nat) -> t -> t

class Subst (t : Type) where
  subst : (Nat -> t) -> t -> t

export Ids (ids)
export Rename (rename)
export Subst (subst)

@[simp]
def scons {T} (s : T) (σ : Nat -> T) : Nat -> T
  | 0 => s
  | x+1 => σ x

@[simp]
def funcomp {A B C} (f : A -> B) (g : B -> C) : A -> C :=
  fun x => g (f x)

def scomp {T} [Subst T] (f g : Nat -> T) : Nat -> T :=
  funcomp f (subst g)

infixl:56 " @@@ " => funcomp
infixl:56 " @@ " => scomp
infixr:55 " .: " => scons
notation:max s:2 ".[" σ:2 "]" => subst σ s
notation:max s:2 ".[" t:2 "/]" => subst (t .: ids) s

def ren {T} [Ids T] (ξ : Nat -> Nat) : Nat -> T :=
  ξ @@@ ids

def shift {T} [Ids T] : Nat -> T :=
  ren Nat.succ

def upren (ξ : Nat -> Nat) : Nat -> Nat :=
  0 .: ξ @@@ Nat.succ

def up {T} [Ids T] [Rename T] (σ : Nat -> T) : Nat -> T :=
  ids 0 .: (σ @@@ rename Nat.succ)

def upn {T} [Ids T] [Rename T] (n : Nat) : (Nat -> T) -> Nat -> T :=
  n.repeat up

@[simp] theorem upren0 (ξ : Nat -> Nat) : upren ξ 0 = 0 := by rfl
@[simp] theorem up0 {T} [Ids T] [Rename T] (σ : Nat -> T) : up σ 0 = ids 0 := by rfl

@[simp] theorem up1 {T} [Ids T] [Rename T] (σ : Nat -> T) : up σ (n + 1) = rename Nat.succ (σ n) := by rfl
@[simp] theorem upn0 {T} [Ids T] [Rename T] σ : @upn T _ _ 0 σ = σ := by rfl
@[simp] theorem upn1 {T} [Ids T] [Rename T] (n : Nat) σ : @upn T _ _ (n + 1) σ = upn n (up σ) := by
  induction n with
  | zero => simp[upn, Nat.repeat]
  | succ n ih =>
    simp[upn, Nat.repeat]
    rw [<-upn]
    rw [<-ih]
    simp[upn, Nat.repeat]
