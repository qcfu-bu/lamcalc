namespace ARS

section ars_def
set_option quotPrecheck false
notation:70 e1:70 " <=2 " e2:70 => (∀ {x y}, e1 x y -> e2 x y)

def Pred (T : Type) := T -> Prop
def Rel (T : Type) := T -> Pred T
attribute [reducible] Pred Rel

variable {T : Type} (e : Rel T)

inductive Star (x : T) : T -> Prop where
  | R  : Star x x
  | SE : Star x y -> e y z -> Star x z

inductive Conv (x : T) : T -> Prop where
  | R   : Conv x x
  | SE  : Conv x y -> e y z -> Conv x z
  | SEi : Conv x y -> e z y -> Conv x z

def Com (R S : Rel T) := ∀ {x y z}, R x y -> S x z -> ∃ u, S y u ∧ R z u
def Joinable (R : Rel T) x y := ∃ z, R x z ∧ R y z
def Diamond := ∀ {x y z}, e x y -> e x z -> ∃ u, e y u ∧ e z u
def Confluent := ∀ {x y z}, Star e x y -> Star e x z -> Joinable (Star e) y z
def CR := ∀ {x y}, Conv e x y -> Joinable (Star e) x y
end ars_def

section ars_lemmas
variable {T : Type} {e : Rel T}

theorem Star.singleton {x y} : e x y -> Star e x y := by
  intro h
  apply Star.SE
  apply Star.R
  assumption

theorem Star.trans {y x z} : Star e x y -> Star e y z -> Star e x z := by
  intros h1 h2
  induction h2 with
  | R => exact h1
  | SE _ rel ih => apply Star.SE ih rel

theorem Star.ES {x y z} : e x y -> Star e y z -> Star e x z := by
  intro h
  apply Star.trans
  apply Star.singleton
  assumption

theorem Star.Conv {x y} : Star e x y -> Conv e x y := by
  intro h
  induction h with
  | R => constructor
  | SE _ rel ih => apply Conv.SE ih rel

theorem Star.img {T1 T2} {f : T1 -> T2} {e1 e2} :
    (∀ {x y}, e1 x y -> Star e2 (f x) (f y)) ->
    (∀ {x y}, Star e1 x y -> Star e2 (f x) (f y)) := by
  intros h1 x y h2
  induction h2 with
  | R => constructor
  | @SE y z _ rel ih => apply Star.trans ih (h1 rel)

theorem Star.hom {T1 T2} (f : T1 -> T2) {e1 e2} :
    (∀ {x y}, e1 x y -> e2 (f x) (f y)) ->
    (∀ {x y}, Star e1 x y -> Star e2 (f x) (f y)) := by
  intro h; apply Star.img
  intros x y h0
  specialize h h0
  apply Star.singleton h

theorem Star.closure {T} {e1 e2 : Rel T} : e1 <=2 Star e2 -> Star e1 <=2 Star e2 := by
  apply Star.img

theorem Star.monotone {T} {e1 e2 : Rel T} : e1 <=2 e2 -> Star e1 <=2 Star e2 := by
  intro h1; apply Star.closure
  intros x y h2
  specialize h1 h2
  apply Star.singleton h1

theorem Conv.singleton {x y} : e x y -> Conv e x y := by
  intro h; apply Conv.SE Conv.R h

theorem Conv.singletoni {x y} : e y x -> Conv e x y := by
  intro h; apply Conv.SEi Conv.R h

theorem Conv.trans {y x z} : Conv e x y -> Conv e y z -> Conv e x z := by
  intros h1 h2
  induction h2 with
  | R => exact h1
  | SE _ rel ih => apply Conv.SE ih rel
  | SEi _ rel ih => apply Conv.SEi ih rel

theorem Conv.ES {x y z} : e x y -> Conv e y z -> Conv e x z := by
  intro h
  apply Conv.trans
  apply Conv.singleton
  assumption

theorem Conv.ESi {x y z} : e y x -> Conv e y z -> Conv e x z := by
  intro h
  apply Conv.trans
  apply Conv.singletoni
  assumption

theorem Conv.sym {x y} : Conv e x y -> Conv e y x := by
  intro h
  induction h with
  | R => constructor
  | SE _ rel ih => apply Conv.ESi rel ih
  | SEi _ rel ih => apply Conv.ES rel ih

theorem Conv.join {x y z} : Star e x y -> Star e z y -> Conv e x z := by
  intro h1 h2
  apply Conv.trans
  apply Star.Conv h1
  apply Conv.sym
  apply Star.Conv h2

theorem Conv.img {T1 T2} {f : T1 -> T2} {e1 e2} :
    (∀ {x y}, e1 x y -> Conv e2 (f x) (f y)) ->
    (∀ {x y}, Conv e1 x y -> Conv e2 (f x) (f y)) := by
  intros h1 x y h2
  induction h2 with
  | R => constructor
  | SE _ rel ih =>
    apply Conv.trans ih (h1 rel)
  | SEi _ rel ih =>
    apply Conv.trans ih
    apply Conv.sym
    apply h1 rel

theorem Conv.hom {T1 T2} (f : T1 -> T2) {e1 e2} :
    (∀ {x y}, e1 x y -> e2 (f x) (f y)) ->
    (∀ {x y}, Conv e1 x y -> Conv e2 (f x) (f y)) := by
  intro h; apply Conv.img
  intros x y h0
  specialize h h0
  apply Conv.singleton h

theorem Confluent.cr : Confluent e <-> CR e := by
  constructor
  . intro h1 x y h2
    induction h2 with
    | R =>
      exists x
      constructor <;> constructor
    | @SE y z _ rel ih =>
      rcases ih with ⟨u, h2, h3⟩
      rcases h1 h3 (Star.singleton rel) with ⟨v, h4, h5⟩
      exists v; constructor
      . apply Star.trans h2 h4
      . apply h5
    | @SEi y z _ rel ih =>
      rcases ih with ⟨u, h2, h3⟩
      exists u; constructor
      . apply h2
      . apply Star.ES rel h3
  . intro h x y z  h1 h2
    have h1 := Star.Conv h1
    have h2 := Star.Conv h2
    apply h
    apply Conv.trans (Conv.sym h1) h2

theorem Com.strip {e1 e2 : Rel T} : Com e1 e2 -> Com (Star e2) e1 := by
  intros h1 x y z h2
  induction h2 with
  | R =>
    intro h2
    exists z
    constructor
    . assumption
    . constructor
  | SE _ rel2 ih =>
    intro h2
    rcases ih h2 with ⟨u, rel1, h3⟩
    rcases h1 rel1 rel2 with ⟨v, rel2, rel1⟩
    exists v; constructor
    . assumption
    . apply Star.SE h3 rel2

theorem Com.lift {e1 e2 : Rel T} : Com e1 e2 -> Com (Star e1) (Star e2) := by
  intro h
  have h := @Com.strip _ e1 e2 h
  have h := @Com.strip _ (Star e2) e1 h
  assumption

theorem Diamond.confluent : Diamond e -> Confluent e := by
  apply Com.lift
end ars_lemmas
