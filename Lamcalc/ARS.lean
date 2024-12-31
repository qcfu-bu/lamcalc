namespace ARS

section ars_def
set_option quotPrecheck false
notation:70 e1:70 " <=2 " e2:70 => (∀ {x y}, e1 x y -> e2 x y)

def Pred (T : Type) := T -> Prop
def Rel (T : Type) := T -> Pred T
attribute [reducible] Pred Rel

variable {T : Type} (e : Rel T)

inductive star (x : T) : T -> Prop where
| R : star x x
| SE {y z} : star x y -> e y z -> star x z

inductive conv (x : T) : T -> Prop where
| R : conv x x
| SE  {y z} : conv x y -> e y z -> conv x z
| SEi {y z} : conv x y -> e z y -> conv x z

def com (R S : Rel T) := ∀ {x y z}, R x y -> S x z -> ∃ u, S y u ∧ R z u
def joinable (R : Rel T) x y := ∃ z, R x z ∧ R y z
def diamond := ∀ {x y z}, e x y -> e x z -> ∃ u, e y u ∧ e z u
def confluent := ∀ {x y z}, star e x y -> star e x z -> joinable (star e) y z
def CR := ∀ {x y}, conv e x y -> joinable (star e) x y
end ars_def

section ars_lemmas
variable {T : Type} {e : Rel T}

theorem star.singleton {x y} : e x y -> star e x y := by
  intro h
  apply star.SE
  apply star.R
  assumption

theorem star.trans {y x z} : star e x y -> star e y z -> star e x z := by
  intros h1 h2
  induction h2 with
  | R => exact h1
  | SE _ rel ih => apply star.SE ih rel

theorem star.ES {x y z} : e x y -> star e y z -> star e x z := by
  intro h
  apply star.trans
  apply star.singleton
  assumption

theorem star.conv {x y} : star e x y -> conv e x y := by
  intro h
  induction h with
  | R => constructor
  | SE _ rel ih => apply conv.SE ih rel

theorem star.img {T1 T2} {f : T1 -> T2} {e1 e2} :
  (∀ {x y}, e1 x y -> star e2 (f x) (f y)) ->
  (∀ {x y}, star e1 x y -> star e2 (f x) (f y)) := by
  intros h1 x y h2
  induction h2 with
  | R => constructor
  | @SE y z _ rel ih => apply star.trans ih (h1 rel)

theorem star.hom {T1 T2} (f : T1 -> T2) {e1 e2} :
  (∀ {x y}, e1 x y -> e2 (f x) (f y)) ->
  (∀ {x y}, star e1 x y -> star e2 (f x) (f y)) := by
  intro h; apply star.img
  intros x y h0
  specialize h h0
  apply star.singleton h

theorem star.closure {T} {e1 e2 : Rel T} : e1 <=2 star e2 -> star e1 <=2 star e2 := by
  apply star.img

theorem star.monotone {T} {e1 e2 : Rel T} : e1 <=2 e2 -> star e1 <=2 star e2 := by
  intro h1; apply star.closure
  intros x y h2
  specialize h1 h2
  apply star.singleton h1

theorem conv.singleton {x y} : e x y -> conv e x y := by
  intro h; apply conv.SE conv.R h

theorem conv.singletoni {x y} : e y x -> conv e x y := by
  intro h; apply conv.SEi conv.R h

theorem conv.trans {y x z} : conv e x y -> conv e y z -> conv e x z := by
  intros h1 h2
  induction h2 with
  | R => exact h1
  | SE _ rel ih => apply conv.SE ih rel
  | SEi _ rel ih => apply conv.SEi ih rel

theorem conv.ES {x y z} : e x y -> conv e y z -> conv e x z := by
  intro h
  apply conv.trans
  apply conv.singleton
  assumption

theorem conv.ESi {x y z} : e y x -> conv e y z -> conv e x z := by
  intro h
  apply conv.trans
  apply conv.singletoni
  assumption

theorem conv.sym {x y} : conv e x y -> conv e y x := by
  intro h
  induction h with
  | R => constructor
  | SE _ rel ih => apply conv.ESi rel ih
  | SEi _ rel ih => apply conv.ES rel ih

theorem conv.join {x y z} : star e x y -> star e z y -> conv e x z := by
  intro h1 h2
  apply conv.trans
  apply star.conv h1
  apply conv.sym
  apply star.conv h2

theorem conv.img {T1 T2} {f : T1 -> T2} {e1 e2} :
  (∀ {x y}, e1 x y -> conv e2 (f x) (f y)) ->
  (∀ {x y}, conv e1 x y -> conv e2 (f x) (f y)) := by
  intros h1 x y h2
  induction h2 with
  | R => constructor
  | SE _ rel ih =>
    apply conv.trans ih (h1 rel)
  | SEi _ rel ih =>
    apply conv.trans ih
    apply conv.sym
    apply h1 rel

theorem conv.hom {T1 T2} (f : T1 -> T2) {e1 e2} :
  (∀ {x y}, e1 x y -> e2 (f x) (f y)) ->
  (∀ {x y}, conv e1 x y -> conv e2 (f x) (f y)) := by
  intro h; apply conv.img
  intros x y h0
  specialize h h0
  apply conv.singleton h

theorem confluent_cr : confluent e <-> CR e := by
  constructor
  . intro h1 x y h2
    induction h2 with
    | R =>
      exists x
      constructor <;> constructor
    | @SE y z _ rel ih =>
      rcases ih with ⟨u, ⟨h2, h3⟩⟩
      rcases h1 h3 (star.singleton rel) with ⟨v, ⟨h4, h5⟩⟩
      exists v; constructor
      . apply star.trans h2 h4
      . apply h5
    | @SEi y z _ rel ih =>
      rcases ih with ⟨u, ⟨h2, h3⟩⟩
      exists u; constructor
      . apply h2
      . apply star.ES rel h3
  . intro h x y z  h1 h2
    have h1 := star.conv h1
    have h2 := star.conv h2
    apply h
    apply conv.trans (conv.sym h1) h2

theorem com.strip {e1 e2 : Rel T} : com e1 e2 -> com (star e2) e1 := by
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
    rcases ih h2 with ⟨u, ⟨rel1, h3⟩⟩
    rcases h1 rel1 rel2 with ⟨v, ⟨rel2, rel1⟩⟩
    exists v; constructor
    . assumption
    . apply star.SE h3 rel2

theorem com.lift {e1 e2 : Rel T} : com e1 e2 -> com (star e1) (star e2) := by
  intro h
  have h := @com.strip _ e1 e2 h
  have h := @com.strip _ (star e2) e1 h
  assumption

theorem diamond_confluent : diamond e -> confluent e := by
  apply com.lift
end ars_lemmas
