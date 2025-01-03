import Lamcalc.Context
import Lamcalc.Confluence

mutual
inductive Typed : Ctx -> Tm -> Tm -> Prop where
  | srt :
    Wf Γ ->
    Typed Γ (Tm.srt i) (Tm.srt i.succ)
  | var :
    Wf Γ ->
    Has Γ x a ->
    Typed Γ (.var x) a
  | pi :
    Typed Γ a (Tm.srt i) ->
    Typed (a :: Γ) b (Tm.srt j) ->
    Typed Γ (Tm.pi a b) (Tm.srt (max i j))
  | lam :
    Typed Γ a (Tm.srt i) ->
    Typed (a :: Γ) m b ->
    Typed Γ (Tm.lam a m) (Tm.pi a b)
  | app :
    Typed Γ m (Tm.pi a b) ->
    Typed Γ n a ->
    Typed Γ (Tm.app m n) (b.[n/])
  | conv :
    a === b ->
    Typed Γ m a ->
    Typed Γ b (Tm.srt i) ->
    Typed Γ m b

inductive Wf : Ctx -> Prop  where
  | nil : Wf []
  | cons :
    Wf Γ ->
    Typed Γ a (.srt i) ->
    Wf (a :: Γ)
end

-- Register non-mutual recursor as default.
@[induction_eliminator]
def Typed.rec_non_mutual {motive : ∀ Γ m a, Typed Γ m a -> Prop} :=
  Typed.rec (motive_1 := motive) (motive_2 := fun _ _ => True)

-- Register non-mutual recursor as default.
@[induction_eliminator]
def Wf.rec_non_mutual {motive : ∀ Γ, Wf Γ -> Prop} :=
  Wf.rec (motive_1 := fun _ _ _ _ => True) (motive_2 := motive)

theorem Typed.wf : Typed Γ m a -> Wf Γ  := by
  intro h
  induction h
  all_goals trivial
