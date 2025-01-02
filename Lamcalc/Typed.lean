import Lamcalc.Context
import Lamcalc.Confluence

mutual
inductive Typed : Ctx -> Tm -> Tm -> Prop where
  | srt Γ (i : Nat) :
    Wf Γ ->
    Typed Γ (Tm.srt i) (Tm.srt i.succ)
  | var Γ x a :
    Wf Γ ->
    Has Γ x a ->
    Typed Γ (.var x) a
  | pi Γ a b i1 i2 :
    Typed Γ a (Tm.srt i1) ->
    Typed (a :: Γ) b (Tm.srt i2) ->
    Typed Γ (Tm.pi a b) (Tm.srt (max i1 i2))
  | lam Γ a b m i :
    Typed Γ a (Tm.srt i) ->
    Typed (a :: Γ) m b ->
    Typed Γ (Tm.lam a m) (Tm.pi a b)
  | app Γ a b m n :
    Typed Γ m (Tm.pi a b) ->
    Typed Γ n a ->
    Typed Γ (Tm.app m n) (b.[n/])
  | conv Γ a b m :
    a === b ->
    Typed Γ m a ->
    Typed Γ b (Tm.srt i) ->
    Typed Γ m b

inductive Wf : Ctx -> Prop  where
  | nil : Wf []
  | cons Γ a i :
    Typed Γ a (.srt i) ->
    Wf (a :: Γ)
end

theorem typed_wf : Typed Γ m a -> Wf Γ  := by
  intro h
  induction h using @Typed.rec _ (fun _ _ => True) <;> trivial
