import Lamcalc.Syntax
import Lamcalc.ARS
open ARS

inductive Step : Tm -> Tm -> Prop where
  | piA {a a'} b :
    Step a a' ->
    Step (.pi a b) (.pi a' b)
  | piB a {b b'} :
    Step b b' ->
    Step (.pi a b) (.pi a b')
  | lamA {a a'} m :
    Step a a' ->
    Step (.lam a m) (.lam a' m)
  | lamM a {m m'} :
    Step m m' ->
    Step (.lam a m) (.lam a m')
  | appM {m m'} n :
    Step m m' ->
    Step (.app m n) (.app m' n)
  | appN m {n n'} :
    Step n n' ->
    Step (.app m n) (.app m n')
  | beta a m n :
    Step (.app (.lam a m) n) (m.[n/])

@[reducible]def star_step := Star Step
@[reducible]def conv_step := Conv Step
infix:50 " ~> " => Step
infix:50 " ~>* " => star_step
infix:50 " === " => conv_step
