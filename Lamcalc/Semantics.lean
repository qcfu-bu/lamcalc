import Lamcalc.Syntax
import Lamcalc.ARS

@[aesop safe [constructors, cases]]
inductive step : tm -> tm -> Prop where
| step_lam a {m m'} :
  step m m' ->
  step (.lam a m) (.lam a m')
| step_appM {m m' n} :
  step m m' ->
  step (.app m n) (.app m' n)
| step_appN {m n n'} :
  step n n' ->
  step (.app m n) (.app m n')
| step_beta a {m n} :
  step (.app (.lam a m) n) (m.[n/])

infix:50 " ~> " => step
infix:50 " ~>* " => ARS.star step
infix:50 " === " => ARS.conv step
