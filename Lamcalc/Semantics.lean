import Lamcalc.Syntax

@[aesop safe [constructors, cases]]
inductive pstep : tm -> tm -> Prop where
| pstep_var x :
  pstep (ids x) (ids x)
| pstep_lam a {m m'} :
  pstep m m' ->
  pstep (tm.lam a m) (tm.lam a m')
| pstep_app {m m' n n'} :
  pstep m m' ->
  pstep n n' ->
  pstep (tm.app m n) (tm.app m' n')
| pstep_beta a {m m' n n'} :
  pstep m m' ->
  pstep n n' ->
  pstep (tm.app (tm.lam a m) n) (m'.[n'/])
| pstep_unit :
  pstep tm.unit tm.unit

infix:50 " ≈> " => pstep
