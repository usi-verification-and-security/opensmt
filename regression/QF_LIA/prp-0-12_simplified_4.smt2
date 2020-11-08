(set-logic QF_LIA)
(declare-fun v0 () Int)
(declare-fun v2 () Int)
(set-info :status unsat)
(assert
 (=
  (ite
   (= v2 0)
   (ite (= v2 0) 0 1)
   (ite (=
    (ite (= v2 0) 1 0) 0)
    0
    1
    ))
  1
))
(check-sat)
(exit)
