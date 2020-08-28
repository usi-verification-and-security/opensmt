(set-logic QF_LIA)
(declare-fun v () Int)
(set-info :status sat)
(assert
 (=
  (ite
   (= (ite (= v 0) 1 0) 0)
   (ite (= v 0) 1 0)
   (ite (= (ite (= v 0) 1 0) 0) 1 0))
  0
))
(check-sat)
(exit)
