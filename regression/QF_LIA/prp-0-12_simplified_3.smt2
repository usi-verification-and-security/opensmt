(set-logic QF_LIA)
(declare-fun v0 () Int)
(declare-fun v2 () Int)
(set-info :status sat)
(assert (= (ite (= v2 0) (ite (= v0 0) 1 0) (ite (= (ite (= v0 0) 1 0) 0) 1 0)) 0))
(check-sat)
(exit)
