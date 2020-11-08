(set-logic QF_LIA)
(declare-fun v1 () Int)
(set-info :status unsat)
(assert (let (
 (?v_9 (= v1 0))
)
 (= v1 (ite (ite (= v1 0) true false) 1 0))))
(check-sat)
(exit)
