(set-logic QF_LIA)
(set-info :status sat)
(declare-fun x () Int)
(declare-fun b () Bool)
(assert (or b (= x 5)))
(assert (or (not b) (= x 5)))
(assert (= 1 (mod x 2)))
(check-sat)