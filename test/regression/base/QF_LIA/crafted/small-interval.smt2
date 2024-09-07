(set-logic QF_LIA)
(declare-fun x () Int)
(assert (and (> x 0) (< x 1)))
(check-sat)
