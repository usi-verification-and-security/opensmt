(set-logic QF_LRA)
(declare-fun x () Real)
(assert (and (= x 0) (or (> x 0) (<= x 0))))
(check-sat)
