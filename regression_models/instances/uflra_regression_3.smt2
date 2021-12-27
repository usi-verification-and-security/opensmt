(set-logic QF_UFLRA)
(declare-fun x (Real) Real)
(assert (and (= 1.0 (x 1.0)) (> 0 (x 0.0)) (= 0.0 (x (- (x 0.0))))))
(check-sat)
