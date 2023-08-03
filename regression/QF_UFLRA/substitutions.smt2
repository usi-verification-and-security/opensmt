(set-logic QF_UFLRA)
(declare-fun f (Real) Real)
(declare-fun x () Real)
(assert (= x (f x)))
(assert (= x (f (+ x 1.0))))
(assert (= (f x) (f (+ x 1.0))))
(check-sat)