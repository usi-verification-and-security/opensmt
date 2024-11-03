(set-logic QF_LRA)
(declare-fun x () Real)
(declare-fun y () Real)
(define-fun uninterp_div ((a Real) (b Real)) Real (/ a b))
(assert (= (uninterp_div y 5) (+ 3 x)))
(check-sat)
(get-model)
(exit)
