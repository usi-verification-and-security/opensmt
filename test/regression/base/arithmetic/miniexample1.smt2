(set-logic QF_LRA)
(define-fun uninterp_div ((a Real) (b Real)) Real (* a b))
(assert (= (uninterp_div 0.25 2) 0.5))
(check-sat)
(exit)
