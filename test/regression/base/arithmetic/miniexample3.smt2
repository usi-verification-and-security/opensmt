(set-logic QF_LIA)
(declare-fun x () Int)
(declare-fun y () Int)
(define-fun uninterp_mul ((a Int) (b Int)) Int (+ (* a b) 10))
(assert (= (uninterp_mul y x) 30))
(check-sat)
(exit)
