(set-logic QF_LIA)
(declare-fun x () Int)
(declare-fun y () Int)
(define-fun uninterp_mul ((a Int) (b Int)) Int (* a b))
(assert (= (uninterp_mul x y) 10))
(check-sat)
(exit)
