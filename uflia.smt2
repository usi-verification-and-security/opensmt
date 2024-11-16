(set-logic QF_UFLIA)
(declare-fun uninterp_mul (Int Int) Int)
(define-fun axiom_mul_by_const ((a Int) (b Int)) Bool
 (= (uninterp_mul a b) (* a b)))
(declare-fun x () Int)
(assert (axiom_mul_by_const 100 x))
(check-sat)
