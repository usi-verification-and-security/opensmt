(set-logic QF_LIA)
(set-info :status sat)

(define-fun f1 ((A Bool)) Bool (not A))
(define-fun f2 ((A Int)) Int (+ A 1))

(declare-fun b () Bool)
(declare-fun x () Int)

(assert (and (f1 b) (> (f2 x) 0)))

(check-sat)
(exit)
