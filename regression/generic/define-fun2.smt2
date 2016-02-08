(set-logic QF_LRA)
(declare-fun a () Real)
(declare-fun b () Real)

(define-fun foo () Real
    (+ a b 1))

(assert (> foo foo))

(check-sat)

