(set-logic QF_UF)
(set-info :status unsat)
(declare-fun p (Bool) Bool)
(declare-fun a () Bool)
(declare-fun b () Bool)
(declare-fun c () Bool)
(assert (= (p a) true))
(assert (= (p b) false))
(assert (or c (= a b)))
(assert (or (not c) (= a b)))
(check-sat)


