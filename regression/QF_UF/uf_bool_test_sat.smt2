(set-logic QF_UF)
(set-info :status sat)
(declare-fun p (Bool) Bool)
(declare-fun a () Bool)
(declare-fun b () Bool)
(declare-fun c () Bool)
(assert (or (not c) (= (p a) true)))
(assert (or (not c) (= (p b) false)))
(assert (or c (= a b)))
(assert (or (not c) (= a b)))
(check-sat)


