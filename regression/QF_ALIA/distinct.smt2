(set-logic QF_ALIA)
(set-info :status unsat)
(declare-fun a () (Array Int Int))
(declare-fun i () Int)
(assert (distinct i (select (store a i i) i)))
(check-sat)
