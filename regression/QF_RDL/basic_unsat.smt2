(set-logic QF_RDL)
(declare-fun a () Real)
(declare-fun b () Real)
(set-info :status unsat)
(assert (and (< a b) (< b a)))
(check-sat)
(exit)
