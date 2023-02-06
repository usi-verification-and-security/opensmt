(set-logic QF_ALIA)
(declare-fun a () (Array Int Int))
(assert (<= 0 (select a 0)))
(check-sat)
