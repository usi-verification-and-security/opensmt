(set-logic QF_UF)
(declare-sort U 0)
(declare-fun c1 () U)
(declare-fun c2 () U)
(declare-fun c3 () U)
(assert (distinct c1 c2 c3))
(assert (= c2 c3))
(check-sat)