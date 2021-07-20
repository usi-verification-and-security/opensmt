(set-logic QF_UF)

(set-info :status sat)
(declare-sort U 0)
(declare-fun Add (U) U)
(declare-fun b () Bool)
(declare-fun u () U)
(declare-fun t () U)
(declare-fun z () U)

(assert (= t (Add u)))
(assert (= b (not (= u z))))
(assert (not b))

(check-sat)
(exit)
