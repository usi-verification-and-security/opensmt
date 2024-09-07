(set-logic QF_LRA)
(declare-fun t6 () Bool)
(declare-fun t7 () Bool)
(assert (or (not t6) (not t7)))

;(push 1)

(assert (and t7 t6))

(check-sat)
(exit)
