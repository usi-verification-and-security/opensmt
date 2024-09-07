(set-logic QF_LRA)
(declare-fun v0 () Real)
(declare-fun v2 () Real)
(assert (and
  (= v0 v2)
  (or (= 0 v0) (= 0 v2))))
(check-sat)
(exit)
