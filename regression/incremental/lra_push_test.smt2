(set-logic QF_LRA)
(declare-fun r () Real)
(declare-fun b () Bool)
(check-sat)
(assert
 (or (not b) (= 0.0 r)))
(check-sat)
(exit)
