(set-logic QF_LRA)
(declare-fun v1 () Bool)
(declare-fun v4 () Bool)
(declare-fun v5 () Bool)
(assert v4)
(check-sat)
(assert v1)
(check-sat)
(declare-fun r12 () Real)
(assert (not v5))
(assert v5)
(check-sat)
(push 1)
(check-sat)
(pop 1)
(assert true)
(check-sat)
(push 1)
(assert (= 0.0 r12))
(check-sat)
(pop 1)
(assert true)
(check-sat)
(check-sat)
(push 1)
(check-sat)
(check-sat)
(check-sat)
(check-sat)
(check-sat)
(check-sat)
(check-sat)
(pop 1)
(check-sat)
