(set-logic QF_LRA)
(declare-fun v () Real)
(assert (and
  (or (= v (/ 1 100000)) (= v (/ 1 100002)))
  (or (= 0.0 v) (= 0.0 (* (/ 1 10003) v)))))
(check-sat)
(exit)
