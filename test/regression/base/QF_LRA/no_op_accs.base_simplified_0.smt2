(set-logic QF_LRA)
(declare-fun v_9 () Real)
(declare-fun x_4 () Bool)
(assert
 (and
  (not x_4)
  (= v_9 (ite (not x_4) (ite (<= 0.0 v_9) 0.0 0.0) 0.0))
  (or x_4 (= v_9 3))))
(check-sat)
(exit)
