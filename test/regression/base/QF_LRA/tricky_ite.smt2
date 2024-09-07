(set-logic QF_LRA)
(declare-fun x8 () Real)
(declare-fun x7 () Real)
(declare-fun x_1 () Bool)
(assert
 (and
  (or (not (= x8 0)) x_1)
  (or (and (= x8 0) (= x7 (ite (not x_1) x8 1)))
      (and (= x8 1) (= x7 x8)))
  (= x7 0))
)
(check-sat)
(exit)
