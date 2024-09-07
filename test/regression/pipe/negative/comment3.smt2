(set-logic QF_LRA)(declare-fun X () Real)(assert (< 1 X)) (check-sat) (get-value (X)); comment)
(assert (> 0 X))(check-sat))
