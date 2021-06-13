(set-logic QF_LRA)(set-option :produce-models true)(declare-fun X () Real)(assert (< 1 X)) (check-sat) (get-value (X))
