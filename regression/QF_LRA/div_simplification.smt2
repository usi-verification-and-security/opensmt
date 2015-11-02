(set-logic QF_LRA)
(assert (and false false false false false (or (= 0.0 (* (/ 0 3000) 0.0)) false) false))
(check-sat)
(exit)
