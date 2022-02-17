(set-logic QF_UFLIA)
(declare-fun x (Int) Int)
(assert (= 1 (+ (* 2 (x 1)) (x 0))))
(check-sat)
