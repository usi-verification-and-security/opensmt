(set-logic QF_LRA)
(declare-fun v2 () Real)
(assert
 (<= 0.0
     (- v2
        (+ (+ 0.0
              (* (* (+ v2 2) 1001)
                 (/ 1 999)))
              0.0))))
(check-sat)
(exit)
