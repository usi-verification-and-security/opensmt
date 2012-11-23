(set-logic QF_UF)
(assert (or (let ((a true) (b (let ((a false)) (not a)))) (and a b)) (let ((a true)) (not a))))
(check-sat)
(exit)
