(set-logic QF_LRA)
(declare-fun s0 () Real)
(declare-fun s2 () Real)
(declare-fun m () Real)
(assert (>= m 0.0))
(assert
 (or
  (< (+ s2 (* m (- 10.0))) 0.0)
  (<=
   (+ (* (- 1.0) s0) (* m (- 10.0)))
   0.0)
  ))

(assert
 (or
  (< (+ (* s2 (- 4294967296.0)) 1.0 s0) 0.0)
  (< (* s2 (- 4294967296.0)) 0.0)
 ))
(check-sat)
(exit)
