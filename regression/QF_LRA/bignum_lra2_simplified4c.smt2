(set-logic QF_LRA)
(declare-fun v2 () Real)
(declare-fun v0 () Real)
(assert (and
  (or (= v2 1)
      (= v2 (/ 1 2)))
  (or (= v0 v2)
      (= v0 (* 2 v2)))
  (or (= 0.0 v0)
      (= 0.0 v2))))
(check-sat)
(exit)

;(and
; v2 = 0 or v0 = 0
; (or (and (<= 0 v2)
;          (<= 0 (* v2 -1)))
;     (and (<= 0 v0)
;          (<= 0 (* v0 -1))))
; v2 = 1/2*v0, i.e., v0 = 2*v2 or v0 = v2
; (or (and (<= 0 (+ v2 (* v0 -1/2)))
;          (<= 0 (+ (* v2 -1) (* 1/2 v0))))
;     (and (<= 0 (+ v0 (* v2 -1)))
;          (<= 0 (+ v2 (* v0 -1)))))
; v2 = 1/2 or v2 = 1
; (or (and (<= -1/2 (* v2 -1))
;          (<= 1/2 v2))
;     (and (<= 1 v2)
;          (<= -1 (* v2 -1)))))
