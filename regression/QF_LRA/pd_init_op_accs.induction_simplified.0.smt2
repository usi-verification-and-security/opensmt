(set-logic QF_LRA)
(declare-fun v12 () Real)
(declare-fun v13 () Real)
(declare-fun x_37 () Bool)
(assert
(and (>= v13 0)
     (or (= v12 0) (= v12 2) (= v12 3))
     (or (not (= v13 0)) (not (= v12 0)))
     (= 0.0 (ite x_37 v13 2))))

; (and (and (or (not x_37) (= v13 .oite0)) (or x_37 (= 2 .oite0))) (and
; (<= 0 v13) (= 0 .oite0) (and (<= 0 v13) (or (= 0 v12) (= v12 2) (= v12
; 3)) (or (not (= 0 v12)) (not (= 0 v13))))))

; (and (<= 0 v13) (or (not (and (<= 0 v13) (<= 0 (* v13 -1)))) (not (and
; (<= 0 v12) (<= 0 (* v12 -1))))) (or (and (<= 0 v12) (<= 0 (* v12 -1)))
; (and (<= -3 (* v12 -1)) (<= 3 v12)) (and (<= -2 (* v12 -1)) (<= 2 v12)))
; (<= 0 .oite0) (<= 0 (* .oite0 -1)) (or x_37 (and (<= 2 .oite0) (<= -2 (*
; .oite0 -1)))) (or (not x_37) (and (<= 0 (+ .oite0 (* v13 -1))) (<= 0 (+
; v13 (* .oite0 -1))))))

(check-sat)
(exit)
