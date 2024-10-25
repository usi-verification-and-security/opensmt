(set-option :produce-unsat-cores true)
(set-logic QF_LRA)
(declare-fun x1 () Real)
(declare-fun x2 () Real)
(declare-fun x3 () Real)
(declare-fun l1y1 () Real)
(declare-fun l1y2 () Real)
(declare-fun l1x1 () Real)
(declare-fun l1x2 () Real)
(declare-fun c1 () Real)
(declare-fun c2 () Real)

;; domains
(assert (>= x1 0))
(assert (<= x1 4))
(assert (>= x2 0))
(assert (<= x2 4))
(assert (>= x3 0))
(assert (<= x3 4))

;; NN
(assert (= l1y1 (+ (* 2 x1) x3)) )
(assert (= l1y2 (+ (- x1) x2 (- x3))) )
(assert (= l1x1 (ite (> l1y1 0) l1y1 0)) )
(assert (= l1x2 (ite (> l1y2 0) l1y2 0)) )
(assert (= c1 (+ l1x1 (* (- 4) l1x2))) )
(assert (= c2 (+ (- l1x1) (* 4 l1x2))) )

;; NOT class c1
(assert (< c1 c2))

;; sample (1,1,3)
(assert (! (= x1 1) :named s1))
(assert (! (= x2 1) :named s2))
(assert (! (= x3 3) :named s3))

(check-sat)
(get-unsat-core)
(exit)
