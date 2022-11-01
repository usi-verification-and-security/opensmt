(set-option :produce-interpolants true)
(set-logic QF_LIA)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(assert (! (<= (+ (* 4 x) (* 2 y)) 3) :named A))
(assert (! (>= (+ (* 8 x) (* 4 y)) 5) :named B))
;(assert (= x (* 2 y)))
;(assert (= x (+ (* 2 z) 1)))
(check-sat)
(get-interpolants A B)
