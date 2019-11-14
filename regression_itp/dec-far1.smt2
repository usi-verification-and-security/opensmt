(set-logic QF_LRA)
(set-option :produce-interpolants true)
(set-option :interpolation-lra-algorithm 4) ; decomposed Farkas
(declare-fun x1 () Real)
(declare-fun x2 () Real)
(declare-fun x3 () Real)

(assert (!(<= 0 (+ x1  x2 ) ) :named A))
(assert (!(<= 0  (+ x1 x3)) :named B))
(assert (!(<= 0 ( * (- 1) x1 ) ) :named C))
(assert (!(<= 1 (+ (* (- 1) x2 ) ( * (- 1) x3 ))) :named D))
(check-sat)
(get-interpolants (and A B C) D)
(get-interpolants A (and B C D))
(get-interpolants B (and A C D))
(get-interpolants C (and A B D))



