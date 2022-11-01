(set-option :produce-interpolants true)
(set-option :certify-interpolants true)
(set-logic QF_LRA)
(set-option :interpolation-lra-algorithm 11) ; decomposed Farkas
(declare-fun x1 () Real)
(declare-fun x2 () Real)
(declare-fun x3 () Real)
(declare-fun x4 () Real)
(declare-fun x5 () Real)

(assert (!(and (<= 0 (+ x1  x2 ))  (<= 0  (+ (- x1) x3)) (<= 0 (+ x1 x4)) (<= 0 (+ (- x1) x5)) ) :named A))
(assert (!(<= 1 (+ (* (- 1) x2 ) ( * (- 1) x3 )  (* (- 1) x4 ) (* (- 1) x5 ))) :named B))
(check-sat)
(get-interpolants A B)



