(set-option :produce-interpolants true)
(set-logic QF_UFLRA)
(declare-fun f (Real) Real)
(declare-fun x () Real)

(assert (!(not (= (f x) (f 0.0))) :named A))
(assert (!(and (>= x 0.0) (<= x 0.0)) :named B))

(check-sat)
(get-interpolants A B)
