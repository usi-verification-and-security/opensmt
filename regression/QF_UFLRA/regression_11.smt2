(set-logic QF_UFLRA)
(set-info :status sat)
(declare-fun b () Real)
(declare-fun f (Real) Real)
(declare-fun a () Real)
(assert (or (= b 0.0) (and (= a b) (and (distinct a b) (= 0.0 (f b))))))
(check-sat)
