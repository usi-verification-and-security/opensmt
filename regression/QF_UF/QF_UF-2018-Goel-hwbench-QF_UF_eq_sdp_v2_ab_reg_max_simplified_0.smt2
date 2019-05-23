(set-logic QF_UF)
(declare-fun Add (Bool Bool) Bool)
(declare-fun b () Bool)

(assert (not (Add false b)))
(check-sat)
(exit)
