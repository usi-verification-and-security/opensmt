(set-logic QF_UF)
(declare-fun uf4 (Bool Bool Bool Bool) Bool)
(declare-fun uf7 (Bool Bool Bool Bool Bool Bool Bool) Bool)
(declare-fun v3 () Bool)
(declare-fun v8 () Bool)
(declare-fun v11 () Bool)
(declare-fun v17 () Bool)
(check-sat)
(check-sat)
(assert (uf7 (=> v3 v11) true true true true v8 true))
(push 1)
(declare-sort S2 0)
(declare-sort S3 0)
(assert (= v3 v17))
(declare-sort S4 0)
(push 1)
(assert false)
(check-sat)
(pop 1)
(check-sat)
(check-sat)
(pop 1)
(push 1)
(declare-sort S2 0)
(assert (uf4 (= (=> v3 v11) (not v8)) true true true))
(check-sat)
(declare-sort S2 0)
(declare-sort S3 0)
(declare-sort S4 0)
(declare-sort S2 0)
(check-sat)
(pop 1)
(assert (=> v3 v11))
(check-sat)
