(set-logic QF_UF)
(declare-fun uf7 (Bool Bool Bool Bool Bool Bool Bool) Bool)
(declare-fun v0 () Bool)
(declare-fun v2 () Bool)
(declare-fun v7 () Bool)
(declare-fun v11 () Bool)
(declare-fun v13 () Bool)
(declare-fun v16 () Bool)
(declare-fun v17 () Bool)
(declare-fun v19 () Bool)
(assert (uf7 v2 v19 (= v11 (not v17)) v13 (=> v16 v0) v7 v17))
(check-sat)
(assert v16)
(check-sat)
