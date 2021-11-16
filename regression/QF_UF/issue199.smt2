(set-logic QF_UF)
(declare-fun uf5 (Bool Bool Bool Bool Bool) Bool)
(declare-fun uf6 (Bool Bool Bool Bool Bool Bool) Bool)
(declare-fun v0 () Bool)
(declare-fun v1 () Bool)
(declare-fun v2 () Bool)
(push 1)
(assert (=> v0 v1))
(push 1)
(assert (uf5 (distinct (=> v2 (=> v0 v1)) v0) true v2 (=> v2 (=> v0 v1)) true))
(check-sat)
(pop 1)
(assert false)
(check-sat)
(pop 1)
(assert (uf6 v0 v2 (=> v0 v1) true true v0))
(push 1)
(assert (xor v1 v0))
(check-sat)
