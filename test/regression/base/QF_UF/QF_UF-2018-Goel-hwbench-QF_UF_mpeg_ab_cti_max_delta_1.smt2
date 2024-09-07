(set-logic QF_UF)
(declare-sort u1 0)
(declare-sort u2 0)
(declare-fun Concat (Bool u1) u2)

(declare-fun b0 () Bool)
(declare-fun b1 () Bool)
(declare-fun b2 () Bool)
(declare-fun b3 () Bool)
(declare-fun b4 () Bool)

(declare-fun n01 () u1)
(declare-fun n02 () u2)
(declare-fun n12 () u2)
(declare-fun w26 () u2)
(declare-fun w27 () u2)
(declare-fun w54 () u2)

(assert (= n02 w54))
(assert (not (= n02 w26)))
(assert (not (= n12 w27)))

(assert (= b4 (not b0)))

(assert (or (not b0) (not b1)))
(assert (or (not b3) (not b2)))

(assert (= b1 (not (= n02 w26))))
(assert (= b2 (not (= n12 w27))))

(assert (= w54 (Concat true n01)))
(assert (= w26 (Concat b4 n01)))
(assert (= w27 (Concat b3 n01)))

(check-sat)
(exit)
