(set-logic QF_UF)
(declare-sort U 0)
(declare-fun p12 (U U) Bool)
(declare-fun p13 (U U) Bool)
(declare-fun f1 (U U) U)
(declare-fun c_1 () U)
(declare-fun c_2 () U)
(assert

 (let ((?v_140 (p12 c_2 c_2)))
 (let ((?v_190 (p13 c_2 c_2)))
 (let ((?v_129 (f1 c_2 c_1)))

 (and (not (p12 c_2 ?v_129)) ?v_140 ?v_190 (= ?v_129 c_2) )))))

(check-sat)
(exit)
