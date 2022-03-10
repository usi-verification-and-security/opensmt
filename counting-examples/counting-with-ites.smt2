;if (b1) { x = rho_1; } else if (b2) { x = rho_2; } else {x = rho_3; }
(set-option :count-models true)
(set-logic QF_BV)

(declare-fun b1 () (_ BitVec 1))
(declare-fun b2 () (_ BitVec 1))
(declare-fun rho_1 () (_ BitVec 32))
(declare-fun rho_2 () (_ BitVec 32))
(declare-fun rho_3 () (_ BitVec 32))
(declare-fun x () (_ BitVec 32))

(assert (= (! x :named v1) (ite (= b1 #b1) rho_1 (ite (= b2 #b1) rho_2 rho_3))))
(count-models v1)

