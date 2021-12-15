(set-option :count-models true)
(set-option :print-clauses-file "./counts.cnf")
(set-logic QF_BV)
(set-info :smt-lib-version 2.0)

(declare-fun rho_1 () (_ BitVec 32))
(declare-fun rho_2 () (_ BitVec 32))

(declare-fun phi_1 () Bool)
(declare-fun phi_2 () Bool)

(declare-fun warehouseid () (_ BitVec 32))
(declare-fun warehouseidGV () (_ BitVec 32))

(assert (= rho_1 (! warehouseid :named v)))
(assert (= rho_2 warehouseidGV))

; 0 <= warehouseid <= 9
(assert
 (= phi_1 (bvult warehouseid #b00000000000000000000000000001010)))

; 0 <= warehouseidGV <= 9
(assert
 (= phi_2 (bvult warehouseidGV #b00000000000000000000000000001010)))

(assert (and (= rho_1 rho_2) (and phi_1 phi_2)))

(count-models v)
;(check-sat)
(exit)
