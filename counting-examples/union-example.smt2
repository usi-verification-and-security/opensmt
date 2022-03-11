; Has 3'000'000 models

(set-option :count-models true)
(set-option :print-clauses-file "./counts.cnf")

(set-logic QF_BV)
(declare-fun rho_1 () (_ BitVec 32))
(declare-fun rho_2 () (_ BitVec 32))
(declare-fun phi_1 () Bool)
(declare-fun phi_2 () Bool)
(declare-fun fromId () (_ BitVec 32))
(declare-fun toId () (_ BitVec 32))

(declare-fun test () (_ BitVec 32))

(assert (= rho_1 fromId))
(assert (and (bvult #b00000000001011011100011010111111 rho_1) (bvult rho_1 #b00000000010110111000110110000001)))
(assert (= rho_2 toId))
(assert (and (bvult #b00000000001011011100011010111111 rho_2) (bvult rho_2 #b00000000010110111000110110000001)))
(assert (= phi_1 (bvult fromId #b00000000010110111000110110000000)))
(assert (= phi_2 (bvult toId #b00000000010110111000110110000000)))
(assert (and phi_1 phi_2))

(assert (or (= (! test :named v1) rho_1) (= test rho_2)))

(count-models v1)
(exit)
