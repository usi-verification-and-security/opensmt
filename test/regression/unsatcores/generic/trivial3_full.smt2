(set-option :produce-unsat-cores true)
(set-option :print-cores-full true)
(set-logic QF_UF)
(declare-fun b1 () Bool)
(declare-fun b2 () Bool)
(assert (! b1 :named a1))
(assert (! b2 :named a2))
(assert (not b1))
(check-sat)
(get-unsat-core)
(exit)