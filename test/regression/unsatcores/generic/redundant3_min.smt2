(set-option :produce-unsat-cores true)
(set-option :minimal-unsat-cores true)

(set-logic QF_UF)

(declare-const b1 Bool)
(declare-const b2 Bool)

(assert (and b1 b2))
(assert (or b1 b2))
(assert (xor b1 b2))
(assert (! b1 :named a1))
(assert (! b2 :named a2))
(assert (! (not b1) :named a3))

(check-sat)
(get-unsat-core)
