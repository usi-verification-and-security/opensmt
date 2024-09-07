(set-option :produce-unsat-cores true)

(set-logic QF_UF)

(declare-const b1 Bool)
(declare-const b2 Bool)

(assert (! (and b1 b2) :named a1))
(assert (! (or b1 b2) :named a2))
(assert (! (xor b1 b2) :named a3))

(check-sat)
(get-unsat-core)
