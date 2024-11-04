(set-option :produce-unsat-cores true)
(set-option :print-cores-full true)

(set-logic QF_UF)

(declare-const b1 Bool)
(declare-const b2 Bool)

(assert (and b1 b2))
(assert (! (or b1 b2) :named x2))
(assert (xor b1 b2))
(assert (! b1 :named a1))
(assert b2)
(assert (! (not b1) :named a3))

(check-sat)
(get-unsat-core)
