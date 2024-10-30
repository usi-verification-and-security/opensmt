(set-option :produce-unsat-cores true)

(set-logic QF_UF)

(declare-const b1 Bool)
(declare-const b2 Bool)

(assert (! b1 :named a1))
(assert (! b2 :named a2))
(assert (! (not b1) :named a3))
(assert (! (and b1 b2) :named x1))
(assert (! (or b1 b2) :named x2))
(assert (! (xor b1 b2) :named x3))

(check-sat)
(get-unsat-core)
