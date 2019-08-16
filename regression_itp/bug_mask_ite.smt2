(set-logic QF_LRA)
(set-option :produce-interpolants 1)

(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun z () Real)

(assert (! (= z (ite (<= 0 x) x y))
:named a))

(assert (! (not (or (< y 0) (<= 0 z)))
:named b))

(check-sat)
(get-interpolants a b)
(exit)


