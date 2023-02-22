(set-option :produce-interpolants 1)
(set-option :certify-interpolants 1)
(set-option :picky true)
(set-option :picky_w 10)
(set-logic QF_LRA)

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


