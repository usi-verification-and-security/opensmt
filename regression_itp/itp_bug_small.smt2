(set-logic QF_LRA)
(set-option :produce-interpolants 1)
;(set-option :certify-interpolants 2)
(declare-fun x () Bool)

(assert (!
(not x)
:named a))


(assert (!
x
:named b))
(check-sat)
(get-interpolants a b)
(exit)
