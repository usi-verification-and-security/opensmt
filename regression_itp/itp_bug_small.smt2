(set-option :produce-interpolants 1)
(set-logic QF_LRA)
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
