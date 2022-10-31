(set-option :produce-interpolants true)
(set-option :certify-interpolants true)
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
