(set-option :produce-interpolants true)
(set-option :certify-interpolants true)
(set-logic QF_UF)
(declare-fun x () Bool)
(assert (! x :named A))
(assert (! false :named B))
(check-sat)
(get-interpolants A B)
