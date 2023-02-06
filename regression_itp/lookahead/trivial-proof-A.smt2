(set-option :produce-interpolants 1)
(set-option :certify-interpolants 1)
(set-option :pure-lookahead true)
(set-logic QF_UF)
(declare-fun x () Bool)
(assert (! false :named A))
(assert (! x :named B))
(check-sat)
(get-interpolants A B)