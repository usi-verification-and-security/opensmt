(set-logic QF_LRA)
(set-option :produce-interpolants 1)
(declare-fun b () Bool)
(assert (!
b
 :named p1))

(push 1)

(assert (! 
(not b)
 :named p2))
(check-sat)
(get-interpolants p1 p2)
