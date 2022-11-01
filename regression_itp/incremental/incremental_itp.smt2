(set-option :produce-interpolants true)
(set-logic QF_LRA)
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
