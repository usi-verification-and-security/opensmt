(set-logic QF_LRA)
(set-option :produce-interpolants 1)
(declare-fun a () Real)
(assert (!
(and
(= a 0)
) :named p1))

(push 1)

(assert (! 
(and (= a 1) )
 :named p2))
(check-sat)
(get-interpolants p1 p2)

(pop 1)
(push 1)

(assert (!
(= a 2) :named p3))
(check-sat)
