(set-logic QF_LRA)
(set-option :produce-interpolants 1)
(declare-fun a () Bool)
(declare-fun b () Bool)
(declare-fun c () Bool)
(assert (!
(and (or (not a) b)
     (or (not a) (not b))
)
 :named p1))

(push 1)

(assert (! 
(or a c)
 :named p2))
(check-sat)

(push 1)

(assert (! 
(or a (not c))
 :named p3))
(check-sat)

(get-interpolants p1 (and p2 p3))
