(set-option :produce-interpolants true)
(set-logic QF_UF)
(declare-fun a () Bool)
(declare-fun b () Bool)
(declare-fun c () Bool)
(declare-fun d () Bool)
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
(get-interpolants (and p1 p2) p3)


(pop 1)

(assert (!
(or (not c) d)
 :named p4))

(push 1)

(assert (!
(not d)
 :named p5))

(check-sat)
(get-interpolants (and p1 p2 p4) p5)
