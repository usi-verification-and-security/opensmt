(set-option :produce-interpolants 1)
(set-option :picky true)
(set-option :picky_w 10)
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
(get-interpolants p1 (and p2 p3))


(pop 1)

(assert (!
(or (not c) d)
 :named p4))

(push 1)

(assert (!
(or (not c) (not d))
 :named p5))

(check-sat)
(get-interpolants p1 (and p2 p4 p5))
