(set-option :produce-interpolants true)
(set-logic QF_LRA)
(push 1)
(push 1)
(assert false)
(check-sat)
(pop 1)
(check-sat)

