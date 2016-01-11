(set-logic QF_UF)
(declare-sort U 0)
(declare-fun z1 () U)
(declare-fun z2 () U)
(declare-fun z3 () U)
(declare-fun z4 () U)
(declare-fun w1 () U)
(declare-fun w2 () U)
(declare-fun w3 () U)
(declare-fun w4 () U)
(assert (not
         (or
          (not
           (and (= w1 w3) (= w4 w2)))
          (= z1 z2))))
(assert (and
         (not (= z3 z4))
         (or
          (not
           (and (= w1 w3) (= w4 w2)))
          (= z1 z2))))
(check-sat)

