(set-logic QF_LIA)
(declare-fun b () Bool)
(set-info :status sat)
(assert
 (=
  (ite
   (= (ite b 1 0) 0)
   (ite b 1 0)
   (ite
    (= (ite b 1 0) 1)
    1
    0
   )
  )
  0
 )
)
(check-sat)
(exit)
