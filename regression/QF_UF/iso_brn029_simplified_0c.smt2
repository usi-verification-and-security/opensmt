(set-logic QF_UF)
(declare-sort I 0)
(declare-fun op (I I) I)
(declare-fun e5 () I)
(declare-fun e4 () I)
(declare-fun e3 () I)
(declare-fun e2 () I)
(declare-fun e1 () I)
(declare-fun e0 () I)
(assert
  (and
   (= (op e1 e5) e0)
   (= (op e3 e5) e1)
   (= (op e4 e5) e2)
   (= (op e2 e5) e3)
   (= (op e5 e0) e4)
   (= (op e1 e5) e5)
))
(assert
 (and
  (not (= (op e1 e2) e1))
  (and
   (not (= (op e2 e0) e1))
   (or
    (not (= (op e2 e1) e1))
    (or
     (= (op e2 e1) e1)
     (not (= (op e1 e2) e1)))))))

(check-sat)
(exit)
