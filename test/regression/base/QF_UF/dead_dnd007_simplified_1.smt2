(set-logic QF_UF)
(declare-sort I 0)
(declare-fun op (I I) I)
(declare-fun e5 () I)
(declare-fun e4 () I)
(declare-fun e2 () I)
(declare-fun e1 () I)
(declare-fun e0 () I)
(assert
  (and (= (op e5 e2) e0)
       (= (op e5 e2) e2)
       (or (= (op e4 e0) e0)
           (= (op e4 e1) e0))
       (= (op e4 e1) e2)))
(check-sat)

(exit)

