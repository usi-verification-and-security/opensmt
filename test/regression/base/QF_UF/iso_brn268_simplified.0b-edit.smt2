(set-logic QF_UF)
(declare-sort I 0)
(declare-fun op (I I) I)
(declare-fun e4 () I)
(declare-fun e3 () I)
(declare-fun e2 () I)
(declare-fun e1 () I)
(declare-fun e0 () I)

(assert
  (or (or (or (or (and (= (op e3 e0) e3) (= (op e0 e3) e3))
                  (and (= (op e3 e1) e3) (= (op e1 e3) e3)))
                  (and (= (op e3 e2) e3) (= (op e2 e3) e3)))
                  (= (op e3 e3) e3))
                  (and (= (op e3 e4) e3) (= (op e4 e3) e3))))

(assert
  (or (or (and (= (op e2 e1) e2) (= (op e1 e2) e2))
          (or (or (or (or (and (= (op e3 e0) e3) (= (op e0 e3) e3))
                          (and (= (op e3 e1) e3) (= (op e1 e3) e3)))
                      (and (= (op e3 e2) e3) (= (op e2 e3) e3)))
                   (= (op e3 e3) e3))
              (and (= (op e3 e4) e3) (= (op e4 e3) e3))))
      (or (= (op e4 e1) e4) (= (op e3 e4) e4))))

(assert (and
   (= (op e2 e1) e0)
   (= (op e4 e4) e0)
   (= (op e3 e4) e1)
   (= (op e4 e1) e2)
   (not (= (op e1 e4) (op e4 e1)))
   (= (op e3 e3) e2)
   (= e1 (op e0 e0))
   (= e4 (op e2 e2))))

(check-sat)
(exit)
