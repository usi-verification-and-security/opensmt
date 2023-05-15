(set-logic QF_LIA)

(define-fun state ((A Bool) (B Bool) (C Bool) (D Bool) (E Int) (F Int) (G Int)) Bool (or (or (or (or (or (or (or (and (and (and (= A true) (= B true)) (not (= D true))) (>= E 1)) (and (and (and (= A true) (= D true)) (and (not (= B true)) (not (= C true)))) (>= E 1))) (and (and (= A true) (and (not (= B true)) (not (= D true)))) (>= E 1))) (and (and (and (= B true) (= D true)) (and (not (= A true)) (not (= C true)))) (>= E 1))) (and (= B true) (and (and (not (= A true)) (not (= C true))) (not (= D true))))) (and (and (= B true) (and (not (= A true)) (not (= D true)))) (>= E 1))) (and (and (= D true) (and (and (not (= A true)) (not (= B true))) (not (= C true)))) (>= E 1))) (and (and (and (not (= A true)) (not (= B true))) (not (= D true))) (>= E 1))))

(declare-fun A ()  Bool)
(declare-fun B ()  Bool)
(declare-fun C ()  Int)
(declare-fun D ()  Int)
(declare-fun E ()  Int)
(declare-fun F ()  Bool)
(declare-fun G ()  Bool)

(assert
    (and
      (and (= A true) (not G) (not F) (not B))
      (not (state B A G F C D E))
    )
)

(check-sat)
(exit)
