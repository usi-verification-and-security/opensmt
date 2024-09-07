(set-logic ALL)
(declare-fun a () (Array Int Int))
(assert (= 1 (select a 0)))
(check-sat)

