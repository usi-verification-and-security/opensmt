(set-logic QF_LIA)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun a () Bool)

(assert (= (* 3 x) (* 4 y)))
(assert (=> a (= x 1)))
(assert (=> (not a) (= x 1)))
(check-sat)
