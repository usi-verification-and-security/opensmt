(set-logic QF_UF)
(declare-sort U 0)
(declare-fun x () Bool)
(declare-fun y () Bool)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun c () U)

(assert (and
  (or (not x) (= a b))
  (or (not x) (= a c))
  (or (not (and (= a b) (= a c))) (= b c))
  (or (= b c) y)))

(check-sat)
