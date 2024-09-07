(set-option :produce-interpolants 1)
(set-logic QF_LIA)
(declare-fun x () Int)
(declare-fun y () Int)
;not (0 <= x - y) with label A; not (1 <= y - x) with label B
(assert (! (not (<= 0 (- x y))) :named A))
(assert (! (not (<= 1 (- y x))) :named B))
(check-sat)
(get-interpolants A B)
