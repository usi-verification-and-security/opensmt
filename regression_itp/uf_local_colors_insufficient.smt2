(set-option :produce-interpolants true)
(set-option :certify-interpolants true)
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun f (U U) U)
(declare-fun P (U) Bool)
(declare-fun x () U)
(declare-fun y () U)

(declare-fun r1 () U)
(declare-fun r2 () U)
(declare-fun a1 () U)
(declare-fun a2 () U)
(declare-fun b1 () U)
(declare-fun b2 () U)

(assert (! (and (= r1 (f a1 b1)) (= r2 (f a2 b2)))
:named B))

(assert (! (and (P (f x y)) (= a1 x) (= b1 y) (= a2 x) (= b2 y) (not (= r1 r2)))
:named A))


(check-sat)
(get-interpolants A B)


