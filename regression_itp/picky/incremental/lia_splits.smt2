(set-option :produce-interpolants 1)
(set-option :picky true)
(set-option :picky_w 10)
(set-logic QF_LIA)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(declare-fun b () Bool)
(push 1)
(assert (!(<= 2 (+ (* 4 x) y)):named A))
(assert (!(<= 1 (- (* 3 y) x)):named B))
(assert (!(>= 2 (+ (* 3 y) x)):named C))
(check-sat)
(pop 1)
(assert (!(and (=> (>= y 1) (>= z 0)) (=> (<= y 0) (>= z 0))):named D))
(assert (!(and (<= z (- 5)) (=> b (<= y 0)) ):named E))
(check-sat)
(get-interpolants D E)
