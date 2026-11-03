; Mixed LIA interpolation: an even value between t and r (A) vs. an odd value between r and t (B).
; The interpolant needs the div-based (rule-la) combination in LASolver::resolveMixed.
(set-option :produce-interpolants 1)
(set-logic QF_LIA)
(declare-fun t () Int)
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun r () Int)
(assert (!(and (<= t (* 2 a)) (<= (* 2 a) r) ):named a))
(assert (!(and (<= r (+ (* 2 b) 1)) (<= (+ (* 2 b) 1) t)):named b))
(check-sat)
(get-interpolants a b)
(exit)
