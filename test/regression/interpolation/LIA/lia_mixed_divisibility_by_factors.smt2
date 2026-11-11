; Mixed LIA interpolation: x divisible by 2 and 3 (A) vs. x not divisible by 6 (B); goes through
; FarkasInterpolator::splitMixedLiteral and LASolver::resolveMixed.
(set-option :produce-interpolants 1)
(set-logic QF_LIA)
(declare-fun x () Int)
(assert (!(and (= (mod x 2) 0) (= (mod x 3) 0)):named a))
(assert (!(not (= (mod x 6) 0)):named b))
(check-sat)
(get-interpolants a b)
(exit)
