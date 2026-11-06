; Mixed LIA interpolation: the conflict contains literals over A- and B-local auxiliary div/mod
; variables, so FarkasInterpolator::splitMixedLiteral and LASolver::resolveMixed are exercised.
(set-option :produce-interpolants 1)
(set-logic QF_LIA)
(declare-fun x () Int)
(assert (!(< (mod x 10) 5):named a))
(assert (!(> (mod x 20) 16):named b))
(check-sat)
(get-interpolants a b)
(exit)
