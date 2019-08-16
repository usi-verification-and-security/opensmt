(set-logic QF_UF)
(set-option :produce-interpolants 1)
;(set-option :certify-interpolants 2)
(declare-sort U 0)
(declare-fun e () U)
(declare-fun f () U)
(declare-fun g () U)
(declare-const c () U)
(declare-const d () U)
(assert (!
(= e c)
:named a))


(assert (!
(and (= f d) (= e f))
:named b))
(check-sat)
(get-interpolants a b)
(exit)
