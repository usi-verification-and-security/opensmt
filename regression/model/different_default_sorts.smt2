(set-option :print-success false)
(set-option :produce-models true)
(set-logic QF_UF)
(declare-sort x4 0)
(declare-sort x1 0)
(declare-fun x2 () x1)
(declare-fun x6 (x4) x1)
(declare-fun x3 (x1) x4)
(declare-fun x5 () x4)
(assert (= (x3 x2) x5))
(assert (= (x6 x5) x2))
(check-sat)
(get-model)