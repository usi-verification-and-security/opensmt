(set-logic QF_UF)
(declare-fun c () Bool)
(declare-fun d () Bool)
(declare-sort U 0)
(declare-fun f (Bool) U)

(assert
  (not (=
   (f (and (or c (not d)) (or (not c) d) (or (not c) (not d))))
   (f false))))

(check-sat)
