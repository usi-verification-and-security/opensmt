(set-logic QF_LRA)
(set-option :ghost-vars 1)
(declare-fun v17 () Real)
(declare-fun v23 () Real)
(declare-fun v31 () Real)
(declare-fun v26 () Real)
(declare-fun v16 () Real)
(assert
 (let
  ((?v_11 (= v26 v16))
   (?v_13 (= v23 v16)))
   (and
    (not (<= v26 0))
    (<= v23 v31)
    (or (or (= v26 v16) (= 0.0 v16)) (= v23 v16))
    (or (<= v17 v16) (and (<= v31 0.0) (<= 0.0 v17)))

    (or
     (or
      (not (<= v16 v31))
      (not (<= v17 v31)))
     (not (<= (- v17 v16) v31))))))
(check-sat)
(exit)
