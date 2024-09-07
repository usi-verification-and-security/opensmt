(set-logic QF_LRA)
(declare-fun _substvar_4_ () Real)
(declare-fun _substvar_7_ () Real)
(declare-fun _substvar_9_ () Real)
(declare-fun _substvar_20_ () Real)
(declare-fun _substvar_21_ () Real)
(declare-fun _substvar_22_ () Real)
(declare-fun _substvar_23_ () Real)
(declare-fun motzkin_1639_2 () Real)
(declare-fun motzkin_1639_3 () Real)
(declare-fun motzkin_1639_4 () Real)
(declare-fun motzkin_1639_5 () Real)
(declare-fun motzkin_1640_3 () Real)
(declare-fun motzkin_1640_4 () Real)
(declare-fun motzkin_1640_6 () Real)
(declare-fun motzkin_1651_2 () Real)
(declare-fun motzkin_1651_3 () Real)
(declare-fun motzkin_1652_0 () Real)
(declare-fun motzkin_1652_2 () Real)
(declare-fun motzkin_1652_3 () Real)

(assert (>= _substvar_23_ 0.0))
(assert (>= motzkin_1639_3 0.0))
(assert
 (or
  (and
   (= (+ _substvar_20_ motzkin_1639_4) 0.0)
   (= (+ motzkin_1639_2 motzkin_1639_3) 0.0)
   (= (+ motzkin_1639_5 _substvar_23_) 0.0)
   (< (+ _substvar_23_ motzkin_1639_3) 0.0)
  )
  (and
   (= (+ (* motzkin_1639_2 (- 1.0)) motzkin_1639_4) 0.0)
   (= (+ (* (- 1.0) _substvar_22_) motzkin_1639_2 motzkin_1639_3 (* motzkin_1639_4 (- 1.0))) 0.0)
   (= (+ _substvar_20_ motzkin_1639_5 _substvar_23_) 0.0)
   (<= (+ (* (- 1.0) _substvar_23_) (* motzkin_1639_3 2147483648.0)) 0.0)
  )
 )
)

(assert
 (or
  (and
   (= motzkin_1640_4 0.0)
   (= _substvar_23_ 0.0)
   (< (+ _substvar_23_ _substvar_20_) 0.0)
  )
  (and
   (= motzkin_1640_4 0.0)
   (= motzkin_1640_3 0.0)
   (= motzkin_1640_6 0.0)
   (<= _substvar_20_ 0.0)
  )
 )
)

(assert
 (or
  (and
   (= motzkin_1651_3 0.0)
   (< (+ _substvar_23_ _substvar_23_ _substvar_23_) 0.0)
  )
  (and
   (= _substvar_20_ 0.0)
   (< _substvar_20_ 0.0)
  )
  (and
   (= (+ _substvar_20_ (* motzkin_1651_3 (- 1.0)) _substvar_21_) 0.0)
   (<= _substvar_20_ 0.0)
  )
  (and
   (= motzkin_1651_2 0.0)
   (<= (+ _substvar_23_ _substvar_20_) 0.0)
   (< (+ _substvar_23_ _substvar_20_ _substvar_23_ _substvar_23_) 0.0)
  )
  (<= (+ _substvar_20_ (* motzkin_1651_2 (- 1.0))) 0.0)
  (= (+ motzkin_1651_3 _substvar_23_) 0.0)
  (and
   (= (+ _substvar_20_ (* motzkin_1651_3 (- 1.0)) _substvar_21_) 0.0)
   (= (+ motzkin_1651_3 _substvar_22_) 0.0)
  )
  (and
   (= (+ _substvar_20_ (* motzkin_1651_3 (- 1.0))) 0.0)
   (= (+ motzkin_1651_3 _substvar_20_) 0.0)
   (< (+ _substvar_23_ _substvar_23_ _substvar_20_ _substvar_23_ _substvar_23_) 0.0)
  )
  (and
   (= _substvar_20_ 0.0)
   (= (+ motzkin_1651_3 _substvar_20_ _substvar_20_) 0.0)
  )
  (and
   (= (+ _substvar_20_ (* motzkin_1651_3 (- 1.0)) _substvar_21_ _substvar_20_) 0.0)
   (= (+ motzkin_1651_3 _substvar_22_ _substvar_20_) 0.0)
   (< (+ _substvar_23_ _substvar_23_ _substvar_23_ _substvar_23_ _substvar_23_ _substvar_20_) 0.0)
  )
  (= (+ motzkin_1651_3 _substvar_20_ _substvar_20_ _substvar_20_) 0.0)
  (and
   (= (+ motzkin_1651_3 _substvar_20_ _substvar_20_) 0.0)
   (<= _substvar_20_ 0.0)
  )
  (and
   (= motzkin_1651_2 0.0)
   (= (+ motzkin_1651_3 _substvar_20_) 0.0)
   (<= (+ (* _substvar_20_ 2.0) (* motzkin_1651_2 (- 1.0)) (* motzkin_1651_3 (- 1.0)) _substvar_20_) 0.0)
  )
  (and
   (= (+ motzkin_1651_2 _substvar_20_) 0.0)
   (= _substvar_20_ 0.0)
   (= (+ _substvar_20_ (* motzkin_1651_3 (- 1.0)) _substvar_21_ _substvar_20_) 0.0)
   (= (+ motzkin_1651_3 _substvar_22_ _substvar_20_) 0.0)
   (<= (+ (* _substvar_20_ 3.0) (* motzkin_1651_2 (- 1.0)) (* motzkin_1651_3 (- 1.0))) 0.0)
  )
 )
)

(assert
 (or
  (and
   (= motzkin_1652_2 0.0)
   (< motzkin_1652_0 0.0)
  )
  (= (+ motzkin_1652_3 _substvar_23_) 0.0)
  (and
   (= _substvar_20_ 0.0)
   (< (+ motzkin_1652_0 _substvar_23_) 0.0)
  )
  (and
   (= (+ (* motzkin_1652_3 (- 1.0)) (* 1.0 _substvar_21_)) 0.0)
   (= (+ motzkin_1652_3 _substvar_22_) 0.0)
   (<= (+ motzkin_1652_0 (* (- 1.0) _substvar_20_)) 0.0)
  )
  (and
   (= (+ motzkin_1652_3 _substvar_20_) 0.0)
   (< (+ motzkin_1652_0 _substvar_20_) 0.0)
  )
  (and
   (= (* motzkin_1652_3 (- 1.0)) 0.0)
   (= (+ motzkin_1652_3 (* (- 1.0) _substvar_20_)) 0.0)
  )
  (and
   (= _substvar_21_ 0.0)
   (= (+ motzkin_1652_3 _substvar_22_ _substvar_20_) 0.0)
   (<= (+ motzkin_1652_0 _substvar_23_ _substvar_23_) 0.0)
   (< (+ motzkin_1652_0 _substvar_23_ _substvar_23_) 0.0)
  )
  (and
   (= (+ (* motzkin_1652_0 (- 1.0)) motzkin_1652_2) 0.0)
   (= _substvar_20_ 0.0)
   (= (+ (* motzkin_1652_3 (- 1.0)) _substvar_21_) 0.0)
  )
  (and
   (= _substvar_20_ 0.0)
   (<= (+ motzkin_1652_0 _substvar_20_) 0.0)
  )
  (and
   (= _substvar_23_ 0.0)
   (<= (+ motzkin_1652_0 (* motzkin_1652_3 (- 1.0))) 0.0)
  )
  (and
   (= (+ (* motzkin_1652_3 (- 1.0)) _substvar_20_) 0.0)
   (= (+ motzkin_1652_3 _substvar_20_) 0.0)
  )
  (and
   (= motzkin_1652_0 0.0)
   (= (+ (* motzkin_1652_0 (- 1.0)) motzkin_1652_2 _substvar_20_) 0.0)
   (= (+ (* motzkin_1652_3 (- 1.0)) _substvar_21_ _substvar_20_) 0.0)
   (= motzkin_1652_3 0.0)
   (<= (+ motzkin_1652_0 _substvar_20_ _substvar_23_) 0.0)
   (or
    (< (+ motzkin_1652_0 (* motzkin_1652_3 (- 1.0)) _substvar_23_ _substvar_20_ _substvar_20_) 0.0)
   )
  )
  (and
   (= (+ motzkin_1652_0 (* motzkin_1652_2 (- 1.0)) (* (- 1.0) _substvar_20_)) 0.0)
   (= (+ (* motzkin_1652_3 (- 1.0)) _substvar_21_ _substvar_20_) 0.0)
   (= (+ motzkin_1652_3 _substvar_22_ _substvar_20_) 0.0)
  )
 )
)

(assert
 (or
  (and
   (= _substvar_23_ 0.0)
   (< _substvar_9_ 0.0)
  )
  (and
   (= (+ _substvar_4_ (* _substvar_7_ 2.0)) 0.0)
   (= (+ _substvar_23_ _substvar_21_) 0.0)
   (= (+ (* _substvar_23_ (- 1.0)) (* _substvar_7_ (- 1.0))) 0.0)
   (< (+ (* _substvar_4_ (- 1.0)) _substvar_7_ _substvar_23_) 0.0)
  )
 )
)
(check-sat)
(exit)
