; This is an example

(set-info :bar "foo \"bar quux")
   (set-info :quux "bar quux frobboz")

(set-info :frobboz (foo :bar (quux bar)))

(set-logic AB_CD)
(declare-fun f () a)
(set-info :quux "bar quux 
frob\\boz\"")

(declare-fun _foo () b)

(declare-fun - () ..foo)

(declare-fun |bar "this is 


internal" quux| () ||)

(declare-fun q () (_ foo 1 2 3 4))

(declare-fun q1 () ((_ foo 1 2 3 4) (_ bar 4 3 2 1) (_ quux 1 2 3 4)))
