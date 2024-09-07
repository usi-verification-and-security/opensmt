; This example is completed with comments.
(set-logic QF_BV)
(set-info :source |
	Constructed by Trevor Hansen to test bvnor nesting.
|)
(set-info :smt-lib-version 2.0)
(set-info :category "check")
(set-info :status unsat)
(declare-fun v0 () (_ BitVec 1))
(assert (not (= v0 v0)))
(check-sat)
