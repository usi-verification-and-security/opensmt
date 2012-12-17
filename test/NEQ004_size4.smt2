(set-logic QF_UF)
(set-info :source |
CADE ATP System competition. See http://www.cs.miami.edu/~tptp/CASC
 for more information. 

This benchmark was obtained by trying to find a finite model of a first-order 
formula (Albert Oliveras).
|)
(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)
(declare-sort U 0)
(declare-fun p3 (U U) Bool)
(declare-fun c_0 () U)
(assert
 (let ((?v_52 (= c_0 c_0)))
  (let ((?v_16 (not ?v_52))
        (?v_32 (p3 c_0 c_0)))
       (and ?v_52 ?v_16 ?v_32)
  )
 )
)
(check-sat)
(exit)
