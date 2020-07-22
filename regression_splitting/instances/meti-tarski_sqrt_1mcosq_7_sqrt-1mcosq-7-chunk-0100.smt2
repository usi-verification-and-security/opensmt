(set-option :lookahead-split)
(set-option :split-num 64)
(set-option :split-format smt2)
(set-option :split-format-length "brief")
(set-option :output-dir "splits_here")
(set-option :test_cube_and_conquer true)
(set-logic QF_LRA)
(set-info :source |
These benchmarks used in the paper:

  Dejan Jovanovic and Leonardo de Moura.  Solving Non-Linear Arithmetic.
  In IJCAR 2012, published as LNCS volume 7364, pp. 339--354.

The meti-tarski benchmarks are proof obligations extracted from the
Meti-Tarski project, see:

  B. Akbarpour and L. C. Paulson. MetiTarski: An automatic theorem prover
  for real-valued special functions. Journal of Automated Reasoning,
  44(3):175-205, 2010.

Submitted by Dejan Jovanovic for SMT-LIB.


|)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status sat)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun pi () Real)
(assert (let ((?v_0 (* skoX 10))) (and (not (<= 0 skoY)) (and (or (not (<= ?v_0 skoY)) (not (<= skoY ?v_0))) (and (not (<= pi (/ 15707963 5000000))) (and (not (<= (/ 31415927 10000000) pi)) (not (<= skoY skoX))))))))
(check-sat)
(exit)
