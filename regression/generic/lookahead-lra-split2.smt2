(set-logic QF_LRA)
(set-info :source |
TLP-GP automated DTP to SMT-LIB encoding for planning
by F.Maris and P.Regnier, IRIT - Universite Paul Sabatier, Toulouse

|)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status unknown)
(declare-fun St_spy_variable () Real)
(declare-fun t_Init_0 () Real)
(declare-fun t_Goal_7 () Real)
(declare-fun t_C_N1_3 () Real)
(declare-fun t_B_N1_2 () Real)
(declare-fun t_A_N1_1 () Real)
(declare-fun t_A_N2_4 () Real)
(declare-fun t_B_N2_5 () Real)
(declare-fun t_C_N2_6 () Real)
(assert (let ((?v_2 (- t_Goal_7 t_C_N1_3)) (?v_1 (- t_Goal_7 t_B_N1_2)) (?v_0 (- t_Goal_7 t_A_N1_1)) (?v_3 (- t_Goal_7 t_A_N2_4)) (?v_4 (- t_Goal_7 t_B_N2_5)) (?v_13 (- t_Goal_7 t_C_N2_6)) (?v_8 (- t_B_N1_2 t_A_N1_1))) (let ((?v_7 (< ?v_8 5)) (?v_6 (- t_C_N1_3 t_B_N1_2))) (let ((?v_5 (< ?v_6 4)) (?v_10 (- t_B_N2_5 t_A_N2_4))) (let ((?v_9 (< ?v_10 5)) (?v_12 (- t_C_N2_6 t_B_N2_5))) (let ((?v_11 (< ?v_12 4)) (?v_17 (- t_A_N2_4 t_C_N1_3)) (?v_14 (- t_A_N2_4 t_A_N1_1))) (let ((?v_23 (< ?v_14 5)) (?v_15 (> ?v_8 1))) (let ((?v_22 (or ?v_23 ?v_15)) (?v_16 (< ?v_0 6)) (?v_18 (< (- t_C_N1_3 t_A_N1_1) 4))) (let ((?v_21 (or (< ?v_17 1) ?v_18)) (?v_19 (> ?v_10 1))) (let ((?v_24 (or (< ?v_10 1) ?v_19)) (?v_20 (< ?v_3 6)) (?v_26 (- t_C_N2_6 t_A_N2_4))) (let ((?v_25 (< ?v_26 4))) (and (= St_spy_variable (+ 1 t_Init_0)) (>= t_Goal_7 t_Init_0) (>= (- t_C_N1_3 t_Init_0) 0) (>= ?v_2 1) (>= (- t_B_N1_2 t_Init_0) 0) (>= ?v_1 4) (>= (- t_A_N1_1 t_Init_0) 0) (>= ?v_0 5) (>= (- t_A_N2_4 t_Init_0) 0) (>= ?v_3 5) (>= (- t_B_N2_5 t_Init_0) 0) (>= ?v_4 4) (>= (- t_C_N2_6 t_Init_0) 0) (>= ?v_13 1) ?v_7 (>= ?v_0 6) ?v_5 (>= ?v_1 5) (>= ?v_2 2) ?v_9 (>= ?v_3 6) ?v_11 (>= ?v_4 5) ?v_5 ?v_5 (>= ?v_6 0) (>= ?v_17 1) ?v_7 ?v_7 (>= ?v_8 0) (>= (- t_A_N2_4 t_B_N1_2) 4) (>= ?v_14 5) ?v_9 (>= ?v_10 0) ?v_11 (>= ?v_12 0) (>= ?v_13 2) ?v_22 (or ?v_16 ?v_15) (or ?v_18 (< ?v_2 2)) (or ?v_15 ?v_16) ?v_21 ?v_24 (or ?v_20 ?v_19) (or ?v_25 (< ?v_13 2)) (or ?v_19 ?v_20) (or ?v_15 (< ?v_8 1)) ?v_21 ?v_22 (or ?v_15 ?v_23) ?v_24 (or ?v_25 (> ?v_26 4))))))))))))))
(check-sat)
(exit)
