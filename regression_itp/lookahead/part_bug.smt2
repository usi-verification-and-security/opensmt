(set-option :produce-interpolants 1)
(set-option :certify-interpolants 1)
(set-option :pure-lookahead true)
(set-logic QF_LRA)
(declare-fun |hifrog::fun_start!0#3| () Bool)
(declare-fun |hifrog::fun_end!0#3| () Bool)
(declare-fun |getchar::1::x!0#2| () Real)
(declare-fun |symex::nondet#1| () Real)
(declare-fun |getchar::$tmp::return_value!0#1| () Real)
(declare-fun |getchar::#return_value!0#1| () Real)
(declare-fun |hifrog::fun_start!0#2| () Bool)
(declare-fun |hifrog::fun_end!0#2| () Bool)
(declare-fun |hifrog::?err!0#1| () Bool)
(declare-fun |main::1::x!0#2| () Real)
(declare-fun |goto_symex::guard#1| () Bool)
(declare-fun |goto_symex::guard#2| () Bool)
(declare-fun |goto_symex::guard#3| () Bool)
(declare-fun |goto_symex::guard#4| () Bool)
(declare-fun |main::1::t!0#11| () Real)
(declare-fun .oite0 () Real)
(declare-fun |main::1::t!0#12| () Real)
(declare-fun .oite1 () Real)
(declare-fun |main::1::t!0#13| () Real)
(declare-fun .oite2 () Real)
(declare-fun |main::1::t!0#14| () Real)
(declare-fun .oite3 () Real)
(declare-fun |hifrog::fun_start!0#1| () Bool)
(declare-fun |hifrog::fun_end!0#1| () Bool)
(declare-fun |nil| () Bool)
(declare-fun |return'!0#1| () Real)
(declare-fun |symex::io::0| () Real)
; XXX oite symbol: (0 out of 3) .oite0
(assert (! (and (or (not |goto_symex::guard#4|) (= (- 2) .oite0)) (or |goto_symex::guard#4| (= 10 .oite0))) :named i1)
)
; XXX oite symbol: (1 out of 3) .oite1
(assert (!(and (or (not |goto_symex::guard#3|) (= 5 .oite1)) (or |goto_symex::guard#3| (= |main::1::t!0#11| .oite1))) :named i2)
)
; XXX oite symbol: (2 out of 3) .oite2
(assert (!(and (or (not |goto_symex::guard#2|) (= 3 .oite2)) (or |goto_symex::guard#2| (= |main::1::t!0#12| .oite2))) :named i3)
)
; XXX oite symbol: (3 out of 3) .oite3
(assert (!(and (or (not |goto_symex::guard#1|) (= 1 .oite3)) (or |goto_symex::guard#1| (= |main::1::t!0#13| .oite3))) :named i4)
)
; XXX Partition: 3
(assert (!
(and (and (<= (- 2147483648) |symex::nondet#1|) (<= (- 2147483647) (* |symex::nondet#1| (- 1)))) (= |getchar::1::x!0#2| |symex::nondet#1|) (= |getchar::1::x!0#2| |getchar::$tmp::return_value!0#1|) (= |getchar::$tmp::return_value!0#1| |getchar::#return_value!0#1|) (or (not |hifrog::fun_end!0#3|) (and (<= (- 1) |getchar::1::x!0#2|) (and |hifrog::fun_start!0#3| (not (<= 256 |getchar::1::x!0#2|))))))
 :named part3))
; XXX Partition: 2
(assert (!
(and (= |getchar::#return_value!0#1| |main::1::x!0#2|) (= |goto_symex::guard#1| (= 1 |main::1::x!0#2|)) (= |goto_symex::guard#2| (= |main::1::x!0#2| 2)) (= |goto_symex::guard#3| (= |main::1::x!0#2| 3)) (= |goto_symex::guard#4| (= |main::1::x!0#2| (- 2))) (= |main::1::t!0#11| .oite0) (= |main::1::t!0#12| .oite1) (= |main::1::t!0#13| .oite2) (= |main::1::t!0#14| .oite3) (= |hifrog::fun_start!0#2| |hifrog::fun_start!0#3|) (= (not (or (not (and |hifrog::fun_end!0#3| |hifrog::fun_start!0#2|)) (not (= (- 2) |main::1::t!0#14|)))) |hifrog::?err!0#1|) (or (not |hifrog::fun_end!0#2|) (and |hifrog::fun_end!0#3| |hifrog::fun_start!0#2|)))
 :named part2))
; XXX Partition: 1
(assert (!
(or |hifrog::fun_start!0#1| (not |hifrog::fun_end!0#1|))
 :named part1))
; XXX Partition: 0
(assert (!
(and |hifrog::?err!0#1| |hifrog::fun_start!0#1| (= |hifrog::fun_end!0#1| |hifrog::fun_start!0#2|) (= |return'!0#1| |symex::io::0|))
 :named part0))
(check-sat)
(get-interpolants (and i1 i2 i3 i4 part2 part1 part0) part3)
