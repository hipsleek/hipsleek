(set-info :source  loris-7.ddns.comp.nus.edu.sg/~project/hip/) 
;Variables declarations
(declare-fun v_null_type_84_2838 () Int)
(declare-fun v_null_type_84_2839 () Int)
(declare-fun flted_79_2840 () Int)
(declare-fun nmin1_2841 () Int)
(declare-fun nmin1_2844 () Int)
(declare-fun flted_25_2860 () Int)
(declare-fun l_2843 () Int)
(declare-fun nmin2_2846 () Int)
(declare-fun flted_25_2859 () Int)
(declare-fun r_2845 () Int)
;Relations declarations
;Axioms assertions
;Antecedent
(assert (< v_null_type_84_2838 1))
(assert (< v_null_type_84_2839 1))
(assert (= l_2843 v_null_type_84_2838))
(assert (= r_2845 v_null_type_84_2839))
(assert (= (+ flted_25_2860 1) flted_79_2840))
(assert (= (+ flted_25_2859 2) flted_79_2840))
(assert (exists ((min_30 Int)) (and (= nmin1_2841 (+ 1 min_30)) (or (and (= min_30 nmin1_2844) (< nmin1_2844 nmin2_2846)) (and (= min_30 nmin2_2846) (>= nmin1_2844 nmin2_2846))))))
(assert (or (and (and (<= 1 nmin1_2844) (<= nmin1_2844 flted_25_2860)) (> l_2843 0)) (or (and (and (< l_2843 1) (= flted_25_2860 0)) (= nmin1_2844 0)) (and (and (<= 1 nmin1_2844) (< nmin1_2844 flted_25_2860)) (> l_2843 0)))))
(assert (or (and (and (<= 1 nmin2_2846) (<= nmin2_2846 flted_25_2859)) (> r_2845 0)) (or (and (and (< r_2845 1) (= flted_25_2859 0)) (= nmin2_2846 0)) (and (and (<= 1 nmin2_2846) (< nmin2_2846 flted_25_2859)) (> r_2845 0)))))
;Negation of Consequence
(assert (not false))
(check-sat)