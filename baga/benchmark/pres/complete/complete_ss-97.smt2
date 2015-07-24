(set-info :source  loris-7.ddns.comp.nus.edu.sg/~project/hip/) 
;Variables declarations
(declare-fun n () Int)
(declare-fun nmin () Int)
(declare-fun v_bool_70_1477_primed () Int)
(declare-fun t () Int)
(declare-fun t_primed () Int)
(declare-fun nmin1_1876 () Int)
(declare-fun flted_25_1873 () Int)
(declare-fun l_1875 () Int)
(declare-fun nmin2_1878 () Int)
(declare-fun flted_25_1872 () Int)
(declare-fun r_1877 () Int)
;Relations declarations
;Axioms assertions
;Antecedent
(assert (= (+ flted_25_1873 1) n))
(assert (= (+ flted_25_1872 2) n))
(assert (exists ((min_30 Int)) (and (= nmin (+ 1 min_30)) (or (and (= min_30 nmin1_1876) (< nmin1_1876 nmin2_1878)) (and (= min_30 nmin2_1878) (>= nmin1_1876 nmin2_1878))))))
(assert (> v_bool_70_1477_primed 0))
(assert (> t_primed 0))
(assert (= t_primed t))
(assert (= t_primed 1))
(assert (or (and (and (<= 1 nmin1_1876) (<= nmin1_1876 flted_25_1873)) (> l_1875 0)) (or (and (and (< l_1875 1) (= flted_25_1873 0)) (= nmin1_1876 0)) (and (and (<= 1 nmin1_1876) (< nmin1_1876 flted_25_1873)) (> l_1875 0)))))
(assert (or (and (and (<= 1 nmin2_1878) (<= nmin2_1878 flted_25_1872)) (> r_1877 0)) (or (and (and (< r_1877 1) (= flted_25_1872 0)) (= nmin2_1878 0)) (and (and (<= 1 nmin2_1878) (< nmin2_1878 flted_25_1872)) (> r_1877 0)))))
;Negation of Consequence
(assert (not false))
(check-sat)