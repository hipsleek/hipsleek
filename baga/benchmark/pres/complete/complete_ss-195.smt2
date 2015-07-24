(set-info :source  loris-7.ddns.comp.nus.edu.sg/~project/hip/) 
;Variables declarations
(declare-fun r_2119 () Int)
(declare-fun flted_25_2114 () Int)
(declare-fun n () Int)
(declare-fun nmin () Int)
(declare-fun nmin2_2120 () Int)
(declare-fun v_node2_88_1332_primed () Int)
(declare-fun flted_25_2115 () Int)
(declare-fun nmin1_2118 () Int)
(declare-fun l_2117 () Int)
;Relations declarations
;Axioms assertions
;Antecedent
(assert (or (and (and (<= 1 nmin2_2120) (<= nmin2_2120 flted_25_2114)) (> r_2119 0)) (or (and (and (< r_2119 1) (= flted_25_2114 0)) (= nmin2_2120 0)) (and (and (<= 1 nmin2_2120) (< nmin2_2120 flted_25_2114)) (> r_2119 0)))))
(assert (< nmin n))
(assert (= (+ flted_25_2114 2) n))
(assert (= (+ flted_25_2115 1) n))
(assert (exists ((min_2136 Int)) (and (= nmin (+ 1 min_2136)) (or (and (= min_2136 nmin1_2118) (< nmin1_2118 nmin2_2120)) (and (= min_2136 nmin2_2120) (>= nmin1_2118 nmin2_2120))))))
(assert (= v_node2_88_1332_primed l_2117))
(assert (or (and (and (<= 1 nmin1_2118) (<= nmin1_2118 flted_25_2115)) (> l_2117 0)) (or (and (and (< l_2117 1) (= flted_25_2115 0)) (= nmin1_2118 0)) (and (and (<= 1 nmin1_2118) (< nmin1_2118 flted_25_2115)) (> l_2117 0)))))
;Negation of Consequence
(assert (not (or (= flted_25_2115 0) (or (= nmin1_2118 0) (< l_2117 1)))))
(check-sat)