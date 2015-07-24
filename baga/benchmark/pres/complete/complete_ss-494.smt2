(set-info :source  loris-7.ddns.comp.nus.edu.sg/~project/hip/) 
;Variables declarations
(declare-fun r_2689 () Int)
(declare-fun flted_26_2684 () Int)
(declare-fun n () Int)
(declare-fun nmin () Int)
(declare-fun nmin2_2690 () Int)
(declare-fun v_node2_88_1332_primed () Int)
(declare-fun flted_26_2685 () Int)
(declare-fun nmin1_2688 () Int)
(declare-fun l_2687 () Int)
;Relations declarations
;Axioms assertions
;Antecedent
(assert (or (and (and (<= 1 nmin2_2690) (<= nmin2_2690 flted_26_2684)) (> r_2689 0)) (or (and (and (< r_2689 1) (= flted_26_2684 0)) (= nmin2_2690 0)) (and (and (<= 1 nmin2_2690) (< nmin2_2690 flted_26_2684)) (> r_2689 0)))))
(assert (= nmin n))
(assert (= (+ flted_26_2684 1) n))
(assert (= (+ flted_26_2685 1) n))
(assert (exists ((min_2697 Int)) (and (= nmin (+ 1 min_2697)) (or (and (= min_2697 nmin1_2688) (< nmin1_2688 nmin2_2690)) (and (= min_2697 nmin2_2690) (>= nmin1_2688 nmin2_2690))))))
(assert (= v_node2_88_1332_primed l_2687))
(assert (or (and (and (<= 1 nmin1_2688) (<= nmin1_2688 flted_26_2685)) (> l_2687 0)) (or (and (and (< l_2687 1) (= flted_26_2685 0)) (= nmin1_2688 0)) (and (and (<= 1 nmin1_2688) (< nmin1_2688 flted_26_2685)) (> l_2687 0)))))
;Negation of Consequence
(assert (not (or (= flted_26_2685 0) (or (= nmin1_2688 0) (< l_2687 1)))))
(check-sat)