(set-info :source  loris-7.ddns.comp.nus.edu.sg/~project/hip/) 
;Variables declarations
(declare-fun n () Int)
(declare-fun nmin () Int)
(declare-fun v_bool_61_1524_primed () Int)
(declare-fun t () Int)
(declare-fun t_primed () Int)
(declare-fun nmin1_1645 () Int)
(declare-fun flted_25_1642 () Int)
(declare-fun l_1644 () Int)
(declare-fun nmin2_1647 () Int)
(declare-fun flted_25_1641 () Int)
(declare-fun r_1646 () Int)
;Relations declarations
;Axioms assertions
;Antecedent
(assert (= (+ flted_25_1642 1) n))
(assert (= (+ flted_25_1641 2) n))
(assert (exists ((min_30 Int)) (and (= nmin (+ 1 min_30)) (or (and (= min_30 nmin1_1645) (< nmin1_1645 nmin2_1647)) (and (= min_30 nmin2_1647) (>= nmin1_1645 nmin2_1647))))))
(assert (> v_bool_61_1524_primed 0))
(assert (> t_primed 0))
(assert (= t_primed t))
(assert (= t_primed 1))
(assert (or (and (and (<= 1 nmin1_1645) (<= nmin1_1645 flted_25_1642)) (> l_1644 0)) (or (and (and (< l_1644 1) (= flted_25_1642 0)) (= nmin1_1645 0)) (and (and (<= 1 nmin1_1645) (< nmin1_1645 flted_25_1642)) (> l_1644 0)))))
(assert (or (and (and (<= 1 nmin2_1647) (<= nmin2_1647 flted_25_1641)) (> r_1646 0)) (or (and (and (< r_1646 1) (= flted_25_1641 0)) (= nmin2_1647 0)) (and (and (<= 1 nmin2_1647) (< nmin2_1647 flted_25_1641)) (> r_1646 0)))))
;Negation of Consequence
(assert (not false))
(check-sat)