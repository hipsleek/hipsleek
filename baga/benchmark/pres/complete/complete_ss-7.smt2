(set-info :source  loris-7.ddns.comp.nus.edu.sg/~project/hip/) 
;Variables declarations
(declare-fun r_1661 () Int)
(declare-fun flted_25_1656 () Int)
(declare-fun n () Int)
(declare-fun nmin () Int)
(declare-fun nmin2_1662 () Int)
(declare-fun v_node2_62_1510_primed () Int)
(declare-fun flted_25_1657 () Int)
(declare-fun nmin1_1660 () Int)
(declare-fun l_1659 () Int)
;Relations declarations
;Axioms assertions
;Antecedent
(assert (or (and (and (<= 1 nmin2_1662) (<= nmin2_1662 flted_25_1656)) (> r_1661 0)) (or (and (and (< r_1661 1) (= flted_25_1656 0)) (= nmin2_1662 0)) (and (and (<= 1 nmin2_1662) (< nmin2_1662 flted_25_1656)) (> r_1661 0)))))
(assert (= (+ flted_25_1656 2) n))
(assert (= (+ flted_25_1657 1) n))
(assert (exists ((min_1678 Int)) (and (= nmin (+ 1 min_1678)) (or (and (= min_1678 nmin1_1660) (< nmin1_1660 nmin2_1662)) (and (= min_1678 nmin2_1662) (>= nmin1_1660 nmin2_1662))))))
(assert (= v_node2_62_1510_primed l_1659))
(assert (or (and (and (<= 1 nmin1_1660) (<= nmin1_1660 flted_25_1657)) (> l_1659 0)) (or (and (and (< l_1659 1) (= flted_25_1657 0)) (= nmin1_1660 0)) (and (and (<= 1 nmin1_1660) (< nmin1_1660 flted_25_1657)) (> l_1659 0)))))
;Negation of Consequence
(assert (not (or (= flted_25_1657 0) (or (= nmin1_1660 0) (< l_1659 1)))))
(check-sat)