(set-info :source  loris-7.ddns.comp.nus.edu.sg/~project/hip/) 
;Variables declarations
(declare-fun r_1669 () Int)
(declare-fun flted_26_1664 () Int)
(declare-fun n () Int)
(declare-fun nmin () Int)
(declare-fun nmin2_1670 () Int)
(declare-fun v_node2_62_1510_primed () Int)
(declare-fun flted_26_1665 () Int)
(declare-fun nmin1_1668 () Int)
(declare-fun l_1667 () Int)
;Relations declarations
;Axioms assertions
;Antecedent
(assert (or (and (and (<= 1 nmin2_1670) (<= nmin2_1670 flted_26_1664)) (> r_1669 0)) (or (and (and (< r_1669 1) (= flted_26_1664 0)) (= nmin2_1670 0)) (and (and (<= 1 nmin2_1670) (< nmin2_1670 flted_26_1664)) (> r_1669 0)))))
(assert (= (+ flted_26_1664 1) n))
(assert (= (+ flted_26_1665 1) n))
(assert (exists ((min_1681 Int)) (and (= nmin (+ 1 min_1681)) (or (and (= min_1681 nmin1_1668) (< nmin1_1668 nmin2_1670)) (and (= min_1681 nmin2_1670) (>= nmin1_1668 nmin2_1670))))))
(assert (= v_node2_62_1510_primed l_1667))
(assert (or (and (and (<= 1 nmin1_1668) (<= nmin1_1668 flted_26_1665)) (> l_1667 0)) (or (and (and (< l_1667 1) (= flted_26_1665 0)) (= nmin1_1668 0)) (and (and (<= 1 nmin1_1668) (< nmin1_1668 flted_26_1665)) (> l_1667 0)))))
;Negation of Consequence
(assert (not (or (= flted_26_1665 0) (or (= nmin1_1668 0) (< l_1667 1)))))
(check-sat)