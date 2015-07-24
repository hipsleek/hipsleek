(set-info :source  loris-7.ddns.comp.nus.edu.sg/~project/hip/) 
;Variables declarations
(declare-fun n () Int)
(declare-fun nmin () Int)
(declare-fun v_bool_61_1524_primed () Int)
(declare-fun t () Int)
(declare-fun t_primed () Int)
(declare-fun nmin1_1652 () Int)
(declare-fun flted_26_1649 () Int)
(declare-fun l_1651 () Int)
(declare-fun nmin2_1654 () Int)
(declare-fun flted_26_1648 () Int)
(declare-fun r_1653 () Int)
;Relations declarations
;Axioms assertions
;Antecedent
(assert (= (+ flted_26_1649 1) n))
(assert (= (+ flted_26_1648 1) n))
(assert (exists ((min_32 Int)) (and (= nmin (+ 1 min_32)) (or (and (= min_32 nmin1_1652) (< nmin1_1652 nmin2_1654)) (and (= min_32 nmin2_1654) (>= nmin1_1652 nmin2_1654))))))
(assert (> v_bool_61_1524_primed 0))
(assert (> t_primed 0))
(assert (= t_primed t))
(assert (= t_primed 1))
(assert (or (and (and (<= 1 nmin1_1652) (<= nmin1_1652 flted_26_1649)) (> l_1651 0)) (or (and (and (< l_1651 1) (= flted_26_1649 0)) (= nmin1_1652 0)) (and (and (<= 1 nmin1_1652) (< nmin1_1652 flted_26_1649)) (> l_1651 0)))))
(assert (or (and (and (<= 1 nmin2_1654) (<= nmin2_1654 flted_26_1648)) (> r_1653 0)) (or (and (and (< r_1653 1) (= flted_26_1648 0)) (= nmin2_1654 0)) (and (and (<= 1 nmin2_1654) (< nmin2_1654 flted_26_1648)) (> r_1653 0)))))
;Negation of Consequence
(assert (not false))
(check-sat)