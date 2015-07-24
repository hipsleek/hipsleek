(set-info :source  loris-7.ddns.comp.nus.edu.sg/~project/hip/) 
;Variables declarations
(declare-fun n () Int)
(declare-fun nmin () Int)
(declare-fun v_bool_70_1477_primed () Int)
(declare-fun t () Int)
(declare-fun t_primed () Int)
(declare-fun nmin1_1883 () Int)
(declare-fun flted_26_1880 () Int)
(declare-fun l_1882 () Int)
(declare-fun nmin2_1885 () Int)
(declare-fun flted_26_1879 () Int)
(declare-fun r_1884 () Int)
;Relations declarations
;Axioms assertions
;Antecedent
(assert (= (+ flted_26_1880 1) n))
(assert (= (+ flted_26_1879 1) n))
(assert (exists ((min_32 Int)) (and (= nmin (+ 1 min_32)) (or (and (= min_32 nmin1_1883) (< nmin1_1883 nmin2_1885)) (and (= min_32 nmin2_1885) (>= nmin1_1883 nmin2_1885))))))
(assert (> v_bool_70_1477_primed 0))
(assert (> t_primed 0))
(assert (= t_primed t))
(assert (= t_primed 1))
(assert (or (and (and (<= 1 nmin1_1883) (<= nmin1_1883 flted_26_1880)) (> l_1882 0)) (or (and (and (< l_1882 1) (= flted_26_1880 0)) (= nmin1_1883 0)) (and (and (<= 1 nmin1_1883) (< nmin1_1883 flted_26_1880)) (> l_1882 0)))))
(assert (or (and (and (<= 1 nmin2_1885) (<= nmin2_1885 flted_26_1879)) (> r_1884 0)) (or (and (and (< r_1884 1) (= flted_26_1879 0)) (= nmin2_1885 0)) (and (and (<= 1 nmin2_1885) (< nmin2_1885 flted_26_1879)) (> r_1884 0)))))
;Negation of Consequence
(assert (not false))
(check-sat)