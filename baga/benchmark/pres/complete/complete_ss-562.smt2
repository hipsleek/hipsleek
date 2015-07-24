(set-info :source  loris-7.ddns.comp.nus.edu.sg/~project/hip/) 
;Variables declarations
(declare-fun t_primed () Int)
(declare-fun t_2650 () Int)
(declare-fun n () Int)
(declare-fun t () Int)
(declare-fun nmin () Int)
(declare-fun nmin2_2853 () Int)
(declare-fun nmin1_2851 () Int)
;Relations declarations
;Axioms assertions
;Antecedent
(assert (< t_2650 1))
(assert (= t_primed 1))
(assert (= t_2650 t))
(assert (exists ((min_2884 Int)) (or (and (= min_2884 nmin1_2851) (< nmin1_2851 nmin2_2853)) (and (= min_2884 nmin2_2853) (>= nmin1_2851 nmin2_2853)))))
(assert (= nmin n))
(assert (= nmin1_2851 0))
(assert (= nmin2_2853 0))
(assert (or (and (and (<= 1 nmin) (<= nmin n)) (> t 0)) (or (and (and (< t 1) (= n 0)) (= nmin 0)) (and (and (<= 1 nmin) (< nmin n)) (> t 0)))))
;Negation of Consequence
(assert (not (or (and (and (<= nmin (+ nmin1_2851 1)) (<= nmin1_2851 nmin)) (< nmin1_2851 nmin2_2853)) (and (and (<= nmin (+ nmin2_2853 1)) (<= nmin2_2853 nmin)) (<= nmin2_2853 nmin1_2851)))))
(check-sat)