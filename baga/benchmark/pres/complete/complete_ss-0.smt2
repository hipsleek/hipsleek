(set-info :source  loris-7.ddns.comp.nus.edu.sg/~project/hip/) 
;Variables declarations
(declare-fun n () Int)
(declare-fun nmin () Int)
(declare-fun self () Int)
;Relations declarations
;Axioms assertions
;Antecedent
(assert (exists ((nmin2 Int)) (and (exists ((r Int)) (exists ((flted_25_34 Int)) (and (= (+ flted_25_34 2) n) (or (and (and (<= 1 nmin2) (<= nmin2 flted_25_34)) (> r 0)) (or (and (and (< r 1) (= flted_25_34 0)) (= nmin2 0)) (and (and (<= 1 nmin2) (< nmin2 flted_25_34)) (> r 0))))))) (exists ((nmin1 Int)) (and (exists ((l Int)) (exists ((flted_25_35 Int)) (and (= (+ flted_25_35 1) n) (or (and (and (<= 1 nmin1) (<= nmin1 flted_25_35)) (> l 0)) (or (and (and (< l 1) (= flted_25_35 0)) (= nmin1 0)) (and (and (<= 1 nmin1) (< nmin1 flted_25_35)) (> l 0))))))) (exists ((min_30 Int)) (and (= nmin (+ 1 min_30)) (or (and (= min_30 nmin1) (< nmin1 nmin2)) (and (= min_30 nmin2) (>= nmin1 nmin2))))))))))
(assert (= self 1))
;Negation of Consequence
(assert (not false))
(check-sat)