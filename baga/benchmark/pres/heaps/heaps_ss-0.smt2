(set-info :source  loris-7.ddns.comp.nus.edu.sg/~project/hip/) 
;Variables declarations
(declare-fun n () Int)
(declare-fun mx () Int)
(declare-fun self () Int)
;Relations declarations
;Axioms assertions
;Antecedent
(assert (exists ((mx2 Int)) (exists ((m2 Int)) (and (or (and (and (exists ((r Int)) (< r 1)) (= m2 0)) (= mx2 0)) (and (and (exists ((r Int)) (> r 0)) (<= 0 mx2)) (<= 1 m2))) (exists ((mx1 Int)) (and (exists ((m1 Int)) (and (and (or (and (and (exists ((l Int)) (< l 1)) (= m1 0)) (= mx1 0)) (and (and (exists ((l Int)) (> l 0)) (<= 0 mx1)) (<= 1 m1))) (exists ((m3_28 Int)) (and (and (= (+ m3_28 m2) m1) (<= 0 m3_28)) (<= m3_28 1)))) (= n (+ (+ m2 1) m1)))) (exists ((d Int)) (and (and (and (<= 0 d) (<= mx1 d)) (<= mx2 d)) (<= d mx)))))))))
(assert (= self 1))
;Negation of Consequence
(assert (not false))
(check-sat)