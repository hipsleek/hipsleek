(set-info :source  loris-7.ddns.comp.nus.edu.sg/~project/hip/) 
;Variables declarations
(declare-fun r () Int)
(declare-fun l () Int)
(declare-fun n () Int)
(declare-fun m2 () Int)
(declare-fun m1 () Int)
(declare-fun mx1 () Int)
(declare-fun mx2 () Int)
(declare-fun d () Int)
(declare-fun mx () Int)
(declare-fun self () Int)
;Relations declarations
;Axioms assertions
;Antecedent
(assert (exists ((m3_28 Int)) (and (and (= (+ m3_28 m2) m1) (<= 0 m3_28)) (<= m3_28 1))))
(assert (or (and (and (< r 1) (= m2 0)) (= mx2 0)) (and (and (<= 0 mx2) (<= 1 m2)) (> r 0))))
(assert (or (and (and (< l 1) (= m1 0)) (= mx1 0)) (and (and (<= 0 mx1) (<= 1 m1)) (> l 0))))
(assert (= n (+ (+ m2 1) m1)))
(assert (<= 0 d))
(assert (<= mx1 d))
(assert (<= mx2 d))
(assert (<= d mx))
(assert (= self 1))
;Negation of Consequence
(assert (not false))
(check-sat)