(set-info :source  loris-7.ddns.comp.nus.edu.sg/~project/hip/) 
;Variables declarations
(declare-fun m () Int)
(declare-fun n () Int)
(declare-fun self () Int)
;Relations declarations
;Axioms assertions
;Antecedent
(assert (exists ((n2 Int)) (exists ((m2 Int)) (and (or (and (= m2 0) (= n2 0)) (and (and (exists ((q Int)) (> q 0)) (<= 1 n2)) (<= 1 m2))) (exists ((n1 Int)) (and (exists ((m1 Int)) (and (or (and (= m1 0) (= n1 0)) (and (and (exists ((p Int)) (> p 0)) (<= 1 n1)) (<= 1 m1))) (= m (+ (+ m2 1) m1)))) (exists ((max_42 Int)) (and (= n (+ max_42 1)) (or (and (= max_42 n1) (>= n1 n2)) (and (= max_42 n2) (< n1 n2)))))))))))
(assert (= self 1))
;Negation of Consequence
(assert (not false))
(check-sat)