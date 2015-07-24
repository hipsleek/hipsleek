(set-info :source  loris-7.ddns.comp.nus.edu.sg/~project/hip/) 
;Variables declarations
(declare-fun m () Int)
(declare-fun n () Int)
(declare-fun bal () Int)
(declare-fun self () Int)
;Relations declarations
;Axioms assertions
;Antecedent
(assert (exists ((Anon_17 Int)) (exists ((n2 Int)) (exists ((m2 Int)) (and (or (and (and (= m2 0) (= n2 0)) (= Anon_17 1)) (and (and (and (and (and (exists ((q Int)) (> q 0)) (<= 0 Anon_17)) (<= (+ (- 0 n2) 2) Anon_17)) (<= Anon_17 n2)) (<= Anon_17 2)) (<= 1 m2))) (exists ((Anon_16 Int)) (exists ((n1 Int)) (and (and (and (and (exists ((m1 Int)) (and (or (and (and (= m1 0) (= n1 0)) (= Anon_16 1)) (and (and (and (and (and (exists ((p Int)) (> p 0)) (<= 0 Anon_16)) (<= (+ (- 0 n1) 2) Anon_16)) (<= Anon_16 n1)) (<= Anon_16 2)) (<= 1 m1))) (= m (+ (+ m2 1) m1)))) (exists ((max_79 Int)) (and (= n (+ max_79 1)) (or (and (= max_79 n1) (>= n1 n2)) (and (= max_79 n2) (< n1 n2)))))) (<= (+ 0 n2) (+ n1 1))) (<= n1 (+ 1 n2))) (= (+ bal n2) (+ 1 n1))))))))))
(assert (= self 1))
;Negation of Consequence
(assert (not false))
(check-sat)