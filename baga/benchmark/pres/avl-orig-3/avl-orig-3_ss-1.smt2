(set-info :source  loris-7.ddns.comp.nus.edu.sg/~project/hip/) 
;Variables declarations
(declare-fun m () Int)
(declare-fun n () Int)
(declare-fun bal () Int)
(declare-fun self () Int)
(declare-fun n1 () Int)
(declare-fun Anon_16 () Int)
(declare-fun m1 () Int)
(declare-fun p () Int)
(declare-fun n2 () Int)
(declare-fun Anon_17 () Int)
(declare-fun m2 () Int)
(declare-fun q () Int)
;Relations declarations
;Axioms assertions
;Antecedent
(assert (= m (+ (+ m2 1) m1)))
(assert (exists ((max_63 Int)) (and (= n (+ 1 max_63)) (or (and (= max_63 n1) (>= n1 n2)) (and (= max_63 n2) (< n1 n2))))))
(assert (= (+ bal n2) (+ 1 n1)))
(assert (<= n2 (+ 1 n1)))
(assert (<= n1 (+ n2 1)))
(assert (= self 1))
(assert (or (and (and (and (< p 1) (= m1 0)) (= n1 0)) (= Anon_16 1)) (and (and (and (and (and (<= 0 Anon_16) (<= (+ (- 0 n1) 2) Anon_16)) (<= Anon_16 n1)) (<= Anon_16 2)) (<= 1 m1)) (> p 0))))
(assert (or (and (and (and (< q 1) (= m2 0)) (= n2 0)) (= Anon_17 1)) (and (and (and (and (and (<= 0 Anon_17) (<= (+ (- 0 n2) 2) Anon_17)) (<= Anon_17 n2)) (<= Anon_17 2)) (<= 1 m2)) (> q 0))))
;Negation of Consequence
(assert (not false))
(check-sat)