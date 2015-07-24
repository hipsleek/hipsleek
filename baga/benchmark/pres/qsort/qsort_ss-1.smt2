(set-info :source  loris-7.ddns.comp.nus.edu.sg/~project/hip/) 
;Variables declarations
(declare-fun y_primed () Int)
(declare-fun x_primed () Int)
(declare-fun v_bool_55_1443_primed () Int)
(declare-fun s0 () Int)
(declare-fun b0 () Int)
(declare-fun nn () Int)
(declare-fun s2 () Int)
(declare-fun b2 () Int)
(declare-fun m () Int)
(declare-fun x () Int)
(declare-fun y () Int)
;Relations declarations
;Axioms assertions
;Antecedent
(assert (= x_primed x))
(assert (= y_primed y))
(assert (<= b0 s2))
(assert (> x_primed 0))
(assert (not (> v_bool_55_1443_primed 0)))
(assert (or (and (and (= b0 s0) (= nn 1)) (> x 0)) (and (and (<= s0 b0) (<= 2 nn)) (> x 0))))
(assert (or (and (and (= b2 s2) (= m 1)) (> y 0)) (and (and (<= s2 b2) (<= 2 m)) (> y 0))))
(assert (not (= x y)))
;Negation of Consequence
(assert (not false))
(check-sat)