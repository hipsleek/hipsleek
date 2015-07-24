(set-info :source  loris-7.ddns.comp.nus.edu.sg/~project/hip/) 
;Variables declarations
(declare-fun t2_primed () Int)
(declare-fun t1_primed () Int)
(declare-fun v_bool_465_1388_primed () Int)
(declare-fun h1 () Int)
(declare-fun s1 () Int)
(declare-fun t1 () Int)
(declare-fun h2 () Int)
(declare-fun s2 () Int)
(declare-fun t2 () Int)
;Relations declarations
;Axioms assertions
;Antecedent
(assert (= t1_primed t1))
(assert (= t2_primed t2))
(assert (> t1 0))
(assert (> t1_primed 0))
(assert (not (> v_bool_465_1388_primed 0)))
(assert (or (and (and (< t1 1) (= s1 0)) (= h1 0)) (and (and (<= 1 h1) (<= 1 s1)) (> t1 0))))
(assert (or (and (and (< t2 1) (= s2 0)) (= h2 0)) (and (and (<= 1 h2) (<= 1 s2)) (> t2 0))))
;Negation of Consequence
(assert (not false))
(check-sat)