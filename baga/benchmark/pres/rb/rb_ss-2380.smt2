(set-info :source  loris-7.ddns.comp.nus.edu.sg/~project/hip/) 
;Variables declarations
(declare-fun a_primed () Int)
(declare-fun a () Int)
(declare-fun x_primed () Int)
(declare-fun v_bool_395_3172_primed () Int)
(declare-fun cl () Int)
(declare-fun bh () Int)
(declare-fun n () Int)
(declare-fun x () Int)
;Relations declarations
;Axioms assertions
;Antecedent
(assert (= x_primed x))
(assert (= a_primed a))
(assert (<= 0 cl))
(assert (<= cl 1))
(assert (not (> v_bool_395_3172_primed 0)))
(assert (< x_primed 1))
(assert (> v_bool_395_3172_primed 0))
(assert (or (and (and (and (= cl 0) (<= 2 bh)) (<= 1 n)) (> x 0)) (or (and (and (and (< x 1) (= n 0)) (= bh 1)) (= cl 0)) (and (and (and (= cl 1) (<= 1 bh)) (<= 1 n)) (> x 0)))))
;Negation of Consequence
(assert (not false))
(check-sat)