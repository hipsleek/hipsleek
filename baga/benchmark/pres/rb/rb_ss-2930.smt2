(set-info :source  loris-7.ddns.comp.nus.edu.sg/~project/hip/) 
;Variables declarations
(declare-fun x () Int)
(declare-fun n () Int)
(declare-fun bh () Int)
(declare-fun h_16569 () Int)
(declare-fun flted_381_16566 () Int)
(declare-fun bh2_16568 () Int)
(declare-fun flted_381_16567 () Int)
(declare-fun x_primed () Int)
;Relations declarations
;Axioms assertions
;Antecedent
(assert (or (= n 0) (< x 1)))
(assert (= x_primed x))
(assert (< x_primed 1))
(assert (= bh 1))
(assert (= n 0))
(assert (< x 1))
(assert (= (+ flted_381_16567 1) n))
(assert (= flted_381_16566 0))
(assert (<= bh (+ bh2_16568 1)))
(assert (<= bh2_16568 h_16569))
(assert (or (and (and (and (= flted_381_16566 0) (<= 2 bh2_16568)) (<= 1 flted_381_16567)) (> x_primed 0)) (or (and (and (and (< x_primed 1) (= flted_381_16567 0)) (= bh2_16568 1)) (= flted_381_16566 0)) (and (and (and (= flted_381_16566 1) (<= 1 bh2_16568)) (<= 1 flted_381_16567)) (> x_primed 0)))))
;Negation of Consequence
(assert (not false))
(check-sat)