(set-info :source  loris-7.ddns.comp.nus.edu.sg/~project/hip/) 
;Variables declarations
(declare-fun n () Int)
(declare-fun nl_13884 () Int)
(declare-fun nr_13887 () Int)
(declare-fun x_14363 () Int)
(declare-fun x () Int)
(declare-fun r_13886 () Int)
(declare-fun flted_299_14817 () Int)
(declare-fun bh2_14819 () Int)
(declare-fun flted_299_14818 () Int)
(declare-fun x_primed () Int)
;Relations declarations
;Axioms assertions
;Antecedent
(assert (= x_14363 3))
(assert (= nl_13884 0))
(assert (< r_13886 1))
(assert (= nr_13887 0))
(assert (= n (+ (+ nr_13887 1) nl_13884)))
(assert (or (= nr_13887 0) (< r_13886 1)))
(assert (= x_14363 x))
(assert (> x 0))
(assert (= x_primed r_13886))
;Negation of Consequence
(assert (not (or (and (and (and (= flted_299_14817 0) (<= 2 bh2_14819)) (<= 1 flted_299_14818)) (> x_primed 0)) (or (and (and (and (< x_primed 1) (= flted_299_14818 0)) (= bh2_14819 1)) (= flted_299_14817 0)) (and (and (and (= flted_299_14817 1) (<= 1 bh2_14819)) (<= 1 flted_299_14818)) (> x_primed 0))))))
(check-sat)