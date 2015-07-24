(set-info :source  loris-7.ddns.comp.nus.edu.sg/~project/hip/) 
;Variables declarations
(declare-fun n () Int)
(declare-fun nr_14911 () Int)
(declare-fun nl_14908 () Int)
(declare-fun x_15395 () Int)
(declare-fun x () Int)
(declare-fun l_14907 () Int)
(declare-fun cl_16522 () Int)
(declare-fun bh_16523 () Int)
(declare-fun n_16521 () Int)
(declare-fun x_primed () Int)
;Relations declarations
;Axioms assertions
;Antecedent
(assert (= x_15395 3))
(assert (= nr_14911 0))
(assert (< l_14907 1))
(assert (= nl_14908 0))
(assert (= n (+ (+ nr_14911 1) nl_14908)))
(assert (> x_15395 0))
(assert (or (= nl_14908 0) (< l_14907 1)))
(assert (= x_15395 x))
(assert (= x_primed l_14907))
;Negation of Consequence
(assert (not (or (and (and (and (= cl_16522 0) (<= 2 bh_16523)) (<= 1 n_16521)) (> x_primed 0)) (or (and (and (and (< x_primed 1) (= n_16521 0)) (= bh_16523 1)) (= cl_16522 0)) (and (and (and (= cl_16522 1) (<= 1 bh_16523)) (<= 1 n_16521)) (> x_primed 0))))))
(check-sat)