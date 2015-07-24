(set-info :source  loris-7.ddns.comp.nus.edu.sg/~project/hip/) 
;Variables declarations
(declare-fun flted_12_13880 () Int)
(declare-fun l_13883 () Int)
(declare-fun bhl_13885 () Int)
(declare-fun bh () Int)
(declare-fun n () Int)
(declare-fun nl_13884 () Int)
(declare-fun v_node_314_3269_primed () Int)
(declare-fun flted_12_13879 () Int)
(declare-fun bhr_13888 () Int)
(declare-fun nr_13887 () Int)
(declare-fun r_13886 () Int)
;Relations declarations
;Axioms assertions
;Antecedent
(assert (< l_13883 1))
(assert (= flted_12_13880 0))
(assert (or (and (and (and (= flted_12_13880 0) (<= 2 bhl_13885)) (<= 1 nl_13884)) (> l_13883 0)) (or (and (and (and (< l_13883 1) (= nl_13884 0)) (= bhl_13885 1)) (= flted_12_13880 0)) (and (and (and (= flted_12_13880 1) (<= 1 bhl_13885)) (<= 1 nl_13884)) (> l_13883 0)))))
(assert (= flted_12_13879 0))
(assert (= bhl_13885 bh))
(assert (= bhr_13888 bh))
(assert (= n (+ (+ nr_13887 1) nl_13884)))
(assert (= v_node_314_3269_primed r_13886))
(assert (or (and (and (and (= flted_12_13879 0) (<= 2 bhr_13888)) (<= 1 nr_13887)) (> r_13886 0)) (or (and (and (and (< r_13886 1) (= nr_13887 0)) (= bhr_13888 1)) (= flted_12_13879 0)) (and (and (and (= flted_12_13879 1) (<= 1 bhr_13888)) (<= 1 nr_13887)) (> r_13886 0)))))
;Negation of Consequence
(assert (not (or (= nr_13887 0) (< r_13886 1))))
(check-sat)