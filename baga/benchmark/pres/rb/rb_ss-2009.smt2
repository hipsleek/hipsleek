(set-info :source  loris-7.ddns.comp.nus.edu.sg/~project/hip/) 
;Variables declarations
(declare-fun bh () Int)
(declare-fun Anon_13894 () Int)
(declare-fun l_13892 () Int)
(declare-fun bhl_13895 () Int)
(declare-fun n () Int)
(declare-fun nl_13893 () Int)
(declare-fun v_node_314_3269_primed () Int)
(declare-fun Anon_13898 () Int)
(declare-fun bhr_13899 () Int)
(declare-fun nr_13897 () Int)
(declare-fun r_13896 () Int)
;Relations declarations
;Axioms assertions
;Antecedent
(assert (< l_13892 1))
(assert (= bh (+ bhl_13895 1)))
(assert (or (and (and (and (= Anon_13894 0) (<= 2 bhl_13895)) (<= 1 nl_13893)) (> l_13892 0)) (or (and (and (and (< l_13892 1) (= nl_13893 0)) (= bhl_13895 1)) (= Anon_13894 0)) (and (and (and (= Anon_13894 1) (<= 1 bhl_13895)) (<= 1 nl_13893)) (> l_13892 0)))))
(assert (= bhl_13895 bhr_13899))
(assert (= n (+ (+ nr_13897 1) nl_13893)))
(assert (= v_node_314_3269_primed r_13896))
(assert (or (and (and (and (= Anon_13898 0) (<= 2 bhr_13899)) (<= 1 nr_13897)) (> r_13896 0)) (or (and (and (and (< r_13896 1) (= nr_13897 0)) (= bhr_13899 1)) (= Anon_13898 0)) (and (and (and (= Anon_13898 1) (<= 1 bhr_13899)) (<= 1 nr_13897)) (> r_13896 0)))))
;Negation of Consequence
(assert (not (or (= nr_13897 0) (< r_13896 1))))
(check-sat)